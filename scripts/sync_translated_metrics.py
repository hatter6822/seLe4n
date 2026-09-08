#!/usr/bin/env python3
# seLe4n  - A Lean Microkernel
# Copyright (C) 2026  Adam Hall
# This program comes with ABSOLUTELY NO WARRANTY.
# This is free software, and you are welcome to redistribute it
# under certain conditions. See: https://github.com/hatter6822/seLe4n/blob/main/LICENSE
"""Push `docs/codebase_map.json` metrics into the translated READMEs and the
GitBook chapters that quote them.

`sync_readme_from_codebase_map.sh` drives `README.md` and
`docs/spec/SELE4N_SPEC.md`.  Everything else that quotes the same five numbers
was hand-copied, so the eleven `docs/i18n/*/README.md` files sat at a
`v0.33.101` generation while the canonical README moved on -- 286,841 against
339,431 -- and four GitBook surfaces sat at two *different* stale generations.
A figure nobody can regenerate is drift by construction; this script is the
mechanism that makes the sync matrix's "translations mirror the root README"
true rather than aspirational (WS-RR RR7.35, register finding 87).

## What makes this harder than the English sync

Three of the target languages inflect the counted noun, so substituting a
numeral can leave the sentence ungrammatical:

    ru   9 601 деклараци*я*   ->  11 287 деклараци*й*
    uk   9 601 деклараці*я*   ->  11 287 деклараці*й*
    ar   9,601 إعلان          ->  11,287 إعلانًا

A sync that rewrote only the digits would publish wrong Russian, Ukrainian and
Arabic, silently, in files nobody who reads this repository's primary language
would check.  So each morphology-bearing word is a declared *slot*: the table
below carries the form for each CLDR plural category, and the script selects by
the category of the number that governs it.  Where a category is needed and not
declared the script **fails**, naming the locale, the row and the category, so a
translator is asked rather than guessed at.

## The declared forms are checked against the file, both directions

A `Word` slot compiles to an alternation of exactly its declared forms, so a
form in the file that the table does not know is a *non-match* and therefore a
hard error -- the table cannot silently drift away from the translation it
claims to model.  A row that matches zero times, or more than once, is likewise
an error and never a silent skip: a scanner's default branch is a decision, and
the fail-closed direction for a rewriter is to refuse input it cannot read.

## What this script deliberately does not own

The surrounding prose.  Every literal in the table is matched verbatim, so a
translator may reword a label, a preposition or a parenthetical freely; the
pattern then stops matching and the script says which row needs its literal
updated.  It rewrites numerals, the `as of vX.Y.Z` measurement stamps, and the
inflected nouns -- nothing else.

Usage:
    scripts/sync_translated_metrics.py            # write through
    scripts/sync_translated_metrics.py --check    # verify only, exit 1 on drift
    scripts/sync_translated_metrics.py --self-test

Exit codes:
    0  in sync (or successfully rewritten)
    1  --check: drift detected
    2  setup error: a row did not match, was ambiguous, or needed an
       undeclared plural form
"""

from __future__ import annotations

import argparse
import io
import json
import re
import sys
import tempfile
from contextlib import redirect_stderr, redirect_stdout
from dataclasses import dataclass, field
from pathlib import Path
from typing import Callable

REPO_ROOT = Path(__file__).resolve().parent.parent

METRIC_KEYS = (
    "prod_loc",
    "prod_files",
    "test_loc",
    "test_files",
    "proved",
    "fixture_lines",
)


# ──────────────────────────────────────────────────────────────────────
# Row slots.  A row is an ordered list of these; both the locating regex
# and the replacement text are derived from the same list, so the two
# cannot disagree about what the row looks like.
# ──────────────────────────────────────────────────────────────────────


@dataclass
class Lit:
    """Literal text, matched verbatim and re-emitted unchanged."""

    text: str


@dataclass
class Num:
    """A metric numeral, formatted with the target's thousands separator."""

    key: str


@dataclass
class Ver:
    """An `as of` measurement stamp, rewritten to `readme_sync.version`."""


@dataclass
class Word:
    """A noun whose form depends on the number governing it.

    `gov` names the metric that governs agreement; `forms` maps a CLDR
    plural category to the form.  A category absent from `forms` is a hard
    error rather than a guess.
    """

    gov: str
    forms: dict


Piece = Lit | Num | Ver | Word


@dataclass
class Row:
    name: str
    pieces: list


@dataclass
class Target:
    path: str
    sep: str
    plural: str
    rows: list = field(default_factory=list)


# ──────────────────────────────────────────────────────────────────────
# CLDR plural categories.  Only the categories the counted nouns below
# actually distinguish are modelled; a language whose rows carry no
# `Word` slot never consults its rule.
# ──────────────────────────────────────────────────────────────────────


def _plural_slavic(n: int) -> str:
    """Russian and Ukrainian share this rule."""
    if n % 10 == 1 and n % 100 != 11:
        return "one"
    if n % 10 in (2, 3, 4) and n % 100 not in (12, 13, 14):
        return "few"
    return "many"


def _plural_arabic(n: int) -> str:
    """CLDR `ar`.

    Note that `other` -- `n % 100` in {0, 1, 2} for `n > 2`, so 100, 101,
    9601 -- is a *different category* from `one` even though both take a
    singular noun: 9,601 is `other`, and a table that declared only `one`
    for the singular form would be refused rather than silently using it.
    The witness suite pins that boundary, because getting it backwards is
    exactly the kind of mistake nobody reading this repository's primary
    language would catch.
    """
    if n == 0:
        return "zero"
    if n == 1:
        return "one"
    if n == 2:
        return "two"
    if 3 <= n % 100 <= 10:
        return "few"
    if 11 <= n % 100 <= 99:
        return "many"
    return "other"


def _plural_french(n: int) -> str:
    """CLDR `fr`.

    0 and 1 share a category, and an exact multiple of a million is `many`
    ("un million de lignes"), which no row below declares -- so a codebase
    that reached exactly 1,000,000 lines would stop this script and ask a
    translator instead of emitting `réparties` under a numeral that governs
    a different construction.
    """
    if n in (0, 1):
        return "one"
    if n >= 1_000_000 and n % 1_000_000 == 0:
        return "many"
    return "other"


def _plural_one_other(n: int) -> str:
    return "one" if n == 1 else "other"


def _plural_invariant(_n: int) -> str:
    return "other"


PLURAL_RULES: dict[str, Callable[[int], str]] = {
    "slavic": _plural_slavic,
    "arabic": _plural_arabic,
    "french": _plural_french,
    "one_other": _plural_one_other,
    "invariant": _plural_invariant,
}


# ──────────────────────────────────────────────────────────────────────
# The targets.
#
# **Translators: this table carries the inflected nouns of the three
# metric rows.**  Everything else in those rows is matched verbatim from
# your file, so you may reword labels, prepositions and parentheticals
# freely.  If you change an inflected noun, change it here too -- the
# script refuses to run when the file holds a form this table does not
# declare, which is deliberate: a silent acceptance would mean the two
# had diverged with nobody told.
#
# Number formatting follows each file's existing convention rather than a
# CLDR default: `hi` groups Western-style (`286,841`, not `2,86,841`) and
# `ar` uses Western digits, because that is what those translations were
# written with, and changing typography is a translator's call, not a
# sync script's.
# ──────────────────────────────────────────────────────────────────────


def _i18n(locale: str, sep: str, plural: str, rows: list) -> Target:
    return Target(path=f"docs/i18n/{locale}/README.md", sep=sep, plural=plural, rows=rows)


TARGETS: list[Target] = [
    # ── Arabic ────────────────────────────────────────────────────────
    # `ملفًا` / `مجموعة اختبار` are the 11..99 (`many`) forms the file
    # already uses for the file and suite counts; `إعلانًا` is the same
    # accusative-singular tamyiz applied to `إعلان`, whose bare form the
    # file carries because 9,601 fell in the `one` category.
    _i18n("ar", ",", "arabic", [
        Row("production", [
            Lit("| **أسطر Lean الإنتاجية** | "), Num("prod_loc"),
            Lit(" عبر "), Num("prod_files"), Lit(" "),
            Word("prod_files", {"many": "ملفًا", "few": "ملفات",
                                "one": "ملف", "other": "ملف"}),
            Lit(" |"),
        ]),
        Row("test", [
            Lit("| **أسطر Lean للاختبارات** | "), Num("test_loc"),
            Lit(" عبر "), Num("test_files"), Lit(" "),
            Word("test_files", {"many": "مجموعة اختبار", "few": "مجموعات اختبار",
                                "one": "مجموعة اختبار", "other": "مجموعة اختبار"}),
            Lit(" |"),
        ]),
        Row("proved", [
            Lit("| **الإعلانات المُبرهَنة** | "), Num("proved"), Lit(" "),
            Word("proved", {"many": "إعلانًا", "few": "إعلانات",
                            "one": "إعلان", "other": "إعلان"}),
            Lit(" theorem/lemma (صفر sorry/axiom) |"),
        ]),
    ]),
    # ── German ────────────────────────────────────────────────────────
    _i18n("de", ".", "one_other", [
        Row("production", [
            Lit("| **Produktions-LoC (Lean)** | "), Num("prod_loc"),
            Lit(" über "), Num("prod_files"), Lit(" "),
            Word("prod_files", {"other": "Dateien", "one": "Datei"}),
            Lit(" |"),
        ]),
        Row("test", [
            Lit("| **Test-LoC (Lean)** | "), Num("test_loc"),
            Lit(" über "), Num("test_files"), Lit(" "),
            Word("test_files", {"other": "Testsuiten", "one": "Testsuite"}),
            Lit(" |"),
        ]),
        Row("proved", [
            Lit("| **Bewiesene Deklarationen** | "), Num("proved"), Lit(" "),
            Word("proved", {"other": "Theorem-/Lemma-Deklarationen",
                            "one": "Theorem-/Lemma-Deklaration"}),
            Lit(" (null sorry/axiom) |"),
        ]),
    ]),
    # ── Spanish ───────────────────────────────────────────────────────
    _i18n("es", ".", "one_other", [
        Row("production", [
            Lit("| **LoC de producción en Lean** | "), Num("prod_loc"),
            Lit(" en "), Num("prod_files"), Lit(" "),
            Word("prod_files", {"other": "archivos", "one": "archivo"}),
            Lit(" |"),
        ]),
        Row("test", [
            Lit("| **LoC de pruebas en Lean** | "), Num("test_loc"),
            Lit(" en "), Num("test_files"), Lit(" "),
            Word("test_files", {"other": "suites de pruebas", "one": "suite de pruebas"}),
            Lit(" |"),
        ]),
        Row("proved", [
            Lit("| **Declaraciones demostradas** | "), Num("proved"), Lit(" "),
            Word("proved", {"other": "declaraciones", "one": "declaración"}),
            Lit(" theorem/lemma (cero sorry/axiom) |"),
        ]),
    ]),
    # ── French ────────────────────────────────────────────────────────
    # `réparties` agrees with the feminine plural "lignes" implied by LoC.
    _i18n("fr", " ", "french", [
        Row("production", [
            Lit("| **LoC Lean de production** | "), Num("prod_loc"), Lit(" "),
            Word("prod_loc", {"other": "réparties", "one": "répartie"}),
            Lit(" sur "), Num("prod_files"), Lit(" "),
            Word("prod_files", {"other": "fichiers", "one": "fichier"}),
            Lit(" |"),
        ]),
        Row("test", [
            Lit("| **LoC Lean de test** | "), Num("test_loc"), Lit(" "),
            Word("test_loc", {"other": "réparties", "one": "répartie"}),
            Lit(" sur "), Num("test_files"), Lit(" "),
            Word("test_files", {"other": "suites de tests", "one": "suite de tests"}),
            Lit(" |"),
        ]),
        Row("proved", [
            Lit("| **Déclarations prouvées** | "), Num("proved"), Lit(" "),
            Word("proved", {"other": "déclarations", "one": "déclaration"}),
            Lit(" theorem/lemma (zéro sorry/axiom) |"),
        ]),
    ]),
]

TARGETS += [
    # ── Hindi ─────────────────────────────────────────────────────────
    # The file counts come first; `फ़ाइलों` / `सुइट्स` are the oblique
    # plurals the postposition `में` governs.
    _i18n("hi", ",", "one_other", [
        Row("production", [
            Lit("| **उत्पादन Lean LoC** | "), Num("prod_files"), Lit(" "),
            Word("prod_files", {"other": "फ़ाइलों", "one": "फ़ाइल"}),
            Lit(" में "), Num("prod_loc"), Lit(" |"),
        ]),
        Row("test", [
            Lit("| **परीक्षण Lean LoC** | "), Num("test_files"), Lit(" "),
            Word("test_files", {"other": "परीक्षण सुइट्स", "one": "परीक्षण सुइट"}),
            Lit(" में "), Num("test_loc"), Lit(" |"),
        ]),
        Row("proved", [
            Lit("| **प्रमाणित घोषणाएँ** | "), Num("proved"), Lit(" प्रमेय/लेम्मा "),
            Word("proved", {"other": "घोषणाएँ", "one": "घोषणा"}),
            Lit(" (शून्य sorry/axiom) |"),
        ]),
    ]),
    # ── Japanese ──────────────────────────────────────────────────────
    # No number agreement; every noun is invariant.
    _i18n("ja", ",", "invariant", [
        Row("production", [
            Lit("| **本番 Lean コード行数** | "), Num("prod_files"),
            Lit(" ファイルにわたる "), Num("prod_loc"), Lit(" 行 |"),
        ]),
        Row("test", [
            Lit("| **テスト Lean コード行数** | "), Num("test_files"),
            Lit(" テストスイートにわたる "), Num("test_loc"), Lit(" 行 |"),
        ]),
        Row("proved", [
            Lit("| **証明済み宣言数** | "), Num("proved"),
            Lit(" 件の定理/補題宣言（sorry/axiom ゼロ） |"),
        ]),
    ]),
    # ── Korean ────────────────────────────────────────────────────────
    _i18n("ko", ",", "invariant", [
        Row("production", [
            Lit("| **프로덕션 Lean LoC** | "), Num("prod_files"), Lit("개 파일, "),
            Num("prod_loc"), Lit("줄 |"),
        ]),
        Row("test", [
            Lit("| **테스트 Lean LoC** | "), Num("test_files"), Lit("개 테스트 스위트, "),
            Num("test_loc"), Lit("줄 |"),
        ]),
        Row("proved", [
            Lit("| **증명된 선언** | "), Num("proved"),
            Lit("개 theorem/lemma 선언 (sorry/axiom 제로) |"),
        ]),
    ]),
    # ── Portuguese (Brazil) ───────────────────────────────────────────
    _i18n("pt-BR", ".", "one_other", [
        Row("production", [
            Lit("| **LoC Lean de produção** | "), Num("prod_loc"),
            Lit(" em "), Num("prod_files"), Lit(" "),
            Word("prod_files", {"other": "arquivos", "one": "arquivo"}),
            Lit(" |"),
        ]),
        Row("test", [
            Lit("| **LoC Lean de testes** | "), Num("test_loc"),
            Lit(" em "), Num("test_files"), Lit(" "),
            Word("test_files", {"other": "suítes de testes", "one": "suíte de testes"}),
            Lit(" |"),
        ]),
        Row("proved", [
            Lit("| **Declarações provadas** | "), Num("proved"), Lit(" "),
            Word("proved", {"other": "declarações", "one": "declaração"}),
            Lit(" de teorema/lema (zero sorry/axiom) |"),
        ]),
    ]),
    # ── Russian ───────────────────────────────────────────────────────
    # `строка/строки/строк` and `декларация/декларации/деклараций` are the
    # nominative-singular, paucal and genitive-plural forms the numeral
    # governs; `файле/файлах` and `тест-сьюте/тест-сьютах` are the
    # prepositional forms after `в`.
    _i18n("ru", " ", "slavic", [
        Row("production", [
            Lit("| **Продуктовый код (Lean LoC)** | "), Num("prod_loc"), Lit(" "),
            Word("prod_loc", {"one": "строка", "few": "строки", "many": "строк"}),
            Lit(" в "), Num("prod_files"), Lit(" "),
            Word("prod_files", {"one": "файле", "few": "файлах", "many": "файлах"}),
            Lit(" |"),
        ]),
        Row("test", [
            Lit("| **Тестовый код (Lean LoC)** | "), Num("test_loc"), Lit(" "),
            Word("test_loc", {"one": "строка", "few": "строки", "many": "строк"}),
            Lit(" в "), Num("test_files"), Lit(" "),
            Word("test_files", {"one": "тест-сьюте", "few": "тест-сьютах",
                                "many": "тест-сьютах"}),
            Lit(" |"),
        ]),
        Row("proved", [
            Lit("| **Доказанные декларации** | "), Num("proved"), Lit(" "),
            Word("proved", {"one": "декларация", "few": "декларации",
                            "many": "деклараций"}),
            Lit(" theorem/lemma (ноль sorry/axiom) |"),
        ]),
    ]),
    # ── Ukrainian ─────────────────────────────────────────────────────
    _i18n("uk", " ", "slavic", [
        Row("production", [
            Lit("| **Продуктовий код (Lean LoC)** | "), Num("prod_loc"), Lit(" "),
            Word("prod_loc", {"one": "рядок", "few": "рядки", "many": "рядків"}),
            Lit(" у "), Num("prod_files"), Lit(" "),
            Word("prod_files", {"one": "файлі", "few": "файлах", "many": "файлах"}),
            Lit(" |"),
        ]),
        Row("test", [
            Lit("| **Тестовий код (Lean LoC)** | "), Num("test_loc"), Lit(" "),
            Word("test_loc", {"one": "рядок", "few": "рядки", "many": "рядків"}),
            Lit(" у "), Num("test_files"), Lit(" "),
            Word("test_files", {"one": "тест-сьюті", "few": "тест-сьютах",
                                "many": "тест-сьютах"}),
            Lit(" |"),
        ]),
        Row("proved", [
            Lit("| **Доведені декларації** | "), Num("proved"), Lit(" "),
            Word("proved", {"one": "декларація", "few": "декларації",
                            "many": "декларацій"}),
            Lit(" theorem/lemma (нуль sorry/axiom) |"),
        ]),
    ]),
    # ── Chinese (Simplified) ──────────────────────────────────────────
    _i18n("zh-CN", ",", "invariant", [
        Row("production", [
            Lit("| **生产代码行数** | "), Num("prod_loc"), Lit(" 行，分布于 "),
            Num("prod_files"), Lit(" 个文件 |"),
        ]),
        Row("test", [
            Lit("| **测试代码行数** | "), Num("test_loc"), Lit(" 行，分布于 "),
            Num("test_files"), Lit(" 个测试套件 |"),
        ]),
        Row("proved", [
            Lit("| **已证明的声明** | "), Num("proved"),
            Lit(" 个定理/引理声明（零 sorry/axiom） |"),
        ]),
    ]),
]

# ── The GitBook surfaces ──────────────────────────────────────────────
# English nouns are literals here, matching `sync_readme_from_codebase_map.sh`:
# one behaviour for English rather than two.  The `as of vX.Y.Z` stamps are
# rewritten, so a chapter states when its figures were measured and is right
# about it -- an unmaintained stamp beside a maintained figure is worse than
# no stamp.
TARGETS += [
    Target("docs/gitbook/01-project-overview.md", ",", "invariant", [
        Row("current state", [
            Lit("Current state (as of v"), Ver(), Lit("): "), Num("prod_loc"),
            Lit(" lines of production Lean across "), Num("prod_files"),
            Lit(" files, "), Num("test_loc"), Lit(" lines across "),
            Num("test_files"), Lit(" Lean test suites,\n"), Num("proved"),
            Lit(" theorem/lemma declarations, zero unsound constructs."),
        ]),
    ]),
    Target("docs/gitbook/07-testing-and-ci.md", ",", "invariant", [
        Row("fixture line count", [
            Lit("all trace output lines ("), Num("fixture_lines"),
            Lit(" fixture lines at v"), Ver(), Lit(")"),
        ]),
    ]),
    Target("docs/gitbook/17-project-usage-value.md", ",", "invariant", [
        Row("production LoC bullet", [
            Lit("- **"), Num("prod_loc"),
            Lit(" lines** of production Lean code across "), Num("prod_files"),
            Lit(" files (as of\n  v"), Ver(), Lit(";"),
        ]),
        Row("proved bullet", [
            Lit("- **"), Num("proved"),
            Lit(" theorem/lemma declarations** with zero sorry/axiom."),
        ]),
    ]),
    # `docs/gitbook/README.md` is generated from this manifest by
    # `generate_doc_navigation.py`, so the manifest is the target and the
    # chapter follows; writing the chapter directly would be overwritten on
    # the next navigation regeneration.
    Target("docs/gitbook/navigation_manifest.json", ",", "invariant", [
        Row("codebase metrics bullet", [
            Lit("**Codebase metrics:** "), Num("prod_loc"),
            Lit(" production LoC across "), Num("prod_files"),
            Lit(" Lean files, "), Num("test_loc"), Lit(" test LoC across "),
            Num("test_files"), Lit(" suites, "), Num("proved"),
            Lit(" proved declarations, zero "),
        ]),
    ]),
]


# ──────────────────────────────────────────────────────────────────────
# Derivation of the regex and the replacement from one piece list.
# ──────────────────────────────────────────────────────────────────────


def numeral_pattern(sep: str) -> str:
    """Digits grouped by this target's own thousands separator.

    Built from `sep` rather than from a permissive character class so the
    slot cannot swallow a following literal that begins with a digit or a
    separator: `[0-9]+(?:,[0-9]{3})*` stops at `286` in `286 ملفًا` and at
    `286,841` in `286,841 عبر`, where `[0-9,]+` would not.
    """
    if not sep:
        return r"[0-9]+"
    return r"[0-9]+(?:" + re.escape(sep) + r"[0-9]{3})*"


VERSION_PATTERN = r"[0-9]+\.[0-9]+\.[0-9]+"


def row_regex(row: Row, sep: str) -> re.Pattern:
    parts: list[str] = []
    for i, piece in enumerate(row.pieces):
        if isinstance(piece, Lit):
            parts.append(re.escape(piece.text))
        elif isinstance(piece, Num):
            parts.append(f"(?P<s{i}>{numeral_pattern(sep)})")
        elif isinstance(piece, Ver):
            parts.append(f"(?P<s{i}>{VERSION_PATTERN})")
        elif isinstance(piece, Word):
            # Longest first so the alternation is unambiguous when one
            # declared form is a prefix of another.
            forms = sorted(set(piece.forms.values()), key=len, reverse=True)
            alts = "|".join(re.escape(f) for f in forms)
            parts.append(f"(?P<s{i}>{alts})")
        else:  # pragma: no cover - guarded by the dataclass union
            raise AssertionError(f"unknown piece: {piece!r}")
    return re.compile("".join(parts))


def format_number(value: int, sep: str) -> str:
    grouped = f"{value:,}"
    return grouped if sep == "," else grouped.replace(",", sep)


class RowError(Exception):
    """A row could not be read or rendered; the caller exits 2."""


def render_row(row: Row, target: Target, values: dict, version: str) -> str:
    rule = PLURAL_RULES[target.plural]
    out: list[str] = []
    for piece in row.pieces:
        if isinstance(piece, Lit):
            out.append(piece.text)
        elif isinstance(piece, Num):
            out.append(format_number(values[piece.key], target.sep))
        elif isinstance(piece, Ver):
            out.append(version)
        elif isinstance(piece, Word):
            category = rule(values[piece.gov])
            if category not in piece.forms:
                raise RowError(
                    f"{target.path}: row '{row.name}': the {piece.gov} value "
                    f"{values[piece.gov]} needs the '{category}' form of a noun "
                    f"declared only for {sorted(piece.forms)}. Ask a translator "
                    f"for the '{category}' form and add it to TARGETS in "
                    f"scripts/sync_translated_metrics.py -- this script will not "
                    f"guess an inflection."
                )
            out.append(piece.forms[category])
    return "".join(out)


def rewrite_text(text: str, target: Target, values: dict, version: str) -> str:
    """Apply every row of `target` to `text`, or raise `RowError`.

    A row that matches zero times or more than once is an error, never a
    skip: this script produces *rewrites*, and a rewrite it silently
    declines to make is a figure that stays stale while the run reports
    success.
    """
    for row in target.rows:
        pattern = row_regex(row, target.sep)
        matches = list(pattern.finditer(text))
        if not matches:
            raise RowError(
                f"{target.path}: row '{row.name}' did not match. Either the "
                f"prose around the figures was reworded, or an inflected noun "
                f"was changed to a form TARGETS does not declare; update the "
                f"row in scripts/sync_translated_metrics.py."
            )
        if len(matches) > 1:
            raise RowError(
                f"{target.path}: row '{row.name}' matched {len(matches)} times, "
                f"so which occurrence to rewrite is ambiguous; make the row's "
                f"literals specific enough to match exactly one."
            )
        replacement = render_row(row, target, values, version)
        start, end = matches[0].span()
        text = text[:start] + replacement + text[end:]
    return text


def count_lines(path: Path) -> int:
    with path.open("rb") as handle:
        return sum(1 for _ in handle)


def load_metrics(root: Path) -> tuple[dict, str]:
    """The five `readme_sync` figures plus the trace-fixture line count.

    The fixture count is read from the fixture rather than from
    `readme_sync` because it is a different question with a different
    source: `readme_sync` is derived from the Lean declaration surface and
    knows nothing about `tests/fixtures/`.  Adding it to the map would put
    one answer in two places.
    """
    map_path = root / "docs/codebase_map.json"
    if not map_path.is_file():
        raise RowError(
            f"{map_path} not found; run scripts/generate_codebase_map.py first"
        )
    sync = json.loads(map_path.read_text(encoding="utf-8"))["readme_sync"]
    fixture = root / "tests/fixtures/main_trace_smoke.expected"
    values = {
        "prod_loc": sync["production_loc"],
        "prod_files": sync["production_files"],
        "test_loc": sync["test_loc"],
        "test_files": sync["test_files"],
        "proved": sync["proved_theorem_lemma_decls"],
        "fixture_lines": count_lines(fixture) if fixture.is_file() else 0,
    }
    for key in METRIC_KEYS:
        if not isinstance(values[key], int):
            raise RowError(f"metric {key} is not an integer: {values[key]!r}")
    version = str(sync["version"])
    return values, version


def run(root: Path, check_only: bool) -> int:
    values, version = load_metrics(root)
    drift = 0
    for target in TARGETS:
        path = root / target.path
        if not path.is_file():
            raise RowError(f"{target.path}: target file not found")
        original = path.read_text(encoding="utf-8")
        updated = rewrite_text(original, target, values, version)
        if updated == original:
            continue
        if check_only:
            print(f"DRIFT in {target.path}", file=sys.stderr)
            drift = 1
        else:
            path.write_text(updated, encoding="utf-8")
            print(f"  {target.path}: updated")
    if check_only:
        if drift:
            print(
                "FAIL: translated/GitBook metric drift. Run "
                "./scripts/sync_translated_metrics.py to rewrite.",
                file=sys.stderr,
            )
            return 1
        print(
            f"PASS: {len(TARGETS)} translated/GitBook surfaces match "
            "docs/codebase_map.json (readme_sync)."
        )
    return 0


# ──────────────────────────────────────────────────────────────────────
# Witnesses.
#
# Every mutation below is *token preserving*: it keeps the numerals and
# the nouns and breaks the relation between them -- a form the table does
# not declare, a governing number in another plural category, a second
# occurrence of the same row, a numeral slot asked to stop before a
# following digit.  Deleting a row would be caught by any presence check;
# these are the shapes that pass one.
# ──────────────────────────────────────────────────────────────────────


def _slavic_row(label: str) -> Row:
    return Row("proved", [
        Lit(f"| **{label}** | "), Num("proved"), Lit(" "),
        Word("proved", {"one": "декларация", "few": "декларации",
                        "many": "деклараций"}),
        Lit(" theorem/lemma |"),
    ])


def _base_values(**overrides) -> dict:
    values = {
        "prod_loc": 339431, "prod_files": 317, "test_loc": 70565,
        "test_files": 70, "proved": 11287, "fixture_lines": 233,
    }
    values.update(overrides)
    return values


def _expect_row_error(fn, needle: str, name: str, failures: list) -> None:
    try:
        fn()
    except RowError as exc:
        if needle not in str(exc):
            failures.append(f"{name}: RowError raised but did not mention {needle!r}: {exc}")
        return
    failures.append(f"{name}: expected RowError, none raised")


def self_test() -> int:
    failures: list[str] = []
    ru = Target("x.md", " ", "slavic", [_slavic_row("Доказанные декларации")])

    # 1. The category change this cut actually makes: one -> many.
    got = rewrite_text(
        "| **Доказанные декларации** | 9 601 декларация theorem/lemma |",
        ru, _base_values(), "0.34.85")
    want = "| **Доказанные декларации** | 11 287 деклараций theorem/lemma |"
    if got != want:
        failures.append(f"slavic one->many: got {got!r}")

    # 2. ... and a category that does not change keeps its form, so the
    #    rule is selecting rather than always emitting the plural.
    got = rewrite_text(
        "| **Доказанные декларации** | 9 601 декларация theorem/lemma |",
        ru, _base_values(proved=339431), "0.34.85")
    want = "| **Доказанные декларации** | 339 431 декларация theorem/lemma |"
    if got != want:
        failures.append(f"slavic one->one: got {got!r}")

    # 3. Token preserving: the noun is still there, in a form the table
    #    does not declare.  A permissive `\S+` slot would accept it.
    _expect_row_error(
        lambda: rewrite_text(
            "| **Доказанные декларации** | 9 601 декларациями theorem/lemma |",
            ru, _base_values(), "0.34.85"),
        "did not match", "undeclared form", failures)

    # 4. A missing row is an error, not a skip.
    _expect_row_error(
        lambda: rewrite_text("nothing here", ru, _base_values(), "0.34.85"),
        "did not match", "absent row", failures)

    # 5. Two occurrences: which one to rewrite is undecidable, so refuse.
    doubled = ("| **Доказанные декларации** | 9 601 декларация theorem/lemma |\n"
               "| **Доказанные декларации** | 9 601 декларация theorem/lemma |")
    _expect_row_error(
        lambda: rewrite_text(doubled, ru, _base_values(), "0.34.85"),
        "matched 2 times", "ambiguous row", failures)

    # 6. A needed category the table does not declare is refused by name,
    #    never guessed.
    partial = Target("y.md", " ", "slavic", [Row("proved", [
        Lit("| x | "), Num("proved"), Lit(" "),
        Word("proved", {"many": "деклараций"}), Lit(" |"),
    ])])
    _expect_row_error(
        lambda: rewrite_text("| x | 9 601 деклараций |", partial,
                             _base_values(proved=339431), "0.34.85"),
        "'one' form", "undeclared category", failures)

    # 7. The numeral slot must stop at its own group boundary.  With a
    #    permissive `[0-9,]+` the first slot swallows `1,234 x 56` up to
    #    the space and the row still matches -- with the numbers in the
    #    wrong slots.
    two = Target("z.md", ",", "invariant", [Row("pair", [
        Num("prod_loc"), Lit(" x "), Num("prod_files"),
    ])])
    got = rewrite_text("1,234 x 56", two, _base_values(), "0.34.85")
    if got != "339,431 x 317":
        failures.append(f"numeral grouping: got {got!r}")

    # 8. Arabic: the same one -> many crossing, in the language whose
    #    inflection is written with a tanwin rather than a suffix.
    ar = Target("a.md", ",", "arabic", [Row("proved", [
        Lit("| x | "), Num("proved"), Lit(" "),
        Word("proved", {"other": "إعلان", "many": "إعلانًا"}), Lit(" |"),
    ])])
    got = rewrite_text("| x | 9,601 إعلان |", ar, _base_values(), "0.34.85")
    if got != "| x | 11,287 إعلانًا |":
        failures.append(f"arabic one->many: got {got!r}")

    # 9. A version stamp is rewritten, and a two-component version is not
    #    a version stamp.
    ver = Target("v.md", ",", "invariant", [Row("stamp", [
        Lit("as of v"), Ver(), Lit(";"),
    ])])
    got = rewrite_text("as of v0.33.101;", ver, _base_values(), "0.34.85")
    if got != "as of v0.34.85;":
        failures.append(f"version stamp: got {got!r}")
    _expect_row_error(
        lambda: rewrite_text("as of v0.33;", ver, _base_values(), "0.34.85"),
        "did not match", "two-component version", failures)

    # 10. Rewriting is a fixpoint, so `--check` cannot oscillate.
    once = rewrite_text("| **Доказанные декларации** | 9 601 декларация theorem/lemma |",
                        ru, _base_values(), "0.34.85")
    twice = rewrite_text(once, ru, _base_values(), "0.34.85")
    if once != twice:
        failures.append(f"not idempotent: {once!r} -> {twice!r}")

    # 11. The plural rules themselves, at the boundaries that decide the
    #     forms above.
    rule_cases = [
        ("slavic", 1, "one"), ("slavic", 11, "many"), ("slavic", 21, "one"),
        ("slavic", 2, "few"), ("slavic", 12, "many"), ("slavic", 5, "many"),
        ("slavic", 9601, "one"), ("slavic", 11287, "many"),
        ("arabic", 1, "one"), ("arabic", 2, "two"), ("arabic", 3, "few"),
        ("arabic", 9601, "other"), ("arabic", 11287, "many"),
        ("arabic", 100, "other"), ("arabic", 101, "other"),
        ("arabic", 110, "few"), ("arabic", 111, "many"),
        ("french", 0, "one"), ("french", 1, "one"), ("french", 2, "other"),
        ("french", 339431, "other"), ("french", 1_000_000, "many"),
        ("one_other", 1, "one"), ("one_other", 2, "other"),
    ]
    for rule_name, n, expected in rule_cases:
        actual = PLURAL_RULES[rule_name](n)
        if actual != expected:
            failures.append(f"plural {rule_name}({n}) = {actual}, expected {expected}")

    # 12. End to end over a temporary tree: --check reports drift, the
    #     write fixes it, and the second --check passes.
    with tempfile.TemporaryDirectory() as tmp:
        root = Path(tmp)
        (root / "docs").mkdir()
        (root / "docs/codebase_map.json").write_text(json.dumps({"readme_sync": {
            "version": "0.34.85", "production_loc": 339431, "production_files": 317,
            "test_loc": 70565, "test_files": 70, "proved_theorem_lemma_decls": 11287,
        }}), encoding="utf-8")
        stale = root / "docs/stale.md"
        stale.write_text("| x | 9 601 декларация theorem/lemma |\n", encoding="utf-8")
        saved = list(TARGETS)
        sink = io.StringIO()
        try:
            TARGETS[:] = [Target("docs/stale.md", " ", "slavic", [Row("proved", [
                Lit("| x | "), Num("proved"), Lit(" "),
                Word("proved", {"one": "декларация", "few": "декларации",
                                "many": "деклараций"}),
                Lit(" theorem/lemma |"),
            ])])]
            with redirect_stdout(sink), redirect_stderr(sink):
                drifted = run(root, check_only=True)
                wrote = run(root, check_only=False)
                settled = run(root, check_only=True)
            if drifted != 1:
                failures.append("end to end: --check did not report drift")
            if wrote != 0:
                failures.append("end to end: write returned nonzero")
            if settled != 0:
                failures.append("end to end: --check still reports drift after write")
            if "11 287 деклараций" not in stale.read_text(encoding="utf-8"):
                failures.append("end to end: file not rewritten")
        finally:
            TARGETS[:] = saved

    for failure in failures:
        print(f"SELF-TEST FAIL: {failure}", file=sys.stderr)
    if failures:
        return 1
    print(f"PASS: sync_translated_metrics self-test ({len(rule_cases)} plural "
          f"cases + 11 rewrite witnesses).")
    return 0


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__.splitlines()[0])
    parser.add_argument("--check", action="store_true",
                        help="verify only; exit 1 on drift")
    parser.add_argument("--self-test", action="store_true",
                        help="run the witness suite and exit")
    args = parser.parse_args()
    if args.self_test:
        return self_test()
    try:
        return run(REPO_ROOT, check_only=args.check)
    except RowError as exc:
        print(f"ERROR: {exc}", file=sys.stderr)
        return 2


if __name__ == "__main__":
    sys.exit(main())
