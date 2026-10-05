#!/usr/bin/env python3
"""Lean declarations and the references between them, read off the source.

This is the reader behind `docs/codebase_map.json`.  It answers three
questions about the Lean tree without elaborating it:

  1. which declarations each file makes, under their **full names** — the
     namespace they are declared in, not the identifier as written;
  2. on which line each one is declared;
  3. which other declarations of the tree each one's text refers to, each
     reference resolved to **one** declaration the way Lean's name resolution
     would resolve it.

Why it exists.  Its predecessor matched one regular expression per line and
matched every identifier in a body against a global set of *short* names.
Measured against Lean's own environment for the same tree (every constant the
compiled modules define, its declaration range, and the constants its type and
value use), that reader:

  * recorded 1,075 of 19,408 declarations under a wrong name — an identifier
    ending in `?` or `!` (`RHTable.get?` became `RHTable.get`), one with a
    subscript or a Greek letter (`τW5a` became `<anonymous>`), every anonymous
    instance;
  * missed every `where` helper (`parseFdtNodes.go`, …) and recorded 478
    `namespace` commands, a `constant` and a `namespace` parsed out of a
    multi-line string literal, `variable` and `section` lines as declarations;
  * drew 34,894 call edges (22%) Lean does not have: a short name matched
    every declaration of that name in any namespace, a bound variable matched a
    declaration that shares its name, and `x?` matched `x`.

This reader tokenizes instead — comments (nested), string literals (raw,
multi-line and interpolated), character literals, `«quoted»` identifiers,
Lean's full identifier alphabet — and reads commands off the token stream, so
`namespace`/`section`/`end`/`open`/`mutual` scopes are tracked and a header
spread over several lines is one header.  A reference is resolved against the
declarations the referring module can actually see (what it imports,
transitively, plus its own private names), through the current namespace, the
declaration's own namespace (`def A.b` elaborates its body inside `A`) and the
opened namespaces, longest prefix first, as Lean does.  Generalized field
notation (`st.objects.invExt`, `.tcb`) is resolved through the types of the
fields and definitions on the path where the source states them, and against
the types the declaration names otherwise; it is left unresolved rather than
guessed when neither decides it.

What it is not.  It reads syntax, not the elaborated environment, so it cannot
see constants that elaboration generates (equation lemmas, match auxiliaries,
`deriving` instances, macro output), and a reference that only exists after
elaboration (an instance found by unification, a `simp` lemma from the simp
set) is not a reference here.  `scripts/check_module_axioms.py` is the gate
that needs the environment, and it reads the environment.  The measurement
behind the figures above is reproducible with the procedure described in the
`v0.36.44` CHANGELOG entry.
"""
from __future__ import annotations

import re
from dataclasses import dataclass, field

# ── Lexer ────────────────────────────────────────────────────────────────────

# Lean's identifier alphabet (`Lean.isLetterLike`, `isSubScriptAlnum`,
# `isIdFirst`, `isIdRest` in `Init/Meta.lean`): ASCII letters and `_`, Greek
# except λ Π Σ, Coptic, polytonic Greek, the letter-like block and the
# mathematical alphanumerics; digits, `'`, `!`, `?` and subscripts may follow.
_LETTER_LIKE = (
    "α-κμ-ω"      # lower Greek without λ
    "Α-ΟΡ΢Τ-Ω"  # upper Greek without Π Σ
    "ϊ-ϻἀ-῾℀-⅏\U0001d49c-\U0001d59f"
)
_ID_FIRST = "A-Za-z_" + _LETTER_LIKE
_ID_REST = _ID_FIRST + "0-9'!?₀-₉ₐ-ₜᵢ-ᵪⱼ"
_COMPONENT = rf"(?:«[^»\n]*»|[{_ID_FIRST}][{_ID_REST}]*)"
_IDENT_RE = re.compile(rf"{_COMPONENT}(?:\.{_COMPONENT})*")

OPEN_BRACKETS = {"(": ")", "[": "]", "{": "}", "⟨": "⟩", "⦃": "⦄", "⟦": "⟧", "@[": "]"}
CLOSE_BRACKETS = {")", "]", "}", "⟩", "⦄", "⟧"}

# Functions that take an interpolated string without an `x!` prefix.
_INTERPOLATING = {"throwError", "throwErrorAt", "logInfo", "logInfoAt", "logWarning", "logError"}


class LexError(ValueError):
    """The source does not tokenize: an unterminated comment or literal.

    Raised rather than tolerated — a reader that guessed where the comment ends
    would silently drop or invent every declaration after it.
    """


@dataclass(slots=True)
class Tok:
    kind: str    # "id" | "sym" | "str" | "num" | "char" | "name"
    text: str    # empty for "str": a literal's content is never code
    line: int    # 1-based
    col: int     # 0-based
    first: bool  # first token on its line


# One pattern, tried at each position; the group that matched says what the
# token is.  Order matters: a raw string `r"…"` before the identifier `r`, a
# block comment before the symbol `/`.
_TOKEN_RE = re.compile(
    r"(?P<nl>\n)|(?P<ws>[ \t\r]+)|(?P<lc>--[^\n]*)|(?P<bc>/-)|(?P<str>\")|(?P<raw>r#*\")"
    rf"|(?P<id>{_COMPONENT}(?:\.{_COMPONENT})*)"
    r"|(?P<bt>``?)|(?P<char>'(?:\\(?:u\{[0-9a-fA-F]+\}|x[0-9a-fA-F]{2}|.)|[^\\\n'])')"
    r"|(?P<num>[0-9][0-9A-Za-z_]*(?:\.[0-9][0-9A-Za-z_]*)?)"
    r"|(?P<sym>:=|=>|\.\.|::|<;>|@\[|.)",
    re.DOTALL,
)
_BLOCK_RE = re.compile(r"/-|-/")


def tokenize(src: str) -> list[Tok]:
    toks: list[Tok] = []
    _lex(src, 0, len(src), 1, 0, toks)
    return toks


def _lex(src: str, i: int, n: int, line: int, line_start: int, toks: list[Tok]) -> None:
    """Tokenize `src[i:n]` into `toks`, numbering lines from `line`."""
    match = _TOKEN_RE.match
    append = toks.append
    last_line = toks[-1].line if toks else 0
    while i < n:
        m = match(src, i, n)
        kind = m.lastgroup
        if kind == "ws" or kind == "lc":
            i = m.end()
            continue
        if kind == "nl":
            line += 1
            i = line_start = i + 1
            continue
        col = i - line_start
        if kind == "id":
            append(Tok("id", m.group(), line, col, last_line != line))
            last_line = line
            i = m.end()
            continue
        if kind == "sym":
            append(Tok("sym", m.group(), line, col, last_line != line))
            last_line = line
            i = m.end()
            continue
        if kind == "bc":
            depth, j = 1, i + 2
            while depth:
                t = _BLOCK_RE.search(src, j, n)
                if t is None:
                    raise LexError(f"block comment opened on line {line} is never closed")
                depth += 1 if t.group() == "/-" else -1
                j = t.end()
            newlines = src.count("\n", i, j)
            if newlines:
                line += newlines
                line_start = src.rfind("\n", i, j) + 1
            i = j
            continue
        if kind == "str":
            prev = toks[-1] if toks else None
            interpolated = bool(prev and prev.kind == "id" and prev.line == line
                                and (prev.text.endswith("!") or prev.text in _INTERPOLATING))
            start_line, j = line, i + 1
            while True:
                if j >= n:
                    raise LexError(f"string literal opened on line {start_line} is never closed")
                ch = src[j]
                if ch == "\\":
                    j += 2
                elif ch == '"':
                    break
                elif ch == "{" and interpolated:
                    # `{…}` inside an interpolated string is code.
                    depth, k = 1, j + 1
                    while k < n and depth:
                        if src[k] == "{":
                            depth += 1
                        elif src[k] == "}":
                            depth -= 1
                        k += 1
                    _lex(src, j + 1, k - 1, start_line + src.count("\n", i, j),
                         src.rfind("\n", 0, j + 1) + 1, toks)
                    j = k
                else:
                    j += 1
            append(Tok("str", "", start_line, col, last_line != start_line))
            last_line = start_line
            newlines = src.count("\n", i, j)
            if newlines:
                line = start_line + newlines
                line_start = src.rfind("\n", i, j) + 1
            i = j + 1
            continue
        if kind == "raw":
            terminator = '"' + "#" * (m.end() - i - 2)
            close = src.find(terminator, m.end(), n)
            if close == -1:
                raise LexError(f"raw string literal opened on line {line} is never closed")
            end = close + len(terminator)
            append(Tok("str", "", line, col, last_line != line))
            last_line = line
            newlines = src.count("\n", i, end)
            if newlines:
                line += newlines
                line_start = src.rfind("\n", i, end) + 1
            i = end
            continue
        if kind == "bt":
            ident = _IDENT_RE.match(src, m.end(), n)
            if ident and m.group() == "``":
                i = m.end()          # ``name resolves at elaboration: lex the name as a reference
                continue
            if ident:
                append(Tok("name", ident.group(), line, col, last_line != line))   # `name: a literal
                last_line = line
                i = ident.end()
                continue
            append(Tok("sym", "`", line, col, last_line != line))
            last_line = line
            i += 1
            continue
        # char, num
        append(Tok(kind, m.group(), line, col, last_line != line))
        last_line = line
        i = m.end()


# ── Commands ─────────────────────────────────────────────────────────────────

# Declaration commands: each defines one named constant (`example` none).
DECL_KEYWORDS = {
    "def", "theorem", "lemma", "abbrev", "instance", "opaque", "axiom", "example",
    "inductive", "structure", "class",
}
TYPE_KINDS = {"inductive", "structure", "class"}
_BODY_KINDS = {"def", "theorem", "lemma", "abbrev", "instance", "opaque"}
_MODIFIERS = {"private", "protected", "noncomputable", "unsafe", "partial", "nonrec",
              "scoped", "local", "public", "meta"}
# A token that begins a command when it opens a line at or left of the column
# the current command started in.  Tactic blocks and terms are indented past
# it, so `open Classical in` inside a proof does not end the declaration.
_COMMAND_KEYWORDS = DECL_KEYWORDS | _MODIFIERS | {
    "namespace", "section", "end", "open", "variable", "universe", "set_option",
    "attribute", "mutual", "export", "syntax", "macro", "macro_rules", "notation",
    "infix", "infixl", "infixr", "prefix", "postfix", "elab", "elab_rules",
    "initialize", "builtin_initialize", "declare_syntax_cat", "deriving", "import",
    "add_decl_doc", "register_option", "omit", "include",
}


_NOTATION_KEYWORDS = {"syntax", "macro", "elab", "notation", "infix", "infixl", "infixr", "prefix", "postfix"}


@dataclass
class Decl:
    kind: str
    name: str           # relative to the enclosing namespace, as declared
    full_name: str      # "" when the declaration is anonymous
    line: int           # line of the declaration keyword
    module: str = ""
    private: bool = False
    parent: str = ""    # constructors, fields and `where` helpers: their owner
    namespace: str = ""
    opens: tuple[str, ...] = ()
    span: tuple[int, int] = (0, 0)     # token range of the whole command
    header: tuple[int, int] = (0, 0)   # token range of binders and type
    type_head: str = ""                # head identifier of the stated type
    derived: tuple[str, ...] = ()      # `deriving` classes (types only)
    header_toks: list = field(default_factory=list)  # unnamed instances: binders and type


def _join(*parts: str) -> str:
    return ".".join(p for p in parts if p)


def _unquote(name: str) -> str:
    return name.replace("«", "").replace("»", "")


def _balanced_end(toks: list[Tok], k: int, end: int) -> int:
    """`k` at an opening bracket: the index just past its partner."""
    depth = 0
    while k < end:
        t = toks[k]
        if t.kind == "sym":
            if t.text in OPEN_BRACKETS:
                depth += 1
            elif t.text in CLOSE_BRACKETS:
                depth -= 1
                if depth == 0:
                    return k + 1
        k += 1
    return k


def _depth0(toks: list[Tok], start: int, end: int):
    """Yield (index, token) for the tokens of `toks[start:end]` outside brackets."""
    depth = 0
    for k in range(start, end):
        t = toks[k]
        if t.kind == "sym":
            if t.text in OPEN_BRACKETS:
                depth += 1
                continue
            if t.text in CLOSE_BRACKETS:
                depth = max(0, depth - 1)
                continue
        if depth == 0:
            yield k, t


@dataclass
class FileParse:
    toks: list[Tok]
    decls: list[Decl]
    imports: list[str]


def parse_file(src: str, module: str = "") -> FileParse:
    toks = tokenize(src)
    n = len(toks)
    decls: list[Decl] = []
    imports: list[str] = []
    # (kind, namespace components, opens) — `namespace A.B` is one entry,
    # closed by one `end A.B`.
    scopes: list[tuple[str, list[str], list[str]]] = [("file", [], [])]

    def current_namespace() -> str:
        return _join(*(c for s in scopes for c in s[1]))

    def current_opens() -> list[str]:
        return [o for s in scopes for o in s[2]]

    def starts_command(k: int) -> bool:
        t = toks[k]
        if not t.first:
            return False
        if t.kind == "sym":
            return t.text == "@[" or (t.text == "#" and k + 1 < n and toks[k + 1].kind == "id")
        if t.kind != "id" or t.text not in _COMMAND_KEYWORDS:
            return False
        if t.text == "deriving":   # `deriving instance …` is a command; `deriving Repr` is not
            return k + 1 < n and toks[k + 1].text == "instance"
        return True

    def command_end(k: int, col: int) -> int:
        depth = 0
        while k < n:
            t = toks[k]
            if depth == 0 and t.first and t.col <= col and starts_command(k):
                return k
            if t.kind == "sym":
                if t.text in OPEN_BRACKETS:
                    depth += 1
                elif t.text in CLOSE_BRACKETS:
                    depth = max(0, depth - 1)
            k += 1
        return n

    def open_names(j: int, line: int) -> tuple[list[str], int]:
        names: list[str] = []
        while j < n and toks[j].kind == "id" and toks[j].line == line \
                and toks[j].text not in ("in", "hiding", "renaming") and toks[j].text not in _COMMAND_KEYWORDS:
            if toks[j].text != "scoped":
                names.append(_unquote(toks[j].text))
            j += 1
            if j < n and toks[j].text == "(":
                j = _balanced_end(toks, j, n)
        return names, j

    i = 0
    while i < n:
        if not starts_command(i):
            i += 1
            continue
        start, col = i, toks[i].col
        private = False
        local_opens: list[str] = []
        # Prefixes: attributes, modifiers, `set_option … in`, `open … in`.
        while i < n:
            t = toks[i]
            if t.kind == "sym" and t.text == "@[":
                i = _balanced_end(toks, i, n)
            elif t.kind == "id" and t.text in _MODIFIERS:
                private = private or t.text == "private"
                i += 1
            elif t.kind == "id" and t.text == "set_option" and i + 3 < n and toks[i + 3].text == "in":
                i += 4
            elif t.kind == "id" and t.text == "open":
                names, j = open_names(i + 1, t.line)
                if j < n and toks[j].text == "in":
                    local_opens += names
                    i = j + 1
                else:
                    break
            else:
                break
        if i >= n:
            break
        t = toks[i]
        kw = t.text if t.kind == "id" else ""
        nxt = toks[i + 1] if i + 1 < n else None
        same_line_id = nxt is not None and nxt.kind == "id" and nxt.line == t.line \
            and nxt.text not in _COMMAND_KEYWORDS

        if kw == "import":
            if nxt is not None and nxt.kind == "id":
                imports.append(_unquote(nxt.text))
            i += 2
            continue
        if kw == "namespace" and nxt is not None and nxt.kind == "id":
            scopes.append(("namespace", _unquote(nxt.text).split("."), []))
            i += 2
            continue
        if kw in ("section", "mutual"):
            scopes.append((kw, [], []))
            i += 2 if (kw == "section" and same_line_id) else 1
            continue
        if kw == "end":
            if len(scopes) > 1:
                scopes.pop()
            i += 2 if same_line_id else 1
            continue
        if kw == "open":
            names, i = open_names(i + 1, t.line)
            scopes[-1][2].extend(names)
            continue
        if kw in ("initialize", "builtin_initialize") and same_line_id \
                and i + 2 < n and toks[i + 2].kind == "sym" and toks[i + 2].text == ":":
            # `initialize ref : IO.Ref σ ← …` declares the constant `ref`.
            ns = current_namespace()
            nm = _unquote(nxt.text)
            end = command_end(i + 2, col)
            decls.append(Decl("initialize", nm, _join(ns, nm), t.line, module=module, private=private,
                              namespace=ns, opens=tuple(current_opens() + local_opens), span=(start, end),
                              header=(i + 2, end), type_head=toks[i + 3].text if i + 3 < n else ""))
            i = end
            continue
        if kw in DECL_KEYWORDS:
            made = _declaration(toks, i, kw, start, col, private, current_namespace(),
                                tuple(current_opens() + local_opens), module, command_end)
            decls.extend(made)
            i = max(made[0].span[1], i + 1)
            continue
        end = command_end(i + 1, col)
        if kw in _NOTATION_KEYWORDS:
            # `syntax (name := foo) …` declares the parser `foo`; without a
            # `name :=` the name is Lean's to generate, and is not guessed.
            for x in range(i + 1, min(end, i + 8)):
                if toks[x].text == "name" and x + 2 < end and toks[x + 1].text == ":=" and toks[x + 2].kind == "id":
                    ns = current_namespace()
                    nm = _unquote(toks[x + 2].text)
                    decls.append(Decl(kw, nm, _join(ns, nm), t.line, module=module, private=private,
                                      namespace=ns, opens=tuple(current_opens() + local_opens), span=(start, end)))
                    break
        # Any other command (`attribute`, `macro_rules`, `#eval`, …) is skipped
        # whole: a quotation inside it may hold text shaped like a declaration.
        i = max(end, i + 1)
    return FileParse(toks, decls, imports)


def _declaration(toks, i, kw, start, col, private, ns, opens, module, command_end) -> list[Decl]:
    n = len(toks)
    kind = kw
    j = i + 1
    if kind == "class" and j < n and toks[j].text in ("inductive", "abbrev"):
        j += 1
    name = ""
    if kind == "instance":
        if j < n and toks[j].text == "(":            # `(priority := …)`
            j = _balanced_end(toks, j, n)
        if j < n and toks[j].kind == "id" and toks[j].text != "where":
            name = toks[j].text
            j += 1
    elif kind != "example" and j < n and toks[j].kind == "id":
        name = toks[j].text
        j += 1
    end = command_end(j, col)

    header_end = end
    for k, t in _depth0(toks, j, end):
        if t.text in (":=", "|") or (t.kind == "id" and t.text in ("where", "deriving")):
            header_end = k
            break
    type_head = ""
    for k, t in _depth0(toks, j, header_end):
        if t.kind == "sym" and t.text == ":" and k + 1 < header_end and toks[k + 1].kind == "id":
            type_head = toks[k + 1].text

    written = _unquote(name)
    if not written:
        full = ""
    elif written.startswith("_root_."):
        full = written[len("_root_."):]
    else:
        full = _join(ns, written)
    rel = full[len(ns) + 1:] if ns and full.startswith(ns + ".") else full
    d = Decl(kind=kind, name=rel, full_name=full, line=toks[i].line, module=module, private=private,
             namespace=ns, opens=opens, span=(start, end), header=(j, header_end), type_head=type_head)
    out = [d]
    if full and kind in TYPE_KINDS:
        out += _type_members(toks, header_end, end, d)
    elif full and kind in _BODY_KINDS:
        out += _where_helpers(toks, j, end, d)
        out += _let_rec_helpers(toks, header_end, end, d)
    return out


def _let_rec_helpers(toks: list[Tok], k: int, end: int, d: Decl) -> list[Decl]:
    """`let rec go …` inside a body declares `f.go`, like a `where` helper.

    Its span runs until the first line that starts at or left of the `let`.
    """
    out: list[Decl] = []
    kind = "theorem" if d.kind == "theorem" else "def"
    for x in range(k, end - 2):
        if toks[x].kind == "id" and toks[x].text == "let" and toks[x + 1].text == "rec" \
                and toks[x + 2].kind == "id":
            col = toks[x].col if toks[x].first else min(toks[x].col, _line_indent(toks, x))
            stop = x + 3
            while stop < end and not (toks[stop].first and toks[stop].col <= col):
                stop += 1
            nm = _unquote(toks[x + 2].text)
            out.append(Decl(kind, f"{d.name}.{nm}", _join(d.full_name, nm), toks[x + 2].line,
                            module=d.module, private=d.private, parent=d.full_name,
                            namespace=d.namespace, opens=d.opens, span=(x + 2, stop)))
    return out


def _line_indent(toks: list[Tok], x: int) -> int:
    """Column of the first token on token `x`'s line."""
    while x > 0 and not toks[x].first:
        x -= 1
    return toks[x].col


def _type_members(toks: list[Tok], k: int, end: int, d: Decl) -> list[Decl]:
    """Constructors and structure fields, and the `deriving` clause.

    Members are not declarations of the map; they are indexed so that a
    reference to `SyscallId.send` resolves to `SyscallId` rather than to an
    unrelated declaration that happens to share the name.
    """
    out: list[Decl] = []

    def member(kind: str, nm: str, line: int, type_head: str = "") -> None:
        nm = _unquote(nm)
        out.append(Decl(kind, nm, _join(d.full_name, nm), line, module=d.module, private=d.private,
                        parent=d.full_name, namespace=d.namespace, opens=d.opens, type_head=type_head))

    derived: list[str] = []
    for x in range(k, end):
        if toks[x].kind == "id" and toks[x].text == "deriving":
            y = x + 1
            while y < end and toks[y].kind == "id":
                derived.append(toks[y].text)
                y += 1
                if y < end and toks[y].text == ",":
                    y += 1
            break
    d.derived = tuple(derived)

    if k >= end:
        return out
    body_kind = toks[k].text
    is_inductive = d.kind == "inductive" or any(t.text == "|" for _, t in _depth0(toks, k, end))
    if is_inductive:
        for x, t in _depth0(toks, k, end):
            if t.kind == "id" and t.text == "deriving":
                break
            if t.kind == "sym" and t.text == "|" and x + 1 < end and toks[x + 1].kind == "id":
                member("ctor", toks[x + 1].text, toks[x + 1].line)
        return out
    if body_kind not in ("where", ":="):
        member("ctor", "mk", d.line)
        return out
    k += 1
    if k + 1 < end and toks[k].kind == "id" and toks[k + 1].text == "::":
        member("ctor", toks[k].text, toks[k].line)
        k += 2
    else:
        member("ctor", "mk", d.line)
    field_col = None
    depth = 0
    while k < end:
        t = toks[k]
        if depth == 0 and t.kind == "id" and t.text == "deriving":
            break
        if t.kind == "sym" and t.text in OPEN_BRACKETS:
            if depth == 0 and t.first and (field_col is None or t.col == field_col) and t.text in ("(", "{", "[", "⦃"):
                field_col = t.col
                m = k + 1
                names = []
                while m < end and toks[m].kind == "id":
                    names.append(toks[m].text)
                    m += 1
                head = toks[m + 1].text if m + 1 < end and toks[m].text == ":" and toks[m + 1].kind == "id" else ""
                for nm in names:
                    member("field", nm, toks[k].line, head)
            depth += 1
        elif t.kind == "sym" and t.text in CLOSE_BRACKETS:
            depth -= 1
        elif depth == 0 and t.first and t.kind == "id" and (field_col is None or t.col == field_col):
            m = k
            names = []
            while m < end and toks[m].kind == "id" and toks[m].line == t.line:
                names.append(toks[m].text)
                m += 1
            if m < end and toks[m].kind == "sym" and toks[m].text in (":", ":=", "(", "{", "[", "⦃"):
                if field_col is None:
                    field_col = t.col
                head = toks[m + 1].text if toks[m].text == ":" and m + 1 < end and toks[m + 1].kind == "id" else ""
                for nm in names:
                    if nm not in ("private", "protected"):
                        member("field", nm, t.line, head)
            k = m
            continue
        k += 1
    return out


def _where_helpers(toks: list[Tok], j: int, end: int, d: Decl) -> list[Decl]:
    """`def f … := body where go …` declares `f.go`; so does a `theorem`.

    A `where` straight after the signature is a structure instance — its
    entries are field values, not declarations — so only a `where` that follows
    the body (`:=` or match alternatives) introduces helpers.  Each helper
    starts on its own line at the column of the first.
    """
    out: list[Decl] = []
    seen_body = False
    for k, t in _depth0(toks, j, end):
        if t.kind == "sym" and t.text in (":=", "|"):
            seen_body = True
            continue
        if not (t.kind == "id" and t.text == "where"):
            continue
        if not seen_body:
            return out
        kind = "theorem" if d.kind == "theorem" else "def"
        col = None
        m = k + 1
        while m < end:
            tt = toks[m]
            if (tt.first or m == k + 1) and (col is None or tt.col == col):
                if col is None:
                    col = tt.col
                p = m
                while p < end and toks[p].kind == "sym" and toks[p].text == "@[":
                    p = _balanced_end(toks, p, end)
                while p < end and toks[p].kind == "id" and toks[p].text in _MODIFIERS | {"theorem", "def"}:
                    p += 1
                if p < end and toks[p].kind == "id" and toks[p].text not in ("termination_by", "decreasing_by"):
                    nm = _unquote(toks[p].text)
                    out.append(Decl(kind, f"{d.name}.{nm}", _join(d.full_name, nm), toks[p].line,
                                    module=d.module, private=d.private, parent=d.full_name,
                                    namespace=d.namespace, opens=d.opens, span=(p, end)))
                elif p < end and toks[p].text in ("termination_by", "decreasing_by"):
                    break
            m += 1
            while m < end and not toks[m].first:
                m += 1
        # A helper's span runs to the next helper.
        for a, b in zip(out, out[1:]):
            a.span = (a.span[0], b.span[0])
        return out
    return out


# ── The corpus and name resolution ──────────────────────────────────────────

# Words after which the identifiers on the same line are bound locally.
_BINDER_INTRO = {"fun", "λ", "∀", "∃", "∃!", "Σ", "Π", "intro", "intros", "rintro", "obtain", "rcases",
                 "let", "have", "with", "case", "next", "generalizing", "at", "induction", "cases",
                 "for", "suffices", "set"}
_WRAPPER_TYPES = {"Option", "Except", "List", "Array", "IO", "BaseIO", "Id", "StateM", "ReaderM"}


def _prefixes(ns: str) -> list[str]:
    parts = ns.split(".") if ns else []
    return [".".join(parts[:k]) for k in range(len(parts), -1, -1)]


class Corpus:
    """Every declaration of the tree, looked up through one module's view.

    A module sees its own declarations and the non-private declarations of the
    modules it imports, transitively — so a reference never resolves to a
    declaration Lean could not have resolved it to.
    """

    def __init__(self) -> None:
        self.by_name: dict[str, list[Decl]] = {}
        self.by_leaf: dict[str, list[str]] = {}
        self.imports: dict[str, list[str]] = {}
        self.files: dict[str, list[Decl]] = {}
        self._closure: dict[str, frozenset[str]] = {}
        self._module = ""
        self._visible: frozenset[str] = frozenset()
        self._cache: dict = {}

    def add_file(self, module: str, decls: list[Decl], imports: list[str]) -> None:
        self.imports[module] = imports
        self.files[module] = decls
        for d in decls:
            self.add(d)

    def add(self, d: Decl) -> None:
        if not d.full_name:
            return
        entries = self.by_name.setdefault(d.full_name, [])
        if not entries:
            self.by_leaf.setdefault(d.full_name.rsplit(".", 1)[-1], []).append(d.full_name)
        entries.append(d)

    def derived_instances(self, namespace: str) -> set[str]:
        """Full names of the instances `deriving` clauses generate in `namespace`."""
        if not hasattr(self, "_derived"):
            self._derived: dict[str, set[str]] = {}
            for entries in self.by_name.values():
                for d in entries:
                    for cls in d.derived:
                        self._derived.setdefault(d.namespace, set()).add(
                            _join(d.namespace, "inst" + _capitalize(cls.rsplit(".", 1)[-1]) + d.name.rsplit(".", 1)[-1]))
        return self._derived.get(namespace, set())

    def closure(self, module: str) -> frozenset[str]:
        if module not in self._closure:
            seen: set[str] = set()
            stack = list(self.imports.get(module, ()))
            while stack:
                m = stack.pop()
                if m not in seen:
                    seen.add(m)
                    stack.extend(self.imports.get(m, ()))
            self._closure[module] = frozenset(seen)
        return self._closure[module]

    def enter(self, module: str) -> None:
        self._module = module
        self._visible = self.closure(module)
        self._cache = {}

    def get(self, name: str) -> Decl | None:
        for d in self.by_name.get(name, ()):
            if d.module == self._module or (not d.private and d.module in self._visible):
                return d
        return None

    def resolve(self, ident: str, ctx: tuple[str, ...], opens: tuple[str, ...]) -> tuple[Decl | None, list[str]]:
        """Resolve `ident` as Lean would without types: the longest prefix of
        it that names a visible declaration, through each namespace of `ctx`
        (innermost first, then its parents), then through `opens`.  Returns the
        declaration and the trailing components (field accesses)."""
        key = (ident, ctx, opens)
        hit = self._cache.get(key)
        if hit is not None:
            return hit
        ident = _unquote(ident)
        parts = ident.split(".")
        result: tuple[Decl | None, list[str]] = (None, parts)
        if parts[0] == "_root_":
            d = self.get(".".join(parts[1:]))
            result = (d, []) if d else (None, parts)
        else:
            for cut in range(len(parts), 0, -1):
                head = ".".join(parts[:cut])
                found = None
                for ns in ctx:
                    for p in _prefixes(ns):
                        found = self.get(_join(p, head))
                        if found:
                            break
                    if found:
                        break
                if not found:
                    for o in opens:
                        for p in _prefixes(ctx[-1] if ctx else ""):
                            found = self.get(_join(p, o, head))
                            if found:
                                break
                        if found:
                            break
                if found:
                    result = (found, parts[cut:])
                    break
        self._cache[key] = result
        return result

    def type_of(self, d: Decl) -> Decl | None:
        """The type a field or definition is stated to have, when the source
        states it as a declaration of the tree (`objects : RHTable …`)."""
        if not d.type_head or d.type_head in _WRAPPER_TYPES:
            return None
        ctx = (d.namespace,) if "." not in d.name else (_join(d.namespace, d.name.rsplit(".", 1)[0]), d.namespace)
        t, rest = self.resolve(d.type_head, ctx, d.opens)
        return t if t is not None and not rest and t.kind in TYPE_KINDS else None


def _owner(d: Decl) -> str:
    """Constructors and fields stand for their type in the reference graph."""
    return d.parent if d.kind in ("ctor", "field") else d.full_name


def references(toks: list[Tok], d: Decl, corpus: Corpus) -> list[str]:
    """The declarations `d`'s text refers to, by full name, sorted."""
    start, end = d.span
    ctx = (d.namespace,)
    if "." in d.name and d.kind not in ("ctor", "field"):
        # `def A.b` elaborates its body with `A` as the current namespace.
        ctx = (_join(d.namespace, d.name.rsplit(".", 1)[0]), d.namespace)
    opens = d.opens
    refs: set[str] = set()
    bound: set[str] = set()

    # Types the declaration names: `x.f` and `.ctor` are resolved against them.
    context_types: set[str] = set()
    for k in range(start, end):
        t = toks[k]
        if t.kind == "id":
            target, _ = corpus.resolve(t.text, ctx, opens)
            if target is None:
                continue
            if target.kind in TYPE_KINDS:
                context_types.add(target.full_name)
            elif target.parent or "." in target.full_name:
                owner = corpus.get(target.parent or target.full_name.rsplit(".", 1)[0])
                if owner is not None and owner.kind in TYPE_KINDS:
                    context_types.add(owner.full_name)

    def method(leaf: str) -> Decl | None:
        hits = []
        for c in corpus.by_leaf.get(_unquote(leaf), ()):
            dd = corpus.get(c)
            if dd is not None and "." in c and c.rsplit(".", 1)[0] in context_types:
                hits.append(dd)
        return hits[0] if len(hits) == 1 else None

    def chain(prev: Decl | None, comps: list[str]) -> None:
        for comp in comps:
            if not comp or comp[0].isdigit():
                return
            nxt = None
            if prev is not None:
                ty = corpus.type_of(prev)
                if ty is not None:
                    nxt = corpus.get(_join(ty.full_name, _unquote(comp)))
            if nxt is None:
                nxt = method(comp)
            if nxt is None:
                return
            refs.add(_owner(nxt))
            prev = nxt

    stack: list[str] = []
    name_seen = False
    k = start
    while k < end:
        t = toks[k]
        if t.kind == "sym":
            if t.text in OPEN_BRACKETS:
                stack.append(t.text)
            elif t.text in CLOSE_BRACKETS and stack:
                stack.pop()
            k += 1
            continue
        if t.kind != "id":
            k += 1
            continue
        text = t.text
        prev = toks[k - 1] if k > start else None
        nxt = toks[k + 1] if k + 1 < end else None
        if not name_seen and d.name and _unquote(text).endswith(d.name.rsplit(".", 1)[-1]):
            name_seen = True       # the declaration's own name in its header
            k += 1
            continue
        if text == "open":         # `open X in` inside a body
            m = k + 1
            extra = []
            while m < end and toks[m].kind == "id" and toks[m].text != "in" and toks[m].line == t.line:
                extra.append(_unquote(toks[m].text))
                m += 1
            opens = opens + tuple(extra)
            k = m
            continue
        if nxt is not None and nxt.kind == "sym" and nxt.text == ":=" and "." not in text and (stack or t.first):
            k += 1                 # a field name in `{ f := v }`, `(f := v)` or a `where` entry
            continue
        if prev is not None and prev.kind == "sym" and prev.text == "." and prev.line == t.line \
                and prev.col + 1 == t.col:
            chain(None, text.split("."))   # `.ctor`, or `(e).f`
            k += 1
            continue
        if stack and stack[-1] in ("(", "{", "⦃", "[") and prev is not None and prev.kind == "sym" \
                and prev.text in ("(", "{", "⦃", "["):
            m = k
            names = []
            while m < end and toks[m].kind == "id" and "." not in toks[m].text:
                names.append(toks[m].text)
                m += 1
            if m < end and toks[m].kind == "sym" and toks[m].text == ":":
                bound.update(names)        # a binder group `(x y : T)`
                k = m
                continue
        if prev is not None and prev.text in _BINDER_INTRO and "." not in text:
            m = k
            while m < end and toks[m].kind == "id" and "." not in toks[m].text \
                    and toks[m].text not in _BINDER_INTRO and toks[m].line == t.line:
                bound.add(toks[m].text)
                m += 1
            if m > k:
                k = m
                continue
        head, _, tail = text.partition(".")
        if head in bound:
            chain(None, tail.split(".") if tail else [])   # `x.f.g` on a local
            k += 1
            continue
        target, rest = corpus.resolve(text, ctx, opens)
        if target is not None:
            refs.add(_owner(target))
            if rest:
                chain(target, rest)
        elif tail:
            chain(None, tail.split(".")[1:] if head and head[0].isupper() else tail.split("."))
        k += 1
    refs.discard(d.full_name)
    refs.discard("")
    return sorted(refs)


# ── Anonymous instances ──────────────────────────────────────────────────────

def _capitalize(s: str) -> str:
    return s[:1].upper() + s[1:]


def instance_name(header: list[Tok], d: Decl, corpus: Corpus, project_root: str) -> str:
    """The name Lean generates for `instance : C T₁ … Tₙ`, or "".

    `Lean.Elab.DeclNameGen` names an anonymous instance after the constants in
    its *elaborated* type, which depends on which arguments are explicit and on
    which binders the type depends on.  Only the form whose elaboration that
    leaves undecided — no binders, and every argument a plain name — is named
    here; anything else stays anonymous rather than carrying a guessed name.
    Measured against the environment, every name this produces is the one Lean
    generated.
    """
    if not header or header[0].kind != "sym" or header[0].text != ":":
        return ""
    names: list[str] = []
    for t in header[1:]:
        if t.kind == "id":
            names.append(_unquote(t.text))
        elif not (t.kind == "sym" and t.text in ("(", ")")):
            return ""
    seen: set[str] = {p for p in _prefixes(d.namespace)[:-1] if corpus.get(p)}
    local = bool(seen)
    out = ""
    for txt in names:
        target, rest = corpus.resolve(txt, (d.namespace,), d.opens)
        if target is not None and rest:
            return ""
        if target is None and not (txt[:1].isupper() and len(txt) > 1):
            return ""      # a variable, or a name this reader cannot place
        full = target.full_name if target is not None else txt
        if full in seen:
            continue
        seen.add(full)
        local = local or target is not None
        out += _capitalize(full.rsplit(".", 1)[-1])
    name = "inst" + out
    if not local:
        name += "_" + project_root[:1].lower() + project_root[1:]
    # `deriving` instances are named first, and `mkUnusedBaseName` steps past them.
    taken = corpus.derived_instances(d.namespace)
    full = _join(d.namespace, name)
    base, suffix = full, 1
    while corpus.get(full) is not None or full in taken:
        full = f"{base}_{suffix}"
        suffix += 1
    return full
