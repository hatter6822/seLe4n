#!/usr/bin/env python3
# seLe4n  - A Lean Microkernel
# Copyright (C) 2026  Adam Hall
# This program comes with ABSOLUTELY NO WARRANTY.
# This is free software, and you are welcome to redistribute it
# under certain conditions. See: https://github.com/hatter6822/seLe4n/blob/main/LICENSE
"""Build `libsele4n.a`: the kernel's Lean object code for the bare-metal target.

WS-BP BP1.  The archive holds the C Lean emits for exactly the modules the
production root `SeLe4n` imports -- its own package modules and the `Init` /
`Std` modules they reach -- compiled freestanding for
`aarch64-unknown-none` with the soft-float ABI the HAL is built with.  It is
what `rust/sele4n-hal/src/boot.rs` asserts is linked; BP2 supplies the
runtime and the libc surface it leaves unresolved, and BP5 links the image.

Every set the build depends on is derived, and each derivation is checked
against an independent answer before anything is compiled:

  * **The closure is the elaborator's.**  A probe imports `SeLe4n` and prints
    `Environment.header.moduleNames`.  Its package half must equal Lake's own
    `SeLe4n:modules` query, it may contain nothing outside `SeLe4n` / `Init` /
    `Std` (the elaborator, `Lean.*`, must not reach the image), and it must be
    disjoint from `scripts/staged_module_allowlist.txt` and `SeLe4n.Testing.*`.
  * **Package C is Lake's `c` facet**, built for exactly those modules, and
    **stdlib C is regenerated** from the toolchain's own sources by the
    toolchain's own `lean -c` -- the toolchain ships `libInit.a` / `libStd.a`
    for the host but no C.  Each generated file's `// Module:` header must name
    the module it was generated for.
  * **The allocator is a relation, not a flag.**  `lean.h`'s inline allocation
    paths are selected by `<lean/config.h>`; the kernel's copy
    (`rust/sele4n-hal/lean_include/lean/config.h`) must be the toolchain's with
    `LEAN_MIMALLOC` replaced by `LEAN_SMALL_ALLOCATOR` and nothing else, and
    the archive must then reference `lean_alloc_small` and no `mi_*` symbol --
    which is what shows the shim was the header actually read.
  * **The compile is the toolchain's clang** (the compiler `leanc` uses),
    `-ffreestanding -nostdlibinc`, `-mgeneral-regs-only -mabi=aapcs-soft`
    (Rust's `aarch64-unknown-none-softfloat`: `+v8a,+strict-align,-neon`,
    static relocation), `-Werror`.  `-mabi=aapcs-soft` is not decoration:
    without it clang 19 refuses a `double` parameter under
    `-mgeneral-regs-only`, and with it a `double` travels in general registers
    exactly as a soft-float Rust caller passes it.
  * **The archive is checked, not trusted.**  Every object defines exactly one
    module initializer; the initializers defined are exactly one per closure
    module and every initializer referenced is defined; no symbol is defined
    twice; each regenerated stdlib module defines exactly the global symbols
    the toolchain's own object for that module defines; and
    `scripts/check_fp_simd_free_objects.py` finds no FP/SIMD register operand.

Output (under `.lake/build/aarch64-unknown-none-softfloat/`):

  libsele4n.a              the archive, members sorted, deterministic headers
  libsele4n.unresolved     the symbols it references and does not define --
                           BP2.2's input, derived here rather than guessed
  stdlib-c/<githash>/      the regenerated stdlib C, cached per toolchain
  obj/                     the objects (rebuilt when their C or the flags move)

    build_lean_aarch64_archive.py [--jobs N]
    build_lean_aarch64_archive.py --self-test
"""

from __future__ import annotations

import argparse
import concurrent.futures
import hashlib
import json
import os
import re
import shutil
import subprocess
import sys
import tempfile
from pathlib import Path

SCRIPTS = Path(__file__).resolve().parent
REPO = SCRIPTS.parent
sys.path.insert(0, str(SCRIPTS))

import check_fp_simd_free_objects as fp_gate  # noqa: E402
import check_kernel_entry_exports as entry_gate  # noqa: E402

ROOT_MODULE = "SeLe4n"
PACKAGE_PREFIX = "SeLe4n"
STDLIB_PREFIXES = ("Init", "Std")
TESTING_PREFIX = "SeLe4n.Testing"
OUT_DIR = REPO / ".lake/build/aarch64-unknown-none-softfloat"
ARCHIVE = OUT_DIR / "libsele4n.a"
UNRESOLVED_REPORT = OUT_DIR / "libsele4n.unresolved"
SHIM_INCLUDE = REPO / "rust/sele4n-hal/lean_include"
STAGED_ALLOWLIST = SCRIPTS / "staged_module_allowlist.txt"
INITIALIZER = re.compile(r"^initialize_\w+$")

# The toolchain's `config.h` macros this build has classified.  A macro the
# toolchain adds and this table does not name stops the build: an
# unclassified configuration switch is one the shim silently drops.
CONFIG_KNOWN = frozenset({"LEAN_MIMALLOC", "LEAN_IS_STAGE0"})
CONFIG_DROPPED = frozenset({"LEAN_MIMALLOC"})
CONFIG_ADDED = {"LEAN_SMALL_ALLOCATOR": ""}
ALLOCATOR_ENTRY = "lean_alloc_small"
# The small-allocator API `lean.h` declares for `LEAN_SMALL_ALLOCATOR`.  The
# toolchain's host runtime is built with mimalloc and defines none of it, so
# whichever of these the archive calls is BP2.1's to provide.
ALLOCATOR_API = frozenset({"lean_alloc_small", "lean_free_small", "lean_small_mem_size"})
RUST_TARGET = "aarch64-unknown-none-softfloat"

# Who provides each unresolved symbol, in the order a symbol is attributed.
# Every class is DERIVED from the provider's own object code or declarations,
# and a symbol no class accounts for stops the build: the report is BP2.2's
# input, and an unattributed symbol is a link failure nobody has planned for.
PROVIDERS = (
    ("allocator", "the small-allocator API the kernel's config.h selects -- the HAL's lean_heap defines it (BP2.1)"),
    ("runtime", "defined by the toolchain's libleanrt.a -- the runtime BP2 builds for the target"),
    ("compiler-builtins", f"defined by Rust's compiler_builtins for {RUST_TARGET} (linked at BP5)"),
    ("hal", "declared @[extern] by a production kernel module -- the HAL's object code defines it"),
    ("stdlib-extern", "declared @[extern] by a closure stdlib module and provided by none of the above (BP2.2)"),
)
MIMALLOC_SYMBOL = re.compile(r"^_?mi_")

# Diagnostics Lean's C generator produces by construction, each with the only
# shape an instance may have.  Every other diagnostic fails the compile
# (`-Werror`), and an instance of one of these that does not match its shape
# fails the census, so "understood" is checked per instance, not asserted.
#
#   unused-but-set-variable -- an IR temporary `x_N` bound to a call whose
#     result is discarded: a `BaseIO Unit` action returns the scalar
#     `lean_box(0)`, so no reference count is owed and nothing leaks.  The
#     generator's own file header disables this diagnostic for GCC; its clang
#     branch predates clang's implementation of it.
#   unused-variable -- `res` in the initializer of a module with no imports
#     (`Init.Prelude`): declared for the per-import checks there are none of.
GENERATOR_DIAGNOSTICS = {
    "unused-but-set-variable": re.compile(r"^variable 'x_\d+' set but not used$"),
    "unused-variable": re.compile(r"^unused variable 'res'$"),
}
CLANG_SUMMARY = re.compile(r"^\d+ warnings? generated\.$")
DIAGNOSTIC = re.compile(r"^(?P<loc>\S+?:\d+:\d+): (?P<sev>warning|error): (?P<msg>.*?) \[(?P<flags>-W[^\]]*)\]$")


# The probe the closure is read from, as a named template with one sentinel
# (the tree's canonical probe spelling: probe text reaches Lean through a
# template and `.replace` over literals).  `loadExts := false`: the question is
# which modules are imported, not what their extensions contain.
CLOSURE_PROBE_TEMPLATE = """import Lean
open Lean

def main : IO UInt32 := do
  initSearchPath (← findSysroot)
  let env ← importModules #[{ module := `@ROOT@ }] {} (loadExts := false)
  for m in env.header.moduleNames do
    IO.println m
  return 0
"""


class Refused(Exception):
    """A condition the build refuses to continue past."""


def run(argv: list[str], **kw) -> subprocess.CompletedProcess:
    result = subprocess.run(argv, capture_output=True, text=True, **kw)
    if result.returncode != 0:
        raise Refused(f"`{' '.join(argv[:4])} …` exited {result.returncode}:\n"
                      f"{(result.stderr or result.stdout).strip()[-2000:]}")
    return result


# ---------------------------------------------------------------------------
# Toolchain
# ---------------------------------------------------------------------------

def toolchain() -> dict[str, str]:
    """The pinned Lean toolchain: prefix, version, githash, clang, llvm-ar."""
    pinned = (REPO / "lean-toolchain").read_text().strip()
    wanted = re.search(r"v(\d+\.\d+\.\d+\S*)$", pinned)
    if not wanted:
        raise Refused(f"lean-toolchain names no version: {pinned!r}")
    version = run(["lean", "--version"], cwd=REPO).stdout
    if f"version {wanted.group(1)}," not in version:
        raise Refused(f"`lean` is not the pinned {pinned}: {version.strip()}")
    prefix = Path(run(["lean", "--print-prefix"], cwd=REPO).stdout.strip())
    githash = run(["lean", "--githash"], cwd=REPO).stdout.strip()
    tools = {"clang": prefix / "bin/clang", "llvm-ar": prefix / "bin/llvm-ar"}
    for name, path in tools.items():
        if not path.is_file():
            raise Refused(f"the toolchain ships no {name} at {path}")
    return {"prefix": str(prefix), "githash": githash, "version": wanted.group(1),
            "clang": str(tools["clang"]), "llvm-ar": str(tools["llvm-ar"])}


def compile_flags(tc: dict[str, str]) -> list[str]:
    prefix = Path(tc["prefix"])
    return [
        "--target=aarch64-unknown-none-elf", "-march=armv8-a",
        "-mgeneral-regs-only", "-mabi=aapcs-soft", "-mstrict-align",
        "-mno-outline-atomics", "-fno-pic",
        "-ffreestanding", "-nostdlibinc",
        "-isystem", str(prefix / "include/clang"),
        "-I", str(SHIM_INCLUDE),
        "-isystem", str(prefix / "include"),
        "-O3", "-DNDEBUG", "-fwrapv", "-fvisibility=hidden",
        "-ffunction-sections", "-fdata-sections",
        "-Wall", "-Wextra", "-Werror",
        # One line per diagnostic, so the census reads every line of stderr
        # rather than guessing which lines are source excerpts.
        "-fno-caret-diagnostics",
        # The two shapes the generator emits by construction are warnings, not
        # errors, and `GENERATOR_DIAGNOSTICS` then classifies every instance:
        # anything else is still an error, and an instance of these two that is
        # not the generator's shape is refused by the census.
        *(f"-Wno-error={d}" for d in GENERATOR_DIAGNOSTICS),
    ]


# ---------------------------------------------------------------------------
# The closure
# ---------------------------------------------------------------------------

def elaborator_closure() -> list[str]:
    closure_probe = CLOSURE_PROBE_TEMPLATE.replace("@ROOT@", ROOT_MODULE)
    with tempfile.TemporaryDirectory() as tmp:
        probe = Path(tmp) / "closure_probe.lean"
        probe.write_text(closure_probe)
        out = run(["lake", "env", "lean", "--run", str(probe)], cwd=REPO).stdout
    return [line.strip() for line in out.splitlines() if line.strip()]


def lake_modules() -> list[str]:
    out = run(["lake", "query", f"{ROOT_MODULE}:modules"], cwd=REPO).stdout
    return [line.strip() for line in out.splitlines() if line.strip()]


def staged_modules() -> set[str]:
    staged = set()
    for line in STAGED_ALLOWLIST.read_text().splitlines():
        entry = line.split("#", 1)[0].strip()
        if entry:
            staged.add(entry)
    if not staged:
        raise Refused(f"{STAGED_ALLOWLIST} lists no module: a partition over nothing decides nothing")
    return staged


def module_family(module: str, prefixes: tuple[str, ...]) -> str | None:
    for prefix in prefixes:
        if module == prefix or module.startswith(prefix + "."):
            return prefix
    return None


def classify_closure(closure: list[str], lake: list[str],
                     staged: set[str]) -> tuple[list[str], list[str]]:
    """(package modules, stdlib modules), or `Refused` naming every violation."""
    problems: list[str] = []
    if len(set(closure)) != len(closure):
        problems.append("the elaborator reported a module twice")
    if ROOT_MODULE not in closure:
        problems.append(f"the closure does not contain its root {ROOT_MODULE}")
    package, stdlib, foreign = [], [], []
    for module in closure:
        family = module_family(module, (PACKAGE_PREFIX,) + STDLIB_PREFIXES)
        if family == PACKAGE_PREFIX:
            package.append(module)
        elif family is not None:
            stdlib.append(module)
        else:
            foreign.append(module)
    if foreign:
        problems.append("modules outside SeLe4n/Init/Std reach the image: "
                        + ", ".join(sorted(foreign)[:12]))
    if set(package) != set(lake):
        only_elab = sorted(set(package) - set(lake))
        only_lake = sorted(set(lake) - set(package))
        problems.append(f"the elaborator and Lake disagree about the package closure: "
                        f"elaborator-only {only_elab[:8]}, Lake-only {only_lake[:8]}")
    leaked = sorted(set(package) & staged)
    if leaked:
        problems.append(f"staged modules reach the image: {leaked[:8]}")
    testing = sorted(m for m in package if module_family(m, (TESTING_PREFIX,)))
    if testing:
        problems.append(f"testing modules reach the image: {testing[:8]}")
    if problems:
        raise Refused("; ".join(problems))
    return sorted(package), sorted(stdlib)


# ---------------------------------------------------------------------------
# C sources
# ---------------------------------------------------------------------------

MODULE_HEADER = re.compile(r"^// Module: (\S+)$", re.MULTILINE)


def header_module(text: str) -> str | None:
    match = MODULE_HEADER.search(text[:4096])
    return match.group(1) if match else None


def package_c(module: str) -> Path:
    return REPO / ".lake/build/ir" / (module.replace(".", "/") + ".c")


def stdlib_c(module: str, tc: dict[str, str]) -> Path:
    return OUT_DIR / "stdlib-c" / tc["githash"] / f"{module}.c"


def build_package_c(package: list[str]) -> None:
    """Lake's own `c` facet, for exactly the closure's package modules."""
    run(["lake", "build", *[f"+{m}:c" for m in package]], cwd=REPO)


def generate_one_stdlib_c(module: str, tc: dict[str, str]) -> None:
    target = stdlib_c(module, tc)
    if target.is_file():
        return
    source = Path(tc["prefix"]) / "src/lean" / (module.replace(".", "/") + ".lean")
    if not source.is_file():
        raise Refused(f"the toolchain ships no source for {module} at {source}")
    target.parent.mkdir(parents=True, exist_ok=True)
    partial = target.with_suffix(".c.partial")
    run([str(Path(tc["prefix"]) / "bin/lean"), "-R", str(Path(tc["prefix"]) / "src/lean"),
         "-c", str(partial), str(source)], cwd=REPO)
    partial.replace(target)


def parallel(fn, items, jobs: int) -> None:
    errors: list[str] = []
    with concurrent.futures.ThreadPoolExecutor(max_workers=jobs) as pool:
        futures = {pool.submit(fn, item): item for item in items}
        for future in concurrent.futures.as_completed(futures):
            try:
                future.result()
            except Refused as exc:
                errors.append(f"{futures[future]}: {exc}")
    if errors:
        raise Refused(f"{len(errors)} failure(s):\n" + "\n".join(sorted(errors)[:20]))


# ---------------------------------------------------------------------------
# The allocator configuration
# ---------------------------------------------------------------------------

def config_items(text: str) -> tuple[dict[str, str], list[str]]:
    """(`#define` NAME -> value, `#include` targets) of a config header."""
    code = re.sub(r"/\*.*?\*/", "", text, flags=re.DOTALL)
    code = re.sub(r"//[^\n]*", "", code)
    defines: dict[str, str] = {}
    includes: list[str] = []
    for line in code.splitlines():
        line = line.strip()
        define = re.match(r"#\s*define\s+(\w+)(?:\s+(.*))?$", line)
        include = re.match(r"#\s*include\s+[<\"]([^>\"]+)[>\"]$", line)
        if define:
            if define.group(1) in defines:
                raise Refused(f"{define.group(1)} is defined twice")
            defines[define.group(1)] = (define.group(2) or "").strip()
        elif include:
            includes.append(include.group(1))
        elif line and not re.match(r"#\s*pragma\s+once$", line):
            raise Refused(f"unrecognised configuration line: {line!r}")
    return defines, includes


def check_config(toolchain_text: str, shim_text: str) -> None:
    """The shim is the toolchain's `config.h` with exactly the classified swap."""
    tc_defs, tc_incs = config_items(toolchain_text)
    shim_defs, shim_incs = config_items(shim_text)
    unclassified = sorted(set(tc_defs) - CONFIG_KNOWN)
    if unclassified:
        raise Refused(f"the toolchain's config.h defines unclassified macros {unclassified}")
    missing = sorted(CONFIG_KNOWN - set(tc_defs))
    if missing:
        raise Refused(f"the toolchain's config.h no longer defines {missing}: reclassify")
    expected = {k: v for k, v in tc_defs.items() if k not in CONFIG_DROPPED}
    expected.update(CONFIG_ADDED)
    if shim_defs != expected:
        raise Refused(f"the kernel's config.h defines {shim_defs}, expected {expected}")
    if shim_incs != tc_incs:
        raise Refused(f"the kernel's config.h includes {shim_incs}, the toolchain's {tc_incs}")


# ---------------------------------------------------------------------------
# Compilation and archiving
# ---------------------------------------------------------------------------

def object_path(module: str) -> Path:
    return OUT_DIR / "obj" / f"{module}.o"


def diagnostics_path(module: str) -> Path:
    return OUT_DIR / "obj" / f"{module}.diag"


def classify_diagnostics(stderr: str) -> tuple[dict[str, int], list[str]]:
    """(count per generator diagnostic, lines that are anything else).

    Every non-empty line must be a classified diagnostic or clang's closing
    count; a line that is neither -- a `note:`, an unparsed diagnostic, a
    `fatal error:` -- is unexplained, which is the fail-closed reading."""
    counts = {name: 0 for name in GENERATOR_DIAGNOSTICS}
    unexplained: list[str] = []
    for line in stderr.splitlines():
        if not line.strip() or CLANG_SUMMARY.match(line):
            continue
        match = DIAGNOSTIC.match(line)
        if not match:
            unexplained.append(line)
            continue
        flag = match.group("flags").split(",")[-1].removeprefix("-W")
        shape = GENERATOR_DIAGNOSTICS.get(flag)
        if match.group("sev") == "warning" and shape and shape.match(match.group("msg")):
            counts[flag] += 1
        else:
            unexplained.append(line)
    return counts, unexplained


def prepare_objects(stamp: str) -> None:
    """Objects built under other flags or another toolchain are discarded."""
    obj = OUT_DIR / "obj"
    stamp_file = OUT_DIR / "obj.stamp"
    if not stamp_file.is_file() or stamp_file.read_text() != stamp:
        shutil.rmtree(obj, ignore_errors=True)
    obj.mkdir(parents=True, exist_ok=True)
    stamp_file.write_text(stamp)


def compile_one(item: tuple[str, Path], tc: dict[str, str], flags: list[str]) -> None:
    module, source = item
    text = source.read_text()
    named = header_module(text)
    if named != module:
        raise Refused(f"{source} is the C of {named!r}, not of {module}")
    target, diag = object_path(module), diagnostics_path(module)
    if (target.is_file() and diag.is_file()
            and target.stat().st_mtime >= source.stat().st_mtime):
        return
    partial = target.with_suffix(".o.partial")
    result = run([tc["clang"], *flags, "-c", str(source), "-o", str(partial)])
    _, unexplained = classify_diagnostics(result.stderr)
    if unexplained:
        raise Refused("diagnostics outside the generator's two shapes:\n"
                      + "\n".join(unexplained[:10]))
    diag.write_text(result.stderr)
    partial.replace(target)


def diagnostic_census(modules: list[str]) -> dict[str, int]:
    """Re-read every object's recorded diagnostics, so an up-to-date object
    that was not recompiled this run is still counted and still classified."""
    total = {name: 0 for name in GENERATOR_DIAGNOSTICS}
    for module in modules:
        counts, unexplained = classify_diagnostics(diagnostics_path(module).read_text())
        if unexplained:
            raise Refused(f"{module}: unexplained diagnostics {unexplained[:3]}")
        for name, n in counts.items():
            total[name] += n
    return total


def build_archive(modules: list[str], tc: dict[str, str]) -> None:
    ARCHIVE.unlink(missing_ok=True)
    partial = ARCHIVE.with_suffix(".a.partial")
    partial.unlink(missing_ok=True)
    run([tc["llvm-ar"], "crsD", str(partial), *[str(object_path(m)) for m in sorted(modules)]])
    partial.replace(ARCHIVE)


# ---------------------------------------------------------------------------
# Symbol checks
# ---------------------------------------------------------------------------

Symbols = dict[str, tuple[set[str], set[str]]]  # unit -> (defined, undefined)


def parse_nm(output: str, source: str) -> Symbols:
    """`llvm-nm -g -P` output, one unit per archive **member instance**.

    An archive may hold two members with one name -- the toolchain's
    `libInit.a` has `Init/Grind.o` and `Init/Data/String/Grind.o`, both
    `Grind.o` -- so a unit is keyed by its header's position, never by its
    name alone: keyed by name, the two merge into one object defining two
    initializers.  Output with no member header is the single object
    `source`."""
    units: Symbols = {}
    current: str | None = None
    ordinal = 0
    for line in output.splitlines():
        if not line.strip():
            continue
        if line.endswith(":") and " " not in line:
            ordinal += 1
            current = f"{source}[{line[:-1]}]#{ordinal}"
            units[current] = (set(), set())
            continue
        fields = line.split()
        if len(fields) < 2:
            raise Refused(f"unreadable llvm-nm line: {line!r}")
        if current is None:
            current = source
            units[current] = (set(), set())
        name, kind = fields[0], fields[1]
        defined, undefined = units[current]
        (undefined if kind in ("U", "w", "v") else defined).add(name)
    return units


def nm(path: Path) -> Symbols:
    tool = fp_gate.rust_llvm_tool("llvm-nm")
    return parse_nm(run([tool, "-g", "-P", str(path)]).stdout, str(path))


def member_module(unit: str) -> str:
    """The module a unit of *our* archive holds: its members are named
    `<module>.o`, so the name is the module."""
    return unit.rpartition("[")[2].partition("]")[0].removesuffix(".o")


def unit_initializers(units: Symbols) -> dict[str, str]:
    """initializer -> unit, refusing a unit that does not define exactly one."""
    owner: dict[str, str] = {}
    for unit, (defined, _) in units.items():
        inits = sorted(s for s in defined if INITIALIZER.match(s))
        if len(inits) != 1:
            raise Refused(f"{unit} defines {len(inits)} module initializers {inits[:4]}, not one")
        owner[inits[0]] = unit
    return owner


def check_archive_symbols(units: Symbols, module_count: int) -> set[str]:
    """The archive-level relations; returns the unresolved symbol set."""
    problems: list[str] = []
    owner = unit_initializers(units)
    if len(owner) != module_count or len(units) != module_count:
        problems.append(f"{len(units)} objects define {len(owner)} initializers "
                        f"for a closure of {module_count} modules")
    defined_all: dict[str, str] = {}
    for unit, (defined, _) in units.items():
        for sym in defined:
            if sym in defined_all:
                problems.append(f"{sym} is defined by both {defined_all[sym]} and {unit}")
            defined_all[sym] = unit
    undefined_all = set().union(*(u for _, u in units.values())) if units else set()
    unresolved = undefined_all - defined_all.keys()
    missing_inits = sorted(s for s in unresolved if INITIALIZER.match(s))
    if missing_inits:
        problems.append(f"module initializers referenced and not defined: {missing_inits[:8]}")
    if ALLOCATOR_ENTRY not in unresolved:
        problems.append(f"the archive does not call {ALLOCATOR_ENTRY}: the small allocator "
                        "was not the configuration the objects were compiled against")
    mimalloc = sorted(s for s in undefined_all | defined_all.keys() if MIMALLOC_SYMBOL.match(s))
    if mimalloc:
        problems.append(f"mimalloc symbols in the archive: {mimalloc[:8]}")
    if problems:
        raise Refused("; ".join(problems[:12]))
    return unresolved


def check_stdlib_fidelity(ours: Symbols, host: Symbols, stdlib: set[str]) -> None:
    """Each regenerated stdlib module defines exactly what the toolchain's object does.

    `stdlib` is the set of initializers the closure's stdlib modules own; each
    is matched to the toolchain's host object defining the same initializer."""
    host_owner = unit_initializers(host)
    our_owner = unit_initializers(ours)
    problems: list[str] = []
    for init in sorted(stdlib):
        if init not in host_owner:
            problems.append(f"{init}: the toolchain's libraries define no such module")
            continue
        mine = ours[our_owner[init]][0]
        theirs = host[host_owner[init]][0]
        if mine != theirs:
            problems.append(f"{init}: +{sorted(mine - theirs)[:4]} -{sorted(theirs - mine)[:4]}")
    if problems:
        raise Refused(f"{len(problems)} regenerated stdlib module(s) differ from the "
                      "toolchain's own objects:\n  " + "\n  ".join(problems[:20]))


def classify_unresolved(unresolved: set[str], runtime: set[str], builtins: set[str],
                        hal: set[str], stdlib_externs: set[str]) -> dict[str, list[str]]:
    """Attribute each unresolved symbol to its provider, or `Refused`.

    A HAL symbol some other provider also defines is refused too: at the
    image link it is a duplicate definition, and whichever the linker prefers
    silently decides whether the kernel reaches the hardware."""
    shadowed = sorted(hal & (runtime | builtins | ALLOCATOR_API))
    if shadowed:
        raise Refused(f"kernel @[extern] symbols another provider also defines: {shadowed[:8]}")
    classes: dict[str, list[str]] = {name: [] for name, _ in PROVIDERS}
    unattributed: list[str] = []
    for sym in sorted(unresolved):
        if sym in ALLOCATOR_API:
            classes["allocator"].append(sym)
        elif sym in runtime:
            classes["runtime"].append(sym)
        elif sym in builtins:
            classes["compiler-builtins"].append(sym)
        elif sym in hal:
            classes["hal"].append(sym)
        elif sym in stdlib_externs:
            classes["stdlib-extern"].append(sym)
        else:
            unattributed.append(sym)
    if unattributed:
        raise Refused(f"{len(unattributed)} unresolved symbol(s) no provider accounts for: "
                      f"{unattributed[:12]}")
    return classes


def defined_symbols(path: Path) -> set[str]:
    return set().union(*(d for d, _ in nm(path).values()))


def rust_target_builtins() -> Path:
    sysroot = Path(run(["rustc", "--print", "sysroot"], cwd=REPO / "rust").stdout.strip())
    found = sorted((sysroot / "lib/rustlib" / RUST_TARGET / "lib").glob("libcompiler_builtins-*.rlib"))
    if len(found) != 1:
        raise Refused(f"expected one compiler_builtins rlib for {RUST_TARGET}, found {len(found)} "
                      f"(install the target: rust/rust-toolchain.toml lists it)")
    return found[0]


def hal_rlib() -> Path:
    """The HAL built for the target, release, with its hardware exports: the
    rlib path cargo's own `compiler-artifact` message names, never a glob over
    `target/`, so a stale rlib from another profile or target cannot answer."""
    out = run(["cargo", "build", "--release", "--target", RUST_TARGET, "-p", "sele4n-hal",
               "--features", "hw_target", "--message-format=json-render-diagnostics"],
              cwd=REPO / "rust").stdout
    rlibs = []
    for line in out.splitlines():
        try:
            msg = json.loads(line)
        except json.JSONDecodeError:
            continue
        if msg.get("reason") == "compiler-artifact" and msg.get("target", {}).get("name") == "sele4n_hal":
            rlibs += [f for f in msg.get("filenames", []) if f.endswith(".rlib")]
    if len(rlibs) != 1:
        raise Refused(f"expected one sele4n_hal rlib for {RUST_TARGET}, cargo reported {rlibs}")
    return Path(rlibs[0])


def global_text(output: str) -> set[str]:
    """The global TEXT symbols in `llvm-nm -g -P` output: functions.  A data
    object under a function's name would satisfy a call at the link and send
    it into data, so only `T` counts as a provider."""
    names = set()
    for line in output.splitlines():
        fields = line.split()
        if len(fields) >= 2 and not line.endswith(":") and fields[1] == "T":
            names.add(fields[0])
    return names


def check_hal_providers(classes: dict[str, list[str]], hal_text: set[str]) -> None:
    """The `allocator` and `hal` classes name the HAL as provider; hold that
    to the HAL's object code.  Every symbol in either class, and the whole
    small-allocator API whether or not this archive calls each member (the
    runtime's free paths call the rest), must be a global function of the
    HAL's rlib."""
    wanted = set(classes["allocator"]) | set(classes["hal"]) | ALLOCATOR_API
    missing = sorted(wanted - hal_text)
    if missing:
        raise Refused(f"{len(missing)} symbol(s) attributed to the HAL that its object code does "
                      f"not define as a function: {missing[:12]}")


def extern_symbols(paths: list[Path]) -> set[str]:
    symbols: set[str] = set()
    for path in paths:
        symbols |= entry_gate.lean_extern_symbols_in(path.read_text())
    return symbols


def write_unresolved_report(classes: dict[str, list[str]]) -> None:
    lines = [
        "# The symbols libsele4n.a references and does not define, by provider.",
        "# Generated by scripts/build_lean_aarch64_archive.py; BP2.2's input.",
    ]
    for name, meaning in PROVIDERS:
        lines.append(f"\n# {name}: {meaning} ({len(classes[name])})")
        lines.extend(classes[name])
    UNRESOLVED_REPORT.write_text("\n".join(lines) + "\n")


# ---------------------------------------------------------------------------
# Driver
# ---------------------------------------------------------------------------

def build(jobs: int) -> int:
    tc = toolchain()
    print(f"[1/8] toolchain {tc['version']} ({tc['githash'][:12]})")
    closure = elaborator_closure()
    package, stdlib = classify_closure(closure, lake_modules(), staged_modules())
    print(f"[2/8] closure: {len(package)} package + {len(stdlib)} stdlib modules "
          f"(elaborator and Lake agree; no staged, testing or Lean.* module)")
    check_config((Path(tc["prefix"]) / "include/lean/config.h").read_text(),
                 (SHIM_INCLUDE / "lean/config.h").read_text())
    print("[3/8] allocator configuration: toolchain config.h with LEAN_MIMALLOC -> LEAN_SMALL_ALLOCATOR")
    build_package_c(package)
    parallel(lambda m: generate_one_stdlib_c(m, tc), stdlib, jobs)
    print(f"[4/8] C: Lake `c` facet for the package, regenerated stdlib C cached under {tc['githash'][:12]}")
    flags = compile_flags(tc)
    prepare_objects(hashlib.sha256("\n".join([tc["githash"], tc["clang"], *flags]).encode()).hexdigest())
    sources = [(m, package_c(m)) for m in package] + [(m, stdlib_c(m, tc)) for m in stdlib]
    parallel(lambda item: compile_one(item, tc, flags), sources, jobs)
    build_archive(package + stdlib, tc)
    census = diagnostic_census(package + stdlib)
    print(f"[5/8] compiled {len(sources)} modules and archived {ARCHIVE.relative_to(REPO)}; "
          "diagnostics: " + ", ".join(f"{n} {name} (generator shape)" for name, n in census.items())
          + ", nothing else")
    units = nm(ARCHIVE)
    unresolved = check_archive_symbols(units, len(closure))
    host = {}
    for lib in ("libInit.a", "libStd.a"):
        host.update(nm(Path(tc["prefix"]) / "lib/lean" / lib))
    stdlib_inits = {init for init, unit in unit_initializers(units).items()
                    if module_family(member_module(unit), STDLIB_PREFIXES)}
    if len(stdlib_inits) != len(stdlib):
        raise Refused(f"{len(stdlib_inits)} stdlib initializers for {len(stdlib)} stdlib modules")
    check_stdlib_fidelity(units, host, stdlib_inits)
    prefix = Path(tc["prefix"])
    classes = classify_unresolved(
        unresolved,
        runtime=defined_symbols(prefix / "lib/lean/libleanrt.a"),
        builtins=defined_symbols(rust_target_builtins()),
        hal=extern_symbols([REPO / (m.replace(".", "/") + ".lean") for m in package]),
        stdlib_externs=extern_symbols(
            [prefix / "src/lean" / (m.replace(".", "/") + ".lean") for m in stdlib]),
    )
    write_unresolved_report(classes)
    print(f"[6/8] symbols: one initializer per module, all resolved, no duplicate definition, "
          f"small allocator; {len(stdlib)} stdlib modules match the toolchain's objects; "
          f"{len(unresolved)} unresolved, every one attributed ("
          + ", ".join(f"{len(v)} {k}" for k, v in classes.items())
          + f") -> {UNRESOLVED_REPORT.relative_to(REPO)}")
    rlib = hal_rlib()
    hal_text = global_text(run([fp_gate.rust_llvm_tool("llvm-nm"), "-g", "-P", str(rlib)]).stdout)
    check_hal_providers(classes, hal_text)
    print(f"[7/8] providers: the HAL's {RUST_TARGET} object code defines every allocator and hal "
          f"symbol ({len(classes['allocator'])} + {len(classes['hal'])}) and the whole "
          f"small-allocator API as functions")
    status = fp_gate.check([ARCHIVE], fp_gate.default_objdump())
    print("[8/8] FP/SIMD register operands: " + ("none" if status == 0 else "FOUND"))
    return status


# ---------------------------------------------------------------------------
# Self-test
# ---------------------------------------------------------------------------

_TC_CONFIG = "#pragma once\n#include <lean/version.h>\n\n#define LEAN_MIMALLOC\n\n\n#define LEAN_IS_STAGE0 0\n"
_SHIM_CONFIG = "/* c */\n#pragma once\n#include <lean/version.h>\n#define LEAN_SMALL_ALLOCATOR\n#define LEAN_IS_STAGE0 0\n"


def _refused(fn, *args) -> bool:
    try:
        fn(*args)
    except Refused:
        return True
    return False


def _units(**objs: tuple[list[str], list[str]]) -> Symbols:
    return {f"lib.a[{name}.o]": (set(d), set(u)) for name, (d, u) in objs.items()}


def self_test() -> int:
    failures: list[str] = []
    checks = 0

    def expect(label: str, ok: bool) -> None:
        nonlocal checks
        checks += 1
        if not ok:
            failures.append(label)

    lake = ["SeLe4n", "SeLe4n.A"]
    good = ["Init.Prelude", "Std.Data.HashMap", "SeLe4n", "SeLe4n.A"]
    expect("a clean closure classifies",
           classify_closure(good, lake, {"SeLe4n.S"}) == (["SeLe4n", "SeLe4n.A"],
                                                         ["Init.Prelude", "Std.Data.HashMap"]))
    for label, closure, lake_mods in [
        ("the elaborator in the image", good + ["Lean.Elab"], lake),
        ("a package module Lake does not list", good + ["SeLe4n.B"], lake),
        ("a Lake module the elaborator does not reach", good, lake + ["SeLe4n.B"]),
        ("a staged module", good + ["SeLe4n.S"], lake + ["SeLe4n.S"]),
        ("a testing module", good + ["SeLe4n.Testing.X"], lake + ["SeLe4n.Testing.X"]),
        ("a module reported twice", good + ["Init.Prelude"], lake),
        ("no root", good[:2] + ["SeLe4n.A"], ["SeLe4n.A"]),
        ("a prefix that only resembles the package", good + ["SeLe4nX.A"], lake),
    ]:
        expect(f"closure refused: {label}", _refused(classify_closure, closure, lake_mods, {"SeLe4n.S"}))

    expect("the shim relation holds", not _refused(check_config, _TC_CONFIG, _SHIM_CONFIG))
    for label, tc_text, shim_text in [
        ("shim keeps mimalloc", _TC_CONFIG, _SHIM_CONFIG + "#define LEAN_MIMALLOC\n"),
        ("shim drops the small allocator", _TC_CONFIG, _SHIM_CONFIG.replace("#define LEAN_SMALL_ALLOCATOR\n", "")),
        ("shim changes a kept value", _TC_CONFIG, _SHIM_CONFIG.replace("STAGE0 0", "STAGE0 1")),
        ("shim drops the version include", _TC_CONFIG, _SHIM_CONFIG.replace("#include <lean/version.h>\n", "")),
        ("toolchain adds an unclassified macro", _TC_CONFIG + "#define LEAN_NEW 1\n", _SHIM_CONFIG),
        ("toolchain drops a classified macro", _TC_CONFIG.replace("#define LEAN_IS_STAGE0 0\n", ""), _SHIM_CONFIG),
        ("shim carries a conditional", _TC_CONFIG, _SHIM_CONFIG + "#ifdef X\n#endif\n"),
        ("a macro defined twice", _TC_CONFIG, _SHIM_CONFIG + "#define LEAN_IS_STAGE0 0\n"),
    ]:
        expect(f"config refused: {label}", _refused(check_config, tc_text, shim_text))
    expect("a define hidden in a comment is not a define",
           config_items("/* #define LEAN_MIMALLOC */\n// #define X\n")[0] == {})

    expect("module header read", header_module("// Lean compiler output\n// Module: Init.Core\n") == "Init.Core")
    expect("no header, no module", header_module("#include <lean/lean.h>\n") is None)

    parsed = parse_nm("A.o:\ninitialize_A T 0 10\nlean_alloc_small U 0 0\n\n"
                      "B.o:\ninitialize_B T 0 4\ninitialize_A U 0 0\n", "lib.a")
    expect("nm parsed per member", parsed == {"lib.a[A.o]#1": ({"initialize_A"}, {"lean_alloc_small"}),
                                              "lib.a[B.o]#2": ({"initialize_B"}, {"initialize_A"})})
    same_name = parse_nm("Grind.o:\ninitialize_Init_Grind T 0 1\n\n"
                         "Grind.o:\ninitialize_Init_Data_String_Grind T 0 1\n", "libInit.a")
    expect("two members with one name stay two units",
           len(same_name) == 2 and len(unit_initializers(same_name)) == 2)
    expect("a lone object is its own unit",
           parse_nm("initialize_A T 0 1\n", "A.o") == {"A.o": ({"initialize_A"}, set())})
    expect("an unreadable nm line refused", _refused(parse_nm, "garbage\n", "x"))
    expect("our member names are modules", member_module("lib.a[Init.Data.List.Basic.o]#3") == "Init.Data.List.Basic")

    base = dict(A=(["initialize_A", "f"], ["lean_alloc_small"]), B=(["initialize_B"], ["initialize_A", "f"]))
    expect("a sound archive passes, unresolved derived",
           check_archive_symbols(_units(**base), 2) == {"lean_alloc_small"})
    for label, units, count in [
        ("a missing module", _units(**base), 3),
        ("an initializer referenced and not defined",
         _units(A=base["A"], B=(["initialize_B"], ["initialize_C"])), 2),
        ("an object with no initializer", _units(A=base["A"], B=(["g"], [])), 2),
        ("an object with two initializers", _units(A=base["A"], B=(["initialize_B", "initialize_C"], [])), 2),
        ("a symbol defined twice", _units(A=base["A"], B=(["initialize_B", "f"], [])), 2),
        ("no small-allocator call", _units(A=(["initialize_A"], []), B=(["initialize_B"], [])), 2),
        ("a mimalloc reference", _units(A=base["A"], B=(["initialize_B"], ["mi_free"])), 2),
    ]:
        expect(f"archive refused: {label}", _refused(check_archive_symbols, units, count))

    ours = _units(I=(["initialize_I", "l_x"], []), S=(["initialize_S", "l_y"], []))
    host = {"libInit.a[I.o]": ({"initialize_I", "l_x"}, set()),
            "libStd.a[S.o]": ({"initialize_S", "l_y"}, set()),
            "libStd.a[T.o]": ({"initialize_T"}, set())}
    expect("matching stdlib passes", not _refused(check_stdlib_fidelity, ours, host, {"initialize_I", "initialize_S"}))
    drift = dict(host)
    drift["libStd.a[S.o]"] = ({"initialize_S", "l_y", "l_z"}, set())
    expect("stdlib drift refused", _refused(check_stdlib_fidelity, ours, drift, {"initialize_I", "initialize_S"}))
    expect("a stdlib module the toolchain lacks refused",
           _refused(check_stdlib_fidelity, ours, {k: v for k, v in host.items() if "I.o" not in k},
                    {"initialize_I", "initialize_S"}))

    counts, other = classify_diagnostics(
        "a.c:1:2: warning: variable 'x_14' set but not used [-Wunused-but-set-variable]\n"
        "b.c:3:4: warning: unused variable 'res' [-Wunused-variable]\n"
        "2 warnings generated.\n")
    expect("the generator's two shapes are classified",
           counts == {"unused-but-set-variable": 1, "unused-variable": 1} and not other)
    for label, line in [
        ("a named variable set but not used",
         "a.c:1:2: warning: variable 'count' set but not used [-Wunused-but-set-variable]"),
        ("an unused variable other than the initializer's",
         "a.c:1:2: warning: unused variable 'x_3' [-Wunused-variable]"),
        ("any other diagnostic", "a.c:1:2: warning: implicit conversion loses precision [-Wshorten-64-to-32]"),
        ("a generator shape reported as an error",
         "a.c:1:2: error: variable 'x_1' set but not used [-Werror,-Wunused-but-set-variable]"),
        ("an unparsed diagnostic line", "fatal error: too many errors emitted"),
        ("a note", "a.c:1:2: note: declared here"),
        ("a summary that also counts errors", "1 warning and 1 error generated."),
    ]:
        expect(f"diagnostic refused: {label}", bool(classify_diagnostics(line)[1]))

    got = classify_unresolved({"lean_alloc_small", "lean_inc", "__adddf3", "ffi_x", "sin"},
                              runtime={"lean_inc"}, builtins={"__adddf3", "sin"},
                              hal={"ffi_x"}, stdlib_externs={"sin", "cosh"})
    expect("each unresolved symbol goes to its first provider",
           got == {"allocator": ["lean_alloc_small"], "runtime": ["lean_inc"],
                   "compiler-builtins": ["__adddf3", "sin"], "hal": ["ffi_x"], "stdlib-extern": []})
    expect("an unattributed symbol refused",
           _refused(classify_unresolved, {"memcpy"}, set(), set(), set(), set()))
    expect("a HAL symbol the runtime also defines refused",
           _refused(classify_unresolved, {"ffi_x"}, {"ffi_x"}, set(), {"ffi_x"}, set()))
    expect("a HAL symbol compiler_builtins also defines refused",
           _refused(classify_unresolved, {"ffi_x"}, set(), {"ffi_x"}, {"ffi_x"}, set()))

    nm_out = ("lib.rmeta:\nx.rcgu.o:\nlean_alloc_small T 0 160\nlean_free_small T 0 8\n"
              "lean_small_mem_size T 0 8\nffi_x T 0 4\nffi_data D 0 8\nffi_ref U\n")
    expect("only global text symbols are providers", global_text(nm_out) ==
           {"lean_alloc_small", "lean_free_small", "lean_small_mem_size", "ffi_x"})
    provided = global_text(nm_out)
    called = {"allocator": ["lean_alloc_small"], "hal": ["ffi_x"]}
    expect("a HAL that defines its classes passes", not _refused(check_hal_providers, called, provided))
    for label, classes, text in [
        ("a hal symbol the HAL does not define", {**called, "hal": ["ffi_x", "ffi_y"]}, provided),
        ("a hal symbol the HAL defines only as data", {**called, "hal": ["ffi_data"]}, provided),
        ("an allocator call the HAL does not define", called, provided - {"lean_alloc_small"}),
        ("an allocator entry no object calls but the runtime will", called, provided - {"lean_small_mem_size"}),
    ]:
        expect(f"providers refused: {label}", _refused(check_hal_providers, classes, text))

    expect("the probe asks the elaborator for the header's module names of the root",
           "env.header.moduleNames" in CLOSURE_PROBE_TEMPLATE
           and "module := `@ROOT@" in CLOSURE_PROBE_TEMPLATE)
    expect("the compile is soft-float and freestanding",
           {"-mgeneral-regs-only", "-mabi=aapcs-soft", "-ffreestanding", "-nostdlibinc", "-Werror"}
           <= set(compile_flags({"prefix": "/t"})))

    for failure in failures:
        print(f"FAIL self-test: {failure}")
    if failures:
        return 1
    print(f"build_lean_aarch64_archive self-test: {checks} cases passed")
    return 0


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__.splitlines()[0])
    parser.add_argument("--self-test", action="store_true")
    parser.add_argument("--jobs", type=int, default=os.cpu_count() or 1)
    args = parser.parse_args()
    if args.self_test:
        return self_test()
    try:
        return build(max(1, args.jobs))
    except (Refused, fp_gate.Unreadable) as exc:
        print(f"FAIL: {exc}")
        return 1


if __name__ == "__main__":
    sys.exit(main())
