#!/usr/bin/env python3
# seLe4n  - A Lean Microkernel
# Copyright (C) 2026  Adam Hall
# This program comes with ABSOLUTELY NO WARRANTY.
# This is free software, and you are welcome to redistribute it
# under certain conditions. See: https://github.com/hatter6822/seLe4n/blob/main/LICENSE
"""No compiled reset/reuse fills a cell with a value built for another cell.

WS-UC UC4.  A carve owns the cells it allocates, and the untyped's retire
returns exactly those cells.  The compiler can break that without any source
saying so: its reset/reuse pass hands the cell of one object to the
constructor that is built next, and when that constructor is a copy of a
*different* object (a capability copied out of a slot, a Robin Hood entry
displaced to the next bucket, a TCB whose queue links are rewritten from its
neighbour's), the cell of the first object comes to hold the second object's
fields.  The first object's owner then frees a cell that now carries another
object, and the second object's cells are no longer the ones its carve made.

**What is read.**  The C the Lean compiler generates for the production
library: the modules of `lake query SeLe4n:modules`, generated with Lake's
`:c` facet.  The functions read are the ones reachable over the C symbol graph
from the package's `@[export]`s (read from the Lean code view with the shared
attribute parser), restricted to the store, Robin Hood, retire and
capability-copy code (`SCOPE`, a pin; every Robin Hood function is in scope by
its symbol, wherever it is specialised).

**The two shapes.**  The compiler emits a reuse in exactly two shapes, and
every exclusivity test in a scanned function must be one of them; any other is
refused (fail closed):

* the slow shape: `if (lean_is_exclusive(a)) { lean_ctor_release(a, i)…;
  t = a; } else { lean_dec_ref(a); t = lean_box(0); }`, and later
  `if (lean_is_scalar(t)) { c = lean_alloc_ctor(…); } else { c = t;
  [lean_ctor_set_tag(c, …);] }` followed by the field writes into `c`;
* the in-place shape: `f = !lean_is_exclusive(a); … if (f == 0) { …
  lean_ctor_set(a, i, v)… }`.

A reuse token may be spent only on its reuse or released with `lean_dec` /
`lean_dec_ref`, and every field write must land in a cell allocated in the
function or in a reused one; anything else is refused.

**The relation.**  Each object field written into a reused cell is traced,
through aliases and `lean_ctor_get` projections, to the cells it was read
from.  A reused cell is flagged when it takes one or more fields, at their own
positions, from a cell that is not the reused cell (nor reached from it), and
that count is at least the number of fields it keeps of its own: those are the
fields of another object moved into this object's cell.  A field written in
place keeps its position; on the in-place shape the fields not written are
kept.  Scalar fields are data (register words, counters), never a cell, and
are not counted.

**Derivations fail closed.**  No module, no export, an export with no C
definition, a scope pin naming no module, or a scope with no reuse site is a
failure, never an empty pass.  `--self-test` breaks the relation on the real
tree (every slow reuse site that keeps its own fields has its projections
retargeted to another parameter, the reset and reuse tokens left in place, and
each must be flagged) and plants each refused shape in synthetic C.
"""
from __future__ import annotations

import pathlib
import re
import subprocess
import sys
from dataclasses import dataclass, field

sys.path.insert(0, str(pathlib.Path(__file__).resolve().parent))
import lean_code_view  # noqa: E402

REPO = pathlib.Path(__file__).resolve().parent.parent
IR_ROOT = REPO / ".lake" / "build" / "ir"
LIBRARY = "SeLe4n"

#: The store, Robin Hood, retire and capability-copy code (a pin: each entry
#: must name a production module, and the scope must hold reuse sites).
SCOPE = (
    "SeLe4n.Model.State",
    "SeLe4n.Kernel.RobinHood",
    "SeLe4n.Kernel.Lifecycle.Operations.CarvedObjectErase",
    "SeLe4n.Kernel.Capability.FinalRetire",
    "SeLe4n.Kernel.Capability.Operations",
    "SeLe4n.Model.Object.Types",
    "SeLe4n.Model.Object.Structures",
)
#: Every Robin Hood function is in scope wherever the compiler specialises it.
SCOPE_SYMBOL_PREFIX = "lp_seLe4n_SeLe4n_Kernel_RobinHood_"

VAR = r"x_\d+"
SCALAR_KIND = r"(?:uint8|uint16|uint32|uint64|usize|float|float32)"
HEADER = re.compile(r"^(LEAN_EXPORT|static) .*\{$")
NAME = re.compile(r"([A-Za-z0-9_]+)\(")
PARAM = re.compile(rf"\b({VAR})\b")
ASSIGN = re.compile(rf"^({VAR}) = (.+);$")
ALIAS = re.compile(rf"^({VAR}) = ({VAR});$")
ALLOC = re.compile(rf"^({VAR}) = lean_alloc_ctor\((\d+), (\d+), (.+)\);$")
SLOW_TEST = re.compile(rf"^if \(lean_is_exclusive\(({VAR})\)\) \{{$")
FAST_TEST = re.compile(rf"^({VAR}) = !lean_is_exclusive\(({VAR})\);$")
SCALAR_TEST = re.compile(rf"^if \(lean_is_scalar\(({VAR})\)\) \{{$")
RELEASE = re.compile(rf"^lean_ctor_release\(({VAR}), \d+\);$")
DEC_REF = re.compile(rf"^lean_dec_ref\(({VAR})\);$")
BOX0 = re.compile(rf"^({VAR}) = lean_box\(0\);$")
SET = re.compile(rf"^lean_ctor_set\(({VAR}), (\d+), (.+)\);$")
SSET = re.compile(rf"^lean_ctor_set_{SCALAR_KIND}\(({VAR}), (.+), (.+)\);$")
SET_TAG = re.compile(rf"^lean_ctor_set_tag\(({VAR}), \d+\);$")
WORD = re.compile(VAR)
DECL = re.compile(r"^(?:lean_object\*|uint8_t|uint16_t|uint32_t|uint64_t|size_t|double|float) x_\d+;")
FIELD_USE = re.compile(rf"lean_ctor_(?:get|set|release)\(({VAR}), (\d+)")
PROJ_RHS = re.compile(rf"lean_ctor_get\(({VAR}), (\d+)\)")
SPROJ_RHS = re.compile(rf"lean_ctor_get_{SCALAR_KIND}\(({VAR}), (.+)\)")
SYMBOL = re.compile(r"\b(?:lp_\w+|l_\w+|lean_\w+|_init_\w+|initialize_\w+)\b")


@dataclass
class Cell:
    """A cell some constructor is written into in place of an allocation."""
    var: str        # the variable its fields are written through
    origin: str     # the variable whose cell it is (the one tested exclusive)
    arity: int      # its object fields (a lower bound on the in-place shape)
    line: int       # body index of the exclusivity test or the reuse
    lo: int         # body lines over which `var` is that cell
    hi: int
    in_place: bool
    writes: list = field(default_factory=list)   # (index, value, scalar?)


@dataclass
class Function:
    name: str
    header: str
    start: int      # 1-based line of the header
    body: list


def functions(text: str) -> list[Function]:
    """Every function definition in one generated C file."""
    out: list[Function] = []
    for number, line in enumerate(text.split("\n"), 1):
        if HEADER.match(line):
            m = NAME.search(line)
            out.append(Function(m.group(1) if m else line, line, number, []))
        elif out:
            out[-1].body.append(line.strip())
    return out


def close_of(body: list[str], i: int) -> int | None:
    """The index of the `}` closing the block opened on line `i`."""
    depth, seen = 0, False
    for j in range(i, len(body)):
        depth += body[j].count("{") - body[j].count("}")
        seen = seen or "{" in body[j]
        if seen and depth <= 0:
            return j
    return None


class Scan:
    """The reuse sites of one function, and what about them is refused."""

    def __init__(self, fn: Function):
        self.fn = fn
        self.refused: list[tuple[int, str]] = []
        self.cells: list[Cell] = []
        self.defs: dict[str, list[str]] = {}
        body = fn.body
        for line in body:
            m = ASSIGN.match(line)
            if m:
                self.defs.setdefault(m.group(1), []).append(m.group(2))
        self.allocs = {m.group(1) for m in map(ALLOC.match, body) if m}
        self.field_bound: dict[str, int] = {}
        for line in body:
            for m in FIELD_USE.finditer(line):
                v, i = m.group(1), int(m.group(2))
                self.field_bound[v] = max(self.field_bound.get(v, -1), i)
        self.tokens: dict[str, str] = {}
        self.token_lines: set[int] = set()
        self._tests()
        self._token_uses()
        self._tags()
        self._writes()

    def refuse(self, i: int, why: str) -> None:
        self.refused.append((self.fn.start + 1 + i, why))

    def _tests(self) -> None:
        """Every exclusivity test is one of the compiler's two shapes."""
        body = self.fn.body
        for i, line in enumerate(body):
            if "lean_is_exclusive" not in line:
                continue
            m = SLOW_TEST.match(line)
            if m:
                self._slow_test(i, m.group(1))
                continue
            m = FAST_TEST.match(line)
            if m:
                self._fast_test(i, m.group(1), m.group(2))
                continue
            self.refuse(i, f"unclassified exclusivity test: {line!r}")

    def _slow_test(self, i: int, a: str) -> None:
        body = self.fn.body
        j, tok = i + 1, None
        while j < len(body) and body[j] != "} else {":
            r, al = RELEASE.match(body[j]), ALIAS.match(body[j])
            if r and r.group(1) == a:
                pass
            elif al and al.group(2) == a and tok is None:
                tok = al.group(1)
            else:
                self.refuse(j, f"unclassified line in the exclusive arm of {a}'s reset: {body[j]!r}")
            j += 1
        k = j + 1
        dec = DEC_REF.match(body[k]) if k < len(body) else None
        box = BOX0.match(body[k + 1]) if k + 1 < len(body) else None
        if not (tok and dec and dec.group(1) == a and box and box.group(1) == tok
                and k + 2 < len(body) and body[k + 2] == "}"):
            self.refuse(i, f"unclassified reset of {a}")
            return
        self.tokens[tok] = a
        self.token_lines.update(range(i, k + 3))

    def _fast_test(self, i: int, flag: str, a: str) -> None:
        body = self.fn.body
        opener = next((j for j in range(i + 1, len(body)) if body[j] == f"if ({flag} == 0)"), None)
        if opener is None or opener + 1 >= len(body) or body[opener + 1] != "{":
            self.refuse(i, f"unclassified in-place test of {a}")
            return
        end = close_of(body, opener + 1)
        if end is None:
            self.refuse(i, f"unclosed in-place arm of {a}")
            return
        self.cells.append(Cell(a, a, self.field_bound.get(a, -1) + 1, i, opener + 1, end, True))

    def _token_uses(self) -> None:
        """A reuse token is spent on its reuse or released, nothing else."""
        body = self.fn.body
        for i, line in enumerate(body):
            if i in self.token_lines or DECL.match(line):
                continue
            for v in sorted(set(WORD.findall(line)) & self.tokens.keys()):
                a = self.tokens[v]
                test = SCALAR_TEST.match(line)
                alias = ALIAS.match(line)
                if test and test.group(1) == v:
                    self._reuse(i, v, a)
                elif alias and alias.group(2) == v and i > 0 and body[i - 1] == "} else {":
                    continue    # the reuse arm, read by `_reuse`
                elif line in (f"lean_dec({v});", f"lean_dec_ref({v});"):
                    continue
                else:
                    self.refuse(i, f"reuse token {v} of {a}'s cell used other than by a reuse: {line!r}")

    def _reuse(self, i: int, v: str, a: str) -> None:
        body = self.fn.body
        alloc = ALLOC.match(body[i + 1]) if i + 1 < len(body) else None
        arm = ALIAS.match(body[i + 3]) if i + 3 < len(body) else None
        if not (alloc and body[i + 2] == "} else {" and arm and arm.group(2) == v
                and arm.group(1) == alloc.group(1)):
            self.refuse(i, f"unclassified reuse of {a}'s cell")
            return
        c = alloc.group(1)
        end = i + 4 if i + 4 < len(body) and SET_TAG.match(body[i + 4]) else i + 3
        if end + 1 >= len(body) or body[end + 1] != "}":
            self.refuse(i, f"unclassified reuse of {a}'s cell")
            return
        hi = end + 2    # the fields are written in the straight run after it
        while hi < len(body) and body[hi].startswith("lean_ctor_set") \
                and not SET_TAG.match(body[hi]) and WORD.findall(body[hi])[:1] == [c]:
            hi += 1
        self.cells.append(Cell(c, a, int(alloc.group(3)), i, end + 2, hi, False))

    def _tags(self) -> None:
        """A tag is rewritten only on a reused cell, as the reuse does it."""
        for i, line in enumerate(self.fn.body):
            m = SET_TAG.match(line)
            if m and not any(c.var == m.group(1) and (c.line < i <= c.lo + 2 or
                                                      (c.in_place and c.lo <= i <= c.hi))
                             for c in self.cells):
                self.refuse(i, f"tag rewritten on a cell no reset names: {line!r}")

    def _writes(self) -> None:
        """Every field write lands in a fresh cell or a reused one."""
        for i, line in enumerate(self.fn.body):
            if not line.startswith("lean_ctor_set") or SET_TAG.match(line):
                continue
            m = SET.match(line) or SSET.match(line)
            if m is None:
                self.refuse(i, f"unclassified field write: {line!r}")
                continue
            target, scalar = m.group(1), SSET.match(line) is not None
            cell = next((c for c in self.cells if c.var == target
                         and (c.lo <= i <= c.hi if c.in_place else c.lo <= i)), None)
            if cell is not None:
                cell.writes.append((m.group(2), m.group(3), scalar))
            elif target in self.allocs:
                continue
            else:
                self.refuse(i, f"field write into a cell neither allocated nor reused here: {line!r}")


class Provenance:
    """Where a function's variables take their values from, memoised."""

    def __init__(self, defs: dict[str, list[str]]):
        self.defs = defs
        self._resolve: dict[str, frozenset] = {}
        self._proj: dict[str, frozenset] = {}
        self._roots: dict[str, frozenset] = {}

    def resolve(self, v: str) -> frozenset:
        """`v` and every variable it is an alias of."""
        if v not in self._resolve:
            out, todo = set(), [v]
            while todo:
                u = todo.pop()
                if u not in out:
                    out.add(u)
                    todo += [d for d in self.defs.get(u, []) if re.fullmatch(VAR, d)]
            self._resolve[v] = frozenset(out)
        return self._resolve[v]

    def projections(self, v: str) -> frozenset:
        """The (cell, index) pairs `v` is a field read of."""
        if v not in self._proj:
            out = set()
            for u in self.resolve(v):
                for d in self.defs.get(u, []):
                    m = PROJ_RHS.fullmatch(d) or SPROJ_RHS.fullmatch(d)
                    if m:
                        out.add((m.group(1), m.group(2)))
            self._proj[v] = frozenset(out)
        return self._proj[v]

    def roots(self, v: str) -> frozenset:
        """Every variable `v` is read out of, through aliases and fields."""
        if v not in self._roots:
            out, todo = set(), [v]
            while todo:
                u = todo.pop()
                if u in out:
                    continue
                out.add(u)
                todo += [r for r in self.resolve(u) if r not in out]
                todo += [w for w, _ in self.projections(u) if w not in out]
            self._roots[v] = frozenset(out)
        return self._roots[v]


def judge(scan: Scan) -> list[tuple[int, str]]:
    """A finding for each reused cell filled with another cell's fields."""
    out: list[tuple[int, str]] = []
    pv = Provenance(scan.defs)
    moved = {c.var: c for c in scan.cells if not c.in_place}
    for c in scan.cells:
        kept, other, written = 0, {}, set()
        for idx, v, scalar in c.writes:
            if scalar:
                continue    # a scalar field holds data, never another cell
            written.add(idx)
            sources = set(pv.projections(v))
            for u in pv.resolve(v):
                if u in moved and moved[u] is not c:
                    sources |= pv.projections(moved[u].origin)
            for w, j in sources:
                if c.origin in pv.roots(w):
                    if j == idx and c.origin in pv.resolve(w):
                        kept += 1
                elif j == idx:
                    other[w] = other.get(w, 0) + 1
        if c.in_place:
            kept += max(c.arity - len(written), 0)
        if other:
            w, n = max(sorted(other.items()), key=lambda kv: kv[1])
            if n >= kept:
                out.append((scan.fn.start + 1 + c.line,
                            f"{c.var} (the cell of {c.origin}) takes {n} field(s) from {w} "
                            f"at their own positions and keeps {kept} of its own"))
    return out


class Refused(Exception):
    """A derivation that came back empty or inconsistent."""


def production_modules() -> list[str]:
    out = subprocess.run(["lake", "query", f"{LIBRARY}:modules"], cwd=REPO,
                         capture_output=True, text=True)
    if out.returncode != 0:
        raise Refused(f"`lake query {LIBRARY}:modules` failed: {out.stderr.strip()}")
    modules = [line.strip() for line in out.stdout.splitlines() if line.strip()]
    if not modules:
        raise Refused(f"`lake query {LIBRARY}:modules` named no module")
    return modules


def module_source(module: str) -> pathlib.Path:
    return REPO / (module.replace(".", "/") + ".lean")


def module_c(module: str) -> pathlib.Path:
    return IR_ROOT / (module.replace(".", "/") + ".c")


def export_roots(modules: list[str]) -> list[str]:
    roots: list[str] = []
    for module in modules:
        view = lean_code_view.code_no_strings(module_source(module).read_text())
        roots += lean_code_view.attribute_arguments(view, "export")
    if not roots:
        raise Refused("no `@[export]` in the production modules: nothing roots the reach")
    return roots


def in_scope(module: str) -> bool:
    return any(module == p or module.startswith(p + ".") for p in SCOPE)


def reach(index: dict[str, tuple[str, Function]], roots: list[str]) -> set[str]:
    """Every function reachable from `roots` over the C symbol graph."""
    seen: set[str] = set()
    todo = list(roots)
    while todo:
        s = todo.pop()
        if s in seen:
            continue
        seen.add(s)
        for line in index[s][1].body:
            for t in SYMBOL.findall(line):
                if t in index and t not in seen:
                    todo.append(t)
                init = "_init_" + t
                if "_closed__" in t and init in index and init not in seen:
                    todo.append(init)
    return seen


def scoped_functions(modules: list[str]) -> list[tuple[str, Function]]:
    """(module, function) for every scanned function: reached from an export
    and in the scope."""
    missing_pins = [p for p in SCOPE if not any(m == p or m.startswith(p + ".") for m in modules)]
    if missing_pins:
        raise Refused(f"scope pins naming no production module: {missing_pins}")
    index: dict[str, tuple[str, Function]] = {}
    for module in modules:
        path = module_c(module)
        if not path.is_file():
            raise Refused(f"{module}: generated C not found at {path.relative_to(REPO)}")
        for fn in functions(path.read_text()):
            index.setdefault(fn.name, (module, fn))
    roots = export_roots(modules)
    absent = [r for r in roots if r not in index]
    if absent:
        raise Refused(f"exports with no C definition: {absent}")
    return [index[s] for s in sorted(reach(index, roots))
            if in_scope(index[s][0]) or s.startswith(SCOPE_SYMBOL_PREFIX)]


def report(module: str, fn: Function) -> tuple[int, list[str]]:
    """(reuse sites, failure lines) for one function."""
    scan = Scan(fn)
    where = module.replace(".", "/") + ".c"
    lines = [f"{where}:{n}: {fn.name}: refused: {why}" for n, why in scan.refused]
    lines += [f"{where}:{n}: {fn.name}: {why}" for n, why in judge(scan)]
    return len(scan.cells), lines


# ---------------------------------------------------------------------------
# Self-test
# ---------------------------------------------------------------------------

SYNTHETIC_HEADER = "LEAN_EXPORT lean_object* lp_probe(lean_object* x_1, lean_object* x_2) {"
#: A reset of x_1 and a reuse of its cell for a two-field constructor, whose
#: fields are read from @SRC@ (x_1 itself: the cell keeps its own fields).
SLOW_TEMPLATE = """x_3 = lean_ctor_get(@SRC@, 0);
lean_inc(x_3);
x_4 = lean_ctor_get(@SRC@, 1);
lean_inc(x_4);
if (lean_is_exclusive(x_1)) {
 lean_ctor_release(x_1, 0);
 lean_ctor_release(x_1, 1);
 x_5 = x_1;
} else {
 lean_dec_ref(x_1);
 x_5 = lean_box(0);
}
@EXTRA@
if (lean_is_scalar(x_5)) {
 x_6 = lean_alloc_ctor(0, 2, 0);
} else {
 x_6 = x_5;
}
lean_ctor_set(x_6, 0, x_3);
@WRITE@
return x_6;"""
#: An in-place update of x_1, field 0 written from @SRC@'s field 0.
FAST_TEMPLATE = """x_3 = !lean_is_exclusive(x_1);
if (x_3 == 0)
{
x_4 = lean_ctor_get(@SRC@, 0);
lean_inc(x_4);
@WRITE@
return x_1;
}
else
{
return x_2;
}"""


def synthetic(template: str, **subst: str) -> Function:
    text = template
    for key, value in {"SRC": "x_1", "EXTRA": "", "WRITE": "", **subst}.items():
        text = text.replace(f"@{key}@", value)
    body = ["_start:", "{"] + [l.strip() for l in text.split("\n")] + ["}"]
    return Function("lp_probe", SYNTHETIC_HEADER, 1, body)


def synthetic_cases() -> list[tuple[str, Function, str]]:
    """(name, function, expected) where expected is clean / finding / refused."""
    slow_write = "lean_ctor_set(x_6, 1, x_4);"
    fast_write = "lean_ctor_set(x_1, 0, x_4);"
    return [
        ("slow reuse keeping its own fields", synthetic(SLOW_TEMPLATE, WRITE=slow_write), "clean"),
        ("slow reuse filled from another cell (tokens kept)",
         synthetic(SLOW_TEMPLATE, SRC="x_2", WRITE=slow_write), "finding"),
        ("in-place write of its own field", synthetic(FAST_TEMPLATE, WRITE=fast_write), "clean"),
        ("in-place write of another cell's field (tokens kept)",
         synthetic(FAST_TEMPLATE, SRC="x_2", WRITE=fast_write), "finding"),
        ("in-place scalar word copied from another cell",
         synthetic(FAST_TEMPLATE.replace("lean_ctor_get(@SRC@, 0)", "lean_ctor_get_uint64(@SRC@, sizeof(void*)*1)"),
                   SRC="x_2", WRITE="lean_ctor_set_uint64(x_1, sizeof(void*)*1, x_4);"), "clean"),
        ("an exclusivity test of another shape",
         synthetic(SLOW_TEMPLATE.replace("if (lean_is_exclusive(x_1)) {", "if (lean_is_exclusive(x_1) && x_2) {"),
                   WRITE=slow_write), "refused"),
        ("a reuse token passed to a call",
         synthetic(SLOW_TEMPLATE, EXTRA="x_7 = lp_keep(x_5);", WRITE=slow_write), "refused"),
        ("a field written into a cell no reset names",
         synthetic(SLOW_TEMPLATE, WRITE="lean_ctor_set(x_2, 1, x_4);"), "refused"),
        ("a field write of an unread form",
         synthetic(SLOW_TEMPLATE, WRITE="lean_ctor_set_widget(x_6, 1, x_4);"), "refused"),
        ("an exclusive arm doing more than releasing",
         synthetic(SLOW_TEMPLATE.replace(" x_5 = x_1;", " lean_inc(x_3);\n x_5 = x_1;"),
                   WRITE=slow_write), "refused"),
    ]


def verdict(fn: Function) -> str:
    scan = Scan(fn)
    if scan.refused:
        return "refused"
    return "finding" if judge(scan) else "clean"


def params(fn: Function) -> list[str]:
    head = fn.header[fn.header.index("("):]
    return PARAM.findall(head)


def retargeted(fn: Function, cell: Cell, scan: Scan) -> Function | None:
    """`fn` with every field read of `cell`'s own cell redirected to another
    parameter — the reset, the reuse and every write left as they were."""
    pv = Provenance(scan.defs)
    others = [p for p in params(fn)
              if p not in pv.roots(cell.origin) and cell.origin not in pv.roots(p)]
    if not others:
        return None
    own = pv.resolve(cell.origin)
    body = list(fn.body)
    for i, line in enumerate(body):
        for v in own:
            line = line.replace(f"lean_ctor_get({v}, ", f"lean_ctor_get({others[0]}, ")
        body[i] = line
    return Function(fn.name, fn.header, fn.start, body)


def keeps_own_fields(cell: Cell, scan: Scan) -> bool:
    pv = Provenance(scan.defs)
    own = pv.resolve(cell.origin)
    return any((w, idx) in pv.projections(v) and not scalar
               for idx, v, scalar in cell.writes for w in own)


def with_token_leak(fn: Function, scan: Scan) -> Function | None:
    """`fn` with its first reuse token also handed to a call."""
    for tok in scan.tokens:
        j = max(i for i in scan.token_lines if tok in fn.body[i])
        body = fn.body[:j + 1] + [f"x_0 = lp_keep({tok});"] + fn.body[j + 1:]
        return Function(fn.name, fn.header, fn.start, body)
    return None


def self_test() -> int:
    failures: list[str] = []
    for name, fn, expected in synthetic_cases():
        got = verdict(fn)
        if got != expected:
            failures.append(f"synthetic case {name!r}: expected {expected}, got {got}")
    try:
        scoped = scoped_functions(production_modules())
    except Refused as e:
        print(f"FAIL: {e}", file=sys.stderr)
        return 1
    retargets = leaks = 0
    for module, fn in scoped:
        scan = Scan(fn)
        if scan.refused or judge(scan):
            continue    # the tree run reports these
        for k, cell in enumerate(scan.cells):
            if cell.in_place or not keeps_own_fields(cell, scan):
                continue
            broken = retargeted(fn, cell, scan)
            if broken is None:
                continue
            retargets += 1
            line = fn.start + 1 + cell.line
            if not any(n == line for n, _ in judge(Scan(broken))):
                failures.append(f"{module}: {fn.name}: the reuse at C line {line}, "
                                "refilled from another cell, was not flagged")
        leaky = with_token_leak(fn, scan)
        if leaky is not None:
            leaks += 1
            if not Scan(leaky).refused:
                failures.append(f"{module}: {fn.name}: a reuse token handed to a call was not refused")
    if retargets == 0 or leaks == 0:
        failures.append(f"the tree offered {retargets} reuse sites to retarget and {leaks} tokens "
                        "to leak: a self-test over nothing tests nothing")
    for f in failures:
        print(f"FAIL: {f}", file=sys.stderr)
    if not failures:
        print(f"cell reuse ownership self-test: {len(synthetic_cases())} synthetic cases, "
              f"{retargets} real reuse sites retargeted and flagged, "
              f"{leaks} real reuse tokens leaked and refused")
    return 1 if failures else 0


def generate_c(modules: list[str]) -> None:
    out = subprocess.run(["lake", "build", *(f"+{m}:c" for m in modules)], cwd=REPO,
                         capture_output=True, text=True)
    if out.returncode != 0:
        raise Refused(f"lake could not generate the production C (exit {out.returncode}):\n"
                      + out.stdout[-2000:] + out.stderr[-2000:])


def main(argv: list[str]) -> int:
    try:
        modules = production_modules()
        generate_c(modules)
        if "--self-test" in argv:
            return self_test()
        scoped = scoped_functions(modules)
    except Refused as e:
        print(f"FAIL: {e}", file=sys.stderr)
        return 1
    sites, failures = 0, []
    for module, fn in scoped:
        n, lines = report(module, fn)
        sites += n
        failures += lines
    if sites == 0:
        failures.append(f"{len(scoped)} scoped functions hold no reuse site: a scan over nothing")
    for f in failures:
        print(f"FAIL: {f}", file=sys.stderr)
    if not failures:
        print(f"cell reuse ownership: {sites} reuse sites in {len(scoped)} reached functions, "
              "none fills a cell with another cell's fields")
    return 1 if failures else 0


if __name__ == "__main__":
    sys.exit(main(sys.argv[1:]))
