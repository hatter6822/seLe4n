-- SPDX-License-Identifier: GPL-3.0-or-later
/-
  seLe4n  - A Lean Microkernel
  Copyright (C) 2026  Adam Hall
  This program comes with ABSOLUTELY NO WARRANTY.
  This is free software, and you are welcome to redistribute it
  under certain conditions. See: https://github.com/hatter6822/seLe4n/blob/main/LICENSE
-/

import SeLe4n.Platform.Sim.Contract
import SeLe4n.Platform.FFI
import SeLe4n.Platform.RPi5.Contract
import SeLe4n.Platform.RPi5.VSpaceBoot
import SeLe4n.Kernel.Architecture.CacheModel
import SeLe4n.Kernel.Architecture.ExceptionModel
import SeLe4n.Kernel.Architecture.TimerModel
-- AN9-C / AN9-A / AN9-B: hardware-binding closure modules
import SeLe4n.Kernel.Architecture.BarrierComposition
import SeLe4n.Kernel.Architecture.TlbCacheComposition
-- AN12-B (Theme 4.4): SMP-latent single-core assumption inventory
import SeLe4n.Kernel.Concurrency.Assumptions

/-!
# AN7-D.6 (PLT-M07) — Staged-modules build graph

This meta-module pulls seven platform-binding-adjacent modules into the
dependency graph so that `lake build SeLe4n.Platform.Staged` (and, via
`scripts/test_tier1_build.sh`, every CI run) forces each one to compile.
Without this wiring, the seven modules are orphans — they are not reached
from `Main.lean` or from any production kernel chain, so a regression that
breaks them would go undetected until the H3 hardware-binding workstream
reaches them.

The staged modules are:

1. `SeLe4n.Platform.Sim.Contract`              — Sim platform contract
2. `SeLe4n.Platform.FFI`                       — Lean @[extern] FFI declarations
3. `SeLe4n.Platform.RPi5.Contract`             — RPi5 platform contract
4. `SeLe4n.Platform.RPi5.VSpaceBoot`           — AN7-D.2 RPi5 boot VSpaceRoot
5. `SeLe4n.Kernel.Architecture.CacheModel`     — Cache coherency model
6. `SeLe4n.Kernel.Architecture.ExceptionModel` — ARM64 exception model
7. `SeLe4n.Kernel.Architecture.TimerModel`     — ARM generic timer model
8. `SeLe4n.Kernel.Architecture.BarrierComposition` — AN9-C BarrierKind algebra
9. `SeLe4n.Kernel.Architecture.TlbCacheComposition` — AN9-A page-table coherency
10. `SeLe4n.Kernel.Concurrency.Assumptions`    — AN12-B SMP-latent inventory

Per the plan (AN9-J will transition most of these from "SMP-latent" to
"SMP-implemented, runtime-gated by smp_enabled=false at v1.0.0"), the
module remains present as a confirmation inventory rather than a
pending-work surface.  See `docs/spec/SELE4N_SPEC.md` §8.15 for the
activation roadmap.

Every imported module carries its own
`-- STATUS: staged for H3 hardware binding` header comment at the top of
its file (PLT-M07 requirement); this module plus the CI hygiene check
guarantees they all continue to compile.
-/

namespace SeLe4n.Platform.Staged

/-- AN7-D.6 anchor: a dummy definition whose mere presence forces Lean to
    link the seven imported modules into this compilation unit.  `lake
    build SeLe4n.Platform.Staged` will fail loudly if any of those modules
    acquires a broken proof. -/
def stagedBuildAnchor : Unit := ()

end SeLe4n.Platform.Staged
