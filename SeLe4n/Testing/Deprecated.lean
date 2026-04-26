-- SPDX-License-Identifier: GPL-3.0-or-later
/-
  seLe4n  - A Lean Microkernel
  Copyright (C) 2026  Adam Hall
  This program comes with ABSOLUTELY NO WARRANTY.
  This is free software, and you are welcome to redistribute it
  under certain conditions. See: https://github.com/hatter6822/seLe4n/blob/main/LICENSE
-/

import SeLe4n.Platform.Boot

/-!
# AN7-D.1 (PLT-M01) — Testing.Deprecated namespace

Test-only aliases for API surface that is deprecated in production but
retained for negative-state / legacy-path coverage.  Production code MUST
NOT import this module — the `SeLe4n.Testing.Deprecated` namespace exists
precisely so that accidental adoption of the unchecked form through a bare
`open SeLe4n.Platform.Boot` is not possible.

Every alias here wraps a `@[deprecated]` production symbol.  Its presence
here is the ONE sanctioned audit-trail location; every call site that
imports this module is a conscious opt-in to the legacy semantics.
-/

namespace SeLe4n.Testing.Deprecated

set_option linter.deprecated false in
/-- AN7-D.1 (PLT-M01) — test-only alias for `SeLe4n.Platform.Boot.bootFromPlatform`.
    Mirrors the previously-named `bootFromPlatformUnchecked` in the production
    Platform namespace, now relocated here so production adopters cannot
    reach the unchecked variant by its bare name.

    The production namespace still exports `bootFromPlatformUnchecked` as a
    deprecated alias for backward compatibility; new test code should use
    this namespaced form. -/
abbrev bootFromPlatformUnchecked := SeLe4n.Platform.Boot.bootFromPlatform

end SeLe4n.Testing.Deprecated
