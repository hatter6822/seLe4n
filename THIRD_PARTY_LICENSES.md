# Third-Party Licenses and Attributions

The seLe4n microkernel itself (the Lean proofs, Rust kernel sources, assembly,
tests, scripts, and documentation authored in this repository) is distributed
under the GNU General Public License v3.0 or later (GPLv3+), as stated in
[`LICENSE`](./LICENSE) and in the SPDX headers on each source file.

During the **build** of the kernel's Rust workspace, a small number of
external crates are fetched from [crates.io](https://crates.io/) by Cargo and
used to assemble the ARM64 boot-time assembly (`boot.S`, `vectors.S`,
`trap.S`). These crates' source code is **not linked into the final kernel
binary** — they only run during `cargo build` on the host that produces the
kernel image — but they are still dependencies of the build graph. This file
provides the attribution those crates require under their MIT and Apache-2.0
license terms, per:

- **MIT**: "The above copyright notice and this permission notice shall be
  included in all copies or substantial portions of the Software."
- **Apache-2.0 § 4(c)**: "You must retain, in the Source form of any
  Derivative Works that You distribute, all copyright, patent, trademark,
  and attribution notices from the Source form of the Work ..."

License compatibility note: both MIT and Apache-2.0 are GPL-3.0-compatible
per the Free Software Foundation. The combined distribution is governed by
GPLv3+; the notices below preserve the attribution obligations on the
original upstream components as required by their respective licenses.

---

## Build Dependencies

These crates appear only in the **build-time** dependency tree of
`sele4n-hal/build.rs`; they are not linked into the runtime kernel. All
three are dual-licensed `MIT OR Apache-2.0`, and seLe4n consumes them under
the MIT option (terms reproduced below). The Apache-2.0 text for each is
available in its upstream repository (linked per-crate) under
`LICENSE-APACHE`.

### 1. `cc`

- **Version used:** 1.2.59
- **SPDX license:** `MIT OR Apache-2.0`
- **Upstream repository:** <https://github.com/rust-lang/cc-rs>
- **Homepage:** <https://github.com/rust-lang/cc-rs>
- **Role in seLe4n:** Invoked from `rust/sele4n-hal/build.rs` to assemble
  the ARM64 boot-time assembly files.

**MIT license text (verbatim from the upstream `LICENSE-MIT`):**

```
Copyright (c) 2014 Alex Crichton

Permission is hereby granted, free of charge, to any
person obtaining a copy of this software and associated
documentation files (the "Software"), to deal in the
Software without restriction, including without
limitation the rights to use, copy, modify, merge,
publish, distribute, sublicense, and/or sell copies of
the Software, and to permit persons to whom the Software
is furnished to do so, subject to the following
conditions:

The above copyright notice and this permission notice
shall be included in all copies or substantial portions
of the Software.

THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF
ANY KIND, EXPRESS OR IMPLIED, INCLUDING BUT NOT LIMITED
TO THE WARRANTIES OF MERCHANTABILITY, FITNESS FOR A
PARTICULAR PURPOSE AND NONINFRINGEMENT. IN NO EVENT
SHALL THE AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY
CLAIM, DAMAGES OR OTHER LIABILITY, WHETHER IN AN ACTION
OF CONTRACT, TORT OR OTHERWISE, ARISING FROM, OUT OF OR
IN CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER
DEALINGS IN THE SOFTWARE.
```

---

### 2. `find-msvc-tools`

- **Version used:** 0.1.9
- **SPDX license:** `MIT OR Apache-2.0`
- **Upstream repository:** <https://github.com/rust-lang/cc-rs>
  (published separately from `cc` as an internal library crate)
- **Role in seLe4n:** Transitive dependency of `cc`. Used only on Windows
  hosts to locate the MSVC toolchain; inactive on the Linux/macOS build
  hosts that seLe4n targets, but included in the build graph on every
  platform because Cargo resolves dependencies eagerly. Published under the
  same copyright as `cc`.

**MIT license text (verbatim from the upstream `LICENSE-MIT`):**

```
Copyright (c) 2014 Alex Crichton

Permission is hereby granted, free of charge, to any
person obtaining a copy of this software and associated
documentation files (the "Software"), to deal in the
Software without restriction, including without
limitation the rights to use, copy, modify, merge,
publish, distribute, sublicense, and/or sell copies of
the Software, and to permit persons to whom the Software
is furnished to do so, subject to the following
conditions:

The above copyright notice and this permission notice
shall be included in all copies or substantial portions
of the Software.

THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF
ANY KIND, EXPRESS OR IMPLIED, INCLUDING BUT NOT LIMITED
TO THE WARRANTIES OF MERCHANTABILITY, FITNESS FOR A
PARTICULAR PURPOSE AND NONINFRINGEMENT. IN NO EVENT
SHALL THE AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY
CLAIM, DAMAGES OR OTHER LIABILITY, WHETHER IN AN ACTION
OF CONTRACT, TORT OR OTHERWISE, ARISING FROM, OUT OF OR
IN CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER
DEALINGS IN THE SOFTWARE.
```

---

### 3. `shlex`

- **Version used:** 1.3.0
- **SPDX license:** `MIT OR Apache-2.0`
- **Upstream repository:** <https://github.com/comex/rust-shlex>
- **Role in seLe4n:** Transitive dependency of `cc` — parses compiler flag
  lists in a POSIX-shell-like manner during assembly invocation. The 1.3.0
  release incorporates the fix for RUSTSEC-2024-0006.
- **Contributors** (from upstream `Cargo.toml`):
  - comex `<comexk@gmail.com>`
  - Fenhl `<fenhl@fenhl.net>`
  - Adrian Taylor `<adetaylor@chromium.org>`
  - Alex Touchet `<alextouchet@outlook.com>`
  - Daniel Parks `<dp+git@oxidized.org>`
  - Garrett Berg `<googberg@gmail.com>`

**MIT license text (verbatim from the upstream `LICENSE-MIT`):**

```
The MIT License (MIT)

Copyright (c) 2015 Nicholas Allegra (comex).

Permission is hereby granted, free of charge, to any person obtaining a copy
of this software and associated documentation files (the "Software"), to deal
in the Software without restriction, including without limitation the rights
to use, copy, modify, merge, publish, distribute, sublicense, and/or sell
copies of the Software, and to permit persons to whom the Software is
furnished to do so, subject to the following conditions:

The above copyright notice and this permission notice shall be included in
all copies or substantial portions of the Software.

THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR
IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY,
FITNESS FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT. IN NO EVENT SHALL THE
AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER
LIABILITY, WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING FROM,
OUT OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS IN
THE SOFTWARE.
```

---

## Runtime Dependencies

**None.** The seLe4n Rust kernel crates (`sele4n-types`, `sele4n-abi`,
`sele4n-sys`, `sele4n-hal`) declare `#![no_std]` and pull no external crates
at runtime. Every line of code linked into the final kernel binary is
authored by the seLe4n project and governed by the top-level GPLv3+ license.

All ARM64 hardware access in the HAL uses `core::ptr::{read_volatile,
write_volatile}` from the Rust standard library directly, rather than any
third-party MMIO crate, to minimize the runtime attack surface.

---

## Apache-2.0 NOTICE-file propagation

Apache-2.0 § 4(d) requires propagation of any upstream `NOTICE` file. As of
the versions listed above, none of `cc` 1.2.59, `find-msvc-tools` 0.1.9, or
`shlex` 1.3.0 ship a `NOTICE` file upstream, so no additional
attribution text is required by that clause. If a future version of any of
these crates adds a `NOTICE` file, the relevant excerpt must be added here
in the same release that bumps the dependency version.

---

## Verifying this attribution

To re-verify the attribution text against the crates in your local Cargo
cache:

```bash
cd rust
cargo fetch
ls ~/.cargo/registry/src/*/cc-1.2.59/LICENSE-MIT
ls ~/.cargo/registry/src/*/find-msvc-tools-0.1.9/LICENSE-MIT
ls ~/.cargo/registry/src/*/shlex-1.3.0/LICENSE-MIT
```

The `LICENSE-APACHE` files are present in the same directories and are the
authoritative copy of the Apache-2.0 license text; per SPDX convention the
license text itself is not re-pasted here because Apache-2.0 is widely
available and unambiguous.
