# WS-RB — Boot the kernel on the emulated Raspberry Pi 5

> **Workstream**: WS-RB (the QEMU lanes moved onto rpi5_machine's `raspi5b`).
> **Status**: **ACTIVE** — registered at `v0.37.25` with RB1; RB2 at `v0.37.26`;
> RB3 at `v0.37.28`; RB4 at `v0.37.29`.
> **Baseline**: the tree at `v0.37.24`. Every `file:line` below was read
> against it.
> **Rows**: RB1–RB5, numbered in the order they are implemented, one PR each.
> Each row consumes only lower-numbered rows. No two rows run in parallel.
> **Owner decision** (Adam, 2026-11-15): move CI, the exercisers and the local
> scripts onto [rpi5_machine](https://github.com/hatter6822/rpi5_machine);
> keep QEMU `virt` as a second lane.

## 1. The problem

Every QEMU boot in the tree runs an image built for QEMU's `virt` machine
(`board_qemu_virt`, `rust/sele4n-hal/src/board.rs:88`). That choice was made
at WS-BP BP8.1 (`docs/planning/SMP_BOOT_PATH_PLAN.md:383`) because upstream
QEMU has no BCM2712 model and `raspi4b` has no PSCI. So the image the kernel
ships for, the Raspberry Pi 5 one, has never run anywhere.

rpi5_machine is an out-of-tree QEMU (pinned v11.1.1) whose `raspi5b` machine
models the Pi 5: four Cortex-A76 PEs with `MPIDR_EL1.MT` set and the core in
Aff1, the GIC-400, UART10, the 54 MHz generic timer, EL2 entry with PSCI over
SMC (the firmware's contract), the firmware's device tree, and, with
`secure=on` and `-bios`, TF-A's `rpi5` BL31 as the Pi's armstub. Its
`scripts/rpi5-boot` boots an SD-card image as the Pi 5's firmware does.

The first boot of the Raspberry Pi 5 image on `raspi5b` found a board bug at
once: `SECONDARY_MPIDR_TABLE` (`rust/sele4n-hal/src/smp.rs:231`) targeted
MPIDR `0x1`, `0x2`, `0x3`, which is `virt`'s numbering. The BCM2712's
secondaries are `0x100`, `0x200`, `0x300` (`bcm2712.dtsi`'s `cpu@100` ..
`cpu@300`). PSCI refused every `CPU_ON`, so on a real Pi 5 the Lean-linked
kernel would have halted at its Phase 7 topology refusal. `virt` hid it.

## 2. Facts the rows rest on

- **F1.** The Raspberry Pi 5 image boots on `raspi5b` with `-kernel` given the
  raw image: QEMU loads an arm64 `Image` at RAM base + `text_offset`
  (`0x8_0000`, the header `boot.S` declares) and passes the device tree in
  `x0`, entering at EL2.
- **F2.** `raspi5b` accepts `-cpu cortex-a76` (its only CPU) and `-nic none`,
  so `qemu_run` (`scripts/qemu_boot_lib.sh`) drives both machines unchanged.
- **F3.** With `-m 1G`, the `raspi5b` tree's memory node is
  `[0, 0x3FC0_0000)`: the first gigabyte less the VideoCore's 4 MiB, as a
  Pi 5's firmware reports it. The RPi5 binding selects its 1 GiB variant.
- **F4.** `raspi5b`'s tree carries per-run random `/chosen` `kaslr-seed` and
  `rng-seed`, as `virt`'s does, so the fixture renderer
  (`scripts/qemu_dtb_fixture.py`) serves both boards.
- **F5.** rpi5_machine builds in about fifteen minutes on four cores and its
  stripped emulator is about 35 MB and runs without the build tree.
- **F6.** The exerciser image raises INTIDs 250 and 251
  (`rust/sele4n-hal/src/smp_exercisers.rs:11665`) because `virt` wires
  nothing there. On the BCM2712 they are PCIe interrupts (`GIC_SPI 209`–`234`
  = INTIDs 241–266). The lines past UARTA (`GIC_SPI 277`–`287`, INTIDs
  309–319) are wired to nothing on the board.
- **F7.** `scripts/rpi5-boot` passes `kernel_address` and
  `device_tree_address` to QEMU only with an armstub; without one it logs them
  as ignored (rpi5_machine `scripts/rpi5-boot:1144`). The Pi 5's firmware
  honours both, and the image's `config.txt` sets both
  (`scripts/rpi5_boot_files.py:83`).

## 3. Rows

### RB1 — The Raspberry Pi 5 image boots on `raspi5b`

- The secondaries' MPIDRs become a field of `BoardMap`
  (`secondary_mpidrs`): `0x100`/`0x200`/`0x300` on the Pi 5, `1`/`2`/`3` on
  `virt`. `well_formed` refuses a zero, a repeated or a non-affinity entry.
- `scripts/setup_rpi5_machine.sh` pins rpi5_machine by commit and builds it
  once per pin into `.lake/rpi5-machine/<commit>/`.
- `scripts/qemu_boot_lib.sh` gains `qemu_select_board rpi5|virt`.
  `scripts/test_qemu.sh` boots the Raspberry Pi 5 image on `raspi5b` at EL2
  first, then the `virt` image at EL1 and EL2, HAL-only and Lean-linked.
- `tests/fixtures/rpi5_machine_dtb.hex` is `raspi5b`'s own tree, checked
  against a fresh dump by the lane, and `tests/Ak9PlatformSuite.lean` holds
  the RPi5 entry to accepting it (1 GiB variant, first gigabyte to
  `0x3FC0_0000`) and the `virt` bridge to refusing it.
- CI's archive lane builds the pinned machine, cached by the script's hash.

### RB2 — The four-PE bring-up and the refusal probe on `raspi5b`

- `scripts/test_qemu_smp_bringup.sh` boots the Pi 5 image on `raspi5b`
  (HAL-only and Lean-linked), then `virt` as the second lane.
- `scripts/test_qemu_lean_init_refusal.sh` builds the probe for the Pi 5 and
  runs it on `raspi5b`, then on `virt`.

### RB3 — The Tier-4 exercisers on `raspi5b`

- The exerciser image builds for the Pi 5: `smp_exercisers` without
  `board_qemu_virt`. The interrupt scenarios' two lines become board data
  (F6): INTIDs 318 and 319 on the Pi 5, 250 and 251 on `virt`.
- The allocation exerciser's Lean half gains a Pi 5 deployment beside
  `SeLe4n/Platform/QemuVirt/Exerciser.lean`: the RPi5 binding with the same
  five differences (labeling, two downgrades, low band, audit monitor,
  run-time interrupt handlers) at the RPi5 deployment's ids. The shared parts
  move to one board-generic module, so the two deployments cannot diverge.
  `lean_entry.rs` calls `lean_kernel_main_rpi5_exerciser` on the Pi 5 image.
- `scripts/qemu_exerciser_lib.sh` boots `raspi5b`, then `virt`. Every pin
  reads its exact count on both machines: the kernel is the same, so a count
  that differs between boards is a finding, not a second pin.
- *Landed (`v0.37.28`), with the two findings the first `raspi5b` run made,
  each fixed in the row:* the interrupt-mask and issued-line writes rebuilt a
  record on lines 256 and up (one cell per Pi 5 interrupt entry on 318/319;
  the per-word choice is now out of line, `irqMaskWordAt`/`irqMaskWordPast`),
  and the declassification scenario's refused lookup assumed the root task
  was current where a tick can hand core 0 to the partner (it now runs with
  the partner suspended). Every board-booting gate checks every board's
  emulator first (`qemu_gate_boards`, from RB2's review).

### RB4 — Boot the packaged boot files as the firmware does

- rpi5_machine (its own PR there): `scripts/rpi5-boot` honours
  `kernel_address` and `device_tree_address`/`device_tree_end` without an
  armstub, as the Pi 5's firmware does (F7). The pin moves to that commit.
- seLe4n's archive lane writes `kernel8.img` and `config.txt` to an SD-card
  image and boots it with `rpi5-boot`, so the boot files are checked by the
  thing that reads them, not only against the ELF.
- A second run boots the same card through TF-A's `rpi5` BL31 as the
  armstub (`secure=on`, `-bios`), the Pi 5's own boot chain.
- *Landed (`v0.37.29`), wider than the row:* rpi5_machine's fix (its PR #7)
  went into the machine, not only `rpi5-boot`: without an armstub `raspi5b`
  now loads the kernel, initrd and tree as the firmware does and enters the
  kernel from a stub at 0 standing in for the firmware's own BL31, with
  `kernel-address`, `dtb-address` and `dtb-end` beside it, and its
  `scripts/firmware` builds just the outputs named. Every `raspi5b` lane, not
  only the archive lane, now boots the packaged `kernel8.img` at its
  `config.txt` addresses (`rpi5_boot_files.py machine-options`), and
  `test_qemu.sh` boots the SD card through `rpi5-boot` with the firmware's
  BL31 and with TF-A's, on the HAL-only and the Lean-linked image alike. The
  card carries the device tree the Raspberry Pi firmware release ships, which
  `scripts/setup_rpi5_machine.sh` fetches with TF-A from rpi5_machine's pinned
  builder; the TF-A card's `config.txt` adds `armstub=bl31.bin`, the one line
  that is the card's rather than the boot files'.

### RB5 — Closure

- The nightly lane and every local QEMU script default to `raspi5b`.
- Documentation sweep against the final tree: `docs/spec/SELE4N_SPEC.md`,
  `docs/DEVELOPMENT.md`, the GitBook chapters on the boot path and testing,
  `README.md`, `docs/CLAIM_EVIDENCE_INDEX.md`, `docs/REGISTERED_DEBT.md`,
  `docs/agent_guide/WORKSTREAM_CONTEXT.md`; this plan archived. Every
  not-yet-started plan is refreshed against the tree. Minor version bump.

## 4. Estimate

RB1 one session. RB2 one. RB3 three to four (the Lean deployment and its
proofs are the bulk). RB4 two, one of them in rpi5_machine. RB5 one.
