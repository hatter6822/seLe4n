<p align="center">
  <picture>
    <source media="(prefers-color-scheme: dark)" srcset="../../../assets/logo_dark.png" />
    <img src="../../../assets/logo.png" alt="seLe4n logo" width="200" />
  </picture>
</p>

<p align="center">
  <a href="https://github.com/hatter6822/seLe4n/actions/workflows/lean_action_ci.yml"><img src="https://github.com/hatter6822/seLe4n/actions/workflows/lean_action_ci.yml/badge.svg?branch=main" alt="CI" /></a>
  <a href="https://github.com/hatter6822/seLe4n/actions/workflows/platform_security_baseline.yml"><img src="https://github.com/hatter6822/seLe4n/actions/workflows/platform_security_baseline.yml/badge.svg" alt="Security" /></a>
  <img src="https://img.shields.io/badge/version-0.37.63-blue" alt="Version" />
  <img src="https://img.shields.io/badge/Lean-v4.28.0-blueviolet" alt="Lean 4" />
  <a href="../../../LICENSE"><img src="https://img.shields.io/badge/license-GPLv3-blue" alt="License" /></a>
</p>

<p align="center">
  Un microkernel escrito en Lean 4 con demostraciones verificadas por máquina,
  inspirado en la arquitectura de <a href="https://sel4.systems">seL4</a>. Primer objetivo de hardware:
  <strong>Raspberry Pi 5</strong>.
</p>
<p align="center">
  <div align="center">
    Creado cuidadosamente con la ayuda de:
  </div>
  <div align="center">
    claude :robot: :heart: :robot: codex
  </div>
  <div align="center">
    <strong>TRATE ESTE KERNEL EN CONSECUENCIA</strong>
  </div>
</p>

<p align="center">
  <a href="../../../README.md">English</a> ·
  <a href="../zh-CN/README.md">简体中文</a> ·
  <strong>Español</strong> ·
  <a href="../ja/README.md">日本語</a> ·
  <a href="../ko/README.md">한국어</a> ·
  <a href="../ar/README.md">العربية</a> ·
  <a href="../fr/README.md">Français</a> ·
  <a href="../pt-BR/README.md">Português</a> ·
  <a href="../ru/README.md">Русский</a> ·
  <a href="../de/README.md">Deutsch</a> ·
  <a href="../hi/README.md">हिन्दी</a> ·
  <a href="../uk/README.md">Українська</a>
</p>

---

## ¿Qué es seLe4n?

seLe4n es un micronúcleo construido desde cero en Lean 4. Cada transición del
núcleo es una función pura ejecutable, y cada invariante lo comprueba el núcleo
de Lean: la superficie de pruebas de producción tiene cero `sorry` y cero
`axiom`. El mismo código Lean se compila a código nativo y se enlaza, junto con
una pequeña capa de hardware en Rust, en la imagen del núcleo que arranca en el
objetivo.

El proyecto conserva el modelo de seguridad basado en capacidades de seL4 y,
cada vez más, la ABI de seL4 visible para el usuario, a la vez que usa Lean para
demostrar más sobre ella y endurecerla donde seL4 deja un hueco. La
especificación completa es [`docs/spec/SELE4N_SPEC.md`](../../../docs/spec/SELE4N_SPEC.md);
los puntos siguientes remiten a ella.

### La ABI de seL4

- **Las llamadas al sistema de seL4-MCS** — las once llamadas MCS (`Call` …
  `Yield`), numeradas en `x7` como las numera seL4; la operación se elige a
  partir de la llamada, el tipo de la capacidad invocada y la etiqueta del
  mensaje (`Syscall.selectOperation`), como en seL4
- **Las cargas de error y de fallo de seL4** — `LookupFault`, la trama de error
  en el orden de registros de mensaje de seL4, los fallos de capacidad en el
  lado receptor, el estado `Restart`, los argumentos de capacidad pasados como
  capacidades adicionales, y la guarda contenida en la capacidad con un único
  `resolveAddressBits`
- El resto del trabajo sobre la ABI de seL4 (las invocaciones restantes, los
  fallos de tiempo de espera, los derechos por invocación, el estado Running
  por núcleo) es el flujo de trabajo activo WS-SX; sus filas están en
  [`docs/planning/SEL4_ABI_FIDELITY_PLAN.md`](../../../docs/planning/SEL4_ABI_FIDELITY_PLAN.md)

### Planificación y tiempo real

- **Contextos de planificación como capacidades** — el tiempo de CPU es un
  objeto del núcleo. Un `SchedContext` contiene el presupuesto, el periodo y las
  recargas de seL4-MCS, se configura mediante la autoridad `SchedControl` del
  núcleo de CPU y se vincula a los hilos mediante capacidades; sus invariantes
  (`budgetWithinBounds`, `refillsConserved`) forman parte del conjunto de nivel
  superior. El aislamiento de ancho de banda es `refill_window_bound`: un
  contexto no ejecuta más que su presupuesto en ninguna ventana de un periodo,
  la garantía de ventana deslizante de seL4-MCS. Un planificador jerárquico de
  ancho de banda constante con raíz EDF, que añade la recíproca (un servidor
  admitido recibe su presupuesto en cada ventana), es el flujo de trabajo
  previsto WS-CB
  ([`docs/planning/HIERARCHICAL_CBS_PLAN.md`](../../../docs/planning/HIERARCHICAL_CBS_PLAN.md))
- **Servidores pasivos** — un servidor se ejecuta con el contexto de
  planificación que su cliente le dona durante el IPC; `donationChainAcyclic`
  excluye las donaciones circulares
- **Tiempos de espera de IPC guiados por presupuesto** — un hilo bloqueado cuyo
  presupuesto se agota se retira de la cola de su endpoint (`timeoutThread`)
- **Herencia de prioridad** — propagación transitiva con ausencia de ciclos de
  bloqueo verificada por máquina (`blockingAcyclic`) y un teorema de inversión
  acotada (`pip_bounded_inversion`)
- **Latencia acotada** — una cota paramétrica del tiempo de respuesta en el peor
  caso, `wcrtBound D L_max N B P = D × L_max + N × (B + P)`
  (`bounded_scheduling_latency_exists`, con una forma por núcleo), demostrada
  sobre los módulos de `SeLe4n/Kernel/Scheduler/Liveness/`

### Objetos del núcleo y memoria

- **Objetos tallados en memoria untyped** — el retype talla un objeto en la
  región de una capacidad untyped, y el reinicio de un untyped es el de seL4.
  Llevar las celdas de cada objeto tallado a la propia memoria de su untyped es
  el flujo de trabajo activo WS-UC
- **Una entrada del núcleo no asigna nada** — las entradas compiladas de
  llamada al sistema, fallo e interrupción no hacen ninguna asignación en el
  heap; el tallado de un retype solo asigna las celdas del nuevo objeto. La
  puerta de heap de QEMU (`scripts/test_qemu_heap_allocations_per_syscall.sh`)
  mide cada entrada en la imagen arrancada y falla ante cualquier otro recuento
- **Estructuras de datos** — el almacén de objetos y los mapeos de VSpace son
  tablas hash Robin Hood verificadas (`RHTable`, con `distCorrect`,
  `noDupKeys` y `probeChainDominant`); un CNode es un arreglo plano de
  `2^radix` ranuras, como en seL4; las colas de ejecución, las colas de
  endpoint y de notificación y las esperas de respuesta se enlazan a través de
  los TCB, cada una con una cola abstracta fantasma cuyo acuerdo con los
  enlaces está demostrado
- **Árbol de derivación de capacidades enlazado por las ranuras** — cada ranura
  guarda sus enlaces de padre, primer hijo y hermano (la base de datos de mapeo
  de seL4), cuyo acuerdo con el árbol está demostrado; el borrado, la
  revocación (el bucle `cteRevoke` de seL4) y la transferencia de ranuras
  recorren los enlaces
- **VSpace** — tablas de páginas ARMv8 con W^X impuesto por marco y
  comprobaciones del tipo de memoria que rechazan un alias sin caché de la RAM

### Seguridad y verificación

- **Flujo de información de N dominios** — políticas de flujo parametrizadas
  que generalizan la partición de dos dominios de seL4; una frontera de
  aplicación cuya longitud fija `enforcementBoundaryExtended_count` (y
  `enforcementBoundaryPerCore_count` para la frontera por núcleo); un teorema
  de no interferencia para cada constructor de `NonInterferenceStep`; y una
  pista de auditoría de desclasificación acotada y fail-closed, leída mediante
  una capacidad `auditTrail`
- **Capa de pruebas compuesta** — `proofLayerInvariantBundle`
  (`SeLe4n/Kernel/Architecture/Invariant.lean`) une el conjunto de invariantes
  de cada subsistema (planificador, capacidades, IPC y su acoplamiento con el
  planificador, ciclo de vida, registro de servicios, VSpace, entre
  subsistemas, coherencia de TLB y de caché de instrucciones, shootdown de TLB,
  registro de auditoría de desclasificación, y el acuerdo de cada estructura
  enlazada con su fantasma) en una única obligación que se mantiene desde el
  arranque a través de cada operación
- **Multinúcleo** — cuatro núcleos con planificación por núcleo, IPC y
  despertar entre núcleos, y shootdown de TLB; el flujo de trabajo de
  finalización de SMP (WS-SM) está en curso
- **Estado en tres fases** — una fase de construcción con testigos de
  invariantes se congela en una representación inmutable con equivalencia de
  búsqueda demostrada; las operaciones congeladas cubren las llamadas que
  enumera `frozenOpCoverage`, fijadas por `frozenOpCoverage_count`
- **Registro de servicios** — una extensión de seLe4n, ausente en seL4: los
  servicios se registran y se buscan mediante una capacidad `serviceRegistry`
  y se anotan en el endpoint que los sirve; la política de dependencias queda,
  como en seL4, en un gestor de servicios en espacio de usuario

## Estado actual

<!-- Metrics below are synced from docs/codebase_map.json → readme_sync section.
     Regenerate with: ./scripts/generate_codebase_map.py --pretty
     Source of truth: docs/codebase_map.json (readme_sync) -->

| Atributo | Valor |
|----------|-------|
| **Versión** | `0.37.63` |
| **Toolchain de Lean** | `v4.28.0` |
| **LoC de producción en Lean** | 699.573 en 709 archivos |
| **LoC de pruebas en Lean** | 91.919 en 71 suites de pruebas |
| **Declaraciones demostradas** | 27.053 declaraciones theorem/lemma (cero sorry/axiom) |
| **Crates de Rust** | `sele4n-types`, `sele4n-abi`, `sele4n-sys` (envoltorios en espacio de usuario), `sele4n-hal` (la capa de hardware del núcleo) y la prueba de host `sele4n-lean-boundary` |
| **Hardware objetivo** | Raspberry Pi 5 (BCM2712 / ARM Cortex-A76 / ARMv8-A) |
| **Carriles de arranque** | Cada carril de QEMU arranca primero la imagen de Raspberry Pi 5 en la máquina `raspi5b` de [rpi5_machine](https://github.com/hatter6822/rpi5_machine) y después la imagen `virt` en la máquina `virt` de QEMU |
| **Flujos de trabajo** | Estado de cada flujo de trabajo abierto: [`docs/agent_guide/WORKSTREAM_CONTEXT.md`](../../../docs/agent_guide/WORKSTREAM_CONTEXT.md); índice y registro de deuda: [`docs/REGISTERED_DEBT.md`](../../../docs/REGISTERED_DEBT.md) |
| **Auditorías** | [`docs/audits/`](../../../docs/audits/README.md) — los artefactos de la auditoría activa; las anteriores están archivadas |
| **Mapa del código** | [`docs/codebase_map.json`](../../../docs/codebase_map.json) — inventario de declaraciones legible por máquina |

Las métricas se derivan del código con `./scripts/generate_codebase_map.py` y se
guardan en [`docs/codebase_map.json`](../../../docs/codebase_map.json) bajo la clave
`readme_sync`. Actualice toda la documentación a la vez con
`./scripts/sync_documentation_metrics.sh` (solo verificación: `--check`).

## Inicio rápido

```bash
./scripts/setup_lean_env.sh    # install the Lean toolchain and test dependencies
source ~/.elan/env
lake build                     # build the default targets
lake exe sele4n                # run the trace harness
./scripts/test_smoke.sh        # hygiene + build + trace + negative-state
```

`lake build` solo construye lo que alcanzan `Main.lean` y los ejecutables de
prueba; antes de confirmar un archivo `.lean`, construya su módulo por nombre
(`lake build <Module.Path>`). El flujo de trabajo completo está en
[`docs/DEVELOPMENT.md`](../../../docs/DEVELOPMENT.md), y las reglas que sigue cada
colaborador están en [`CLAUDE.md`](../../../CLAUDE.md).

## Documentación

| Empiece aquí | Después |
|--------------|---------|
| [`docs/DEVELOPMENT.md`](../../../docs/DEVELOPMENT.md) — flujo de trabajo, validación, lista de PR | [`docs/spec/SELE4N_SPEC.md`](../../../docs/spec/SELE4N_SPEC.md) — especificación e hitos |
| [`docs/gitbook/README.md`](../../../docs/gitbook/README.md) — manual completo | [`docs/spec/SEL4_SPEC.md`](../../../docs/spec/SEL4_SPEC.md) — semántica de referencia de seL4 |
| [`docs/codebase_map.json`](../../../docs/codebase_map.json) — inventario legible por máquina | [`docs/REGISTERED_DEBT.md`](../../../docs/REGISTERED_DEBT.md) — cada elemento diferido, con un responsable |
| [`CONTRIBUTING.md`](../../../CONTRIBUTING.md) — mecánica de contribución | [`CHANGELOG.md`](../../../CHANGELOG.md) — historial de versiones |

## Comandos de validación

```bash
./scripts/test_fast.sh      # Tier 0+1: hygiene + build
./scripts/test_smoke.sh     # + Tier 2: trace + negative-state
./scripts/test_full.sh      # + Tier 3: invariant surface anchors + Lean #check
NIGHTLY_ENABLE_EXPERIMENTAL=1 ./scripts/test_nightly.sh  # + Tier 4: nightly determinism

./scripts/test_rust.sh                 # host Rust: build, tests, fmt, clippy
./scripts/test_aarch64_cross_build.sh  # the kernel HAL's real target

./scripts/test_qemu.sh                 # boot the image on raspi5b, then on virt
./scripts/test_qemu.sh --lean-kernel   # the Lean-linked images, on four cores
```

Ejecute al menos `test_smoke.sh` antes de cualquier PR, y `test_full.sh` al
cambiar teoremas, invariantes o anclas de Tier 3. Un tier se detiene en su
primera comprobación fallida; pase `--continue` para reunir todos los fallos de
una vez.

Tras cualquier cambio bajo `rust/`, ejecute **ambos** carriles de Rust. Cubren
mitades disjuntas de la misma crate: en el host se elimina cada bloque
`#[cfg(target_arch = "aarch64")]` antes de que rustc o clippy lo vean, así que
el carril de host no ve los bloques condicionales, los sitios `asm!` ni las
fuentes `.S` que forman la mayor parte del HAL. El carril cruzado construye
`sele4n-hal` para `aarch64-unknown-none-softfloat` en ambos perfiles, verifica
que las fuentes en ensamblador se ensamblaron, analiza el objetivo cruzado y
desensambla los objetos de release para demostrar que no usan ningún registro
FP/SIMD. Los carriles de QEMU construyen rpi5_machine en el commit fijado en
`scripts/setup_rpi5_machine.sh` en el primer uso; un carril al que le falta un
requisito se informa como NOT RUN en lugar de aprobarse. La lista completa está
en [`docs/DEVELOPMENT.md`](../../../docs/DEVELOPMENT.md).

## Arquitectura

seLe4n se organiza en contratos por capas, cada uno con transiciones
ejecutables y pruebas de preservación de invariantes verificadas por máquina:

```
┌──────────────────────────────────────────────────────────────────────┐
│   Kernel entries  (syscall, fault, interrupt, per-core timer tick)   │
│                 Kernel API  (SeLe4n/Kernel/API.lean)                 │
├──────────────┬─────────────┬────────────┬───────────┬────────────────┤
│  Scheduler   │  Capability │    IPC     │ Lifecycle │  Service (ext) │
│   RunQueue   │  CSpace/CDT │  DualQueue │  Untyped  │    Registry    │
│ SchedContext │             │  Donation  │  Retype   │                │
├──────────────┴─────────────┴────────────┴───────────┴────────────────┤
│         Information Flow  (Policy, Projection, Enforcement)          │
├──────────────────────────────────────────────────────────────────────┤
│  Architecture  (VSpace, page tables, TLB/cache, decode, trap frame)  │
├──────────────────────────────────────────────────────────────────────┤
│         Concurrency  (locks, memory model, per-core state)           │
├──────────────────────────────────────────────────────────────────────┤
│                     Model  (Object, State, CDT)                      │
├──────────────────────────────────────────────────────────────────────┤
│             Foundations  (Prelude, Machine, MachineConfig)           │
├──────────────────────────────────────────────────────────────────────┤
│    Platform  (Contract, Boot, Sim, RPi5, QemuVirt)  ← bindings       │
├──────────────────────────────────────────────────────────────────────┤
│        Rust HAL  (rust/sele4n-hal: boot, traps, GIC, MMU, SMP)       │
└──────────────────────────────────────────────────────────────────────┘
```

## Estructura del código fuente

```
SeLe4n/
├── Prelude.lean                 Typed identifiers, KernelM monad
├── Machine.lean                 Register file, memory, timer
├── Model/                       Object types, SystemState, slot links, builder/freeze phases
├── Kernel/
│   ├── API.lean                 Unified public API + apiInvariantBundle
│   ├── *Entry.lean              Compiled syscall, fault, interrupt and per-core timer entries
│   ├── Scheduler/               Run queues, selection, priority inheritance, liveness (WCRT)
│   ├── SchedContext/            Scheduling contexts, seL4-MCS refills, SchedControl
│   ├── Capability/              CSpace operations, derivation tree, authority proofs
│   ├── IPC/                     Dual-queue endpoints, donation, timeouts, cross-core IPC
│   ├── Lifecycle/               Untyped retype and reset, thread suspend/resume
│   ├── Service/                 Service registry and its invariants
│   ├── Architecture/            VSpace (W^X), page tables, TLB/cache models, decode, trap frame
│   ├── InformationFlow/         N-domain policy, projection, enforcement, NI proofs
│   ├── Concurrency/             Lock model, memory model, per-core runtime
│   ├── RobinHood/               Verified Robin Hood hash table (RHTable/RHSet)
│   ├── RadixTree/               CNode radix view and its bridge to the slot array
│   ├── FrozenOps/               Frozen-state operations + commutativity proofs
│   └── CrossSubsystem.lean      Cross-subsystem invariant composition
├── Platform/
│   ├── Contract.lean            PlatformBinding typeclass and boundary contracts
│   ├── Boot.lean, Boot/         Boot sequence: root server, initial threads, IRQ nodes
│   ├── FFI.lean                 The Lean side of the HAL boundary
│   ├── Sim/                     Simulation platform (permissive contracts for testing)
│   ├── RPi5/                    Raspberry Pi 5 (BCM2712, GIC-400, MMIO, boot VSpace)
│   └── QemuVirt/                QEMU `virt` binding and boot entry
├── Testing/                     Test harness, state builder, invariant checks, censuses
Main.lean                        Executable entry point
tests/                           Executable test suites + fixtures
rust/                            sele4n-types, sele4n-abi, sele4n-sys, sele4n-hal, sele4n-lean-boundary
```

Cada subsistema sigue la **separación Operations/Invariant**: las transiciones
en `Operations.lean`, las pruebas en `Invariant.lean`. El `apiInvariantBundle`
unificado agrega todos los invariantes de los subsistemas en una única
obligación de prueba. El mapa de subsistemas es
[`docs/DEVELOPMENT.md`](../../../docs/DEVELOPMENT.md) §5; para el inventario completo
por archivo, véase [`docs/codebase_map.json`](../../../docs/codebase_map.json).

## Comparación con seL4

| Característica | seL4 | seLe4n |
|----------------|------|--------|
| **ABI de llamadas al sistema** | Llamadas MCS, etiquetas de invocación, cargas de error y de fallo | Las mismas: las once llamadas de seL4-MCS con su numeración, invocaciones elegidas por etiqueta y las cargas de error de seL4; las invocaciones restantes son filas de WS-SX |
| **Planificación** | Contextos de planificación MCS con recargas de servidor esporádico | El mismo motor de recargas, con su invariante de conservación y la cota de un presupuesto por ventana (`refill_window_bound`) demostrados; se prevé un CBS jerárquico con raíz EDF (WS-CB) |
| **Servidores pasivos** | Donación de SchedContext | Donación verificada con el invariante `donationChainAcyclic` |
| **IPC** | Una cola por endpoint, enlazada a través de los TCB | Una cola de envío y una de recepción por endpoint, ambas enlazadas a través de los TCB con extracción en O(1) desde cualquier posición; tiempos de espera guiados por presupuesto |
| **Flujo de información** | Partición binaria alto/bajo | Política configurable de N dominios, una frontera de aplicación fijada por `enforcementBoundaryExtended_count`, un teorema de no interferencia por paso, y una pista de auditoría controlada por capacidad para cada desclasificación autorizada |
| **Herencia de prioridad** | No está en el núcleo | PIP transitivo verificado por máquina, sin ciclos de bloqueo, con un teorema de inversión acotada |
| **Latencia acotada** | Sin cota WCRT formal | `wcrtBound D L_max N B P = D × L_max + N × (B + P)`, demostrada sobre los módulos de vivacidad |
| **Almacén de objetos** | Objetos en direcciones físicas | Tablas hash Robin Hood verificadas (`RHTable`/`RHSet`); los CNodes son arreglos planos de ranuras como en seL4 |
| **Mapeo de memoria** | W^X no impuesto por el núcleo | W^X impuesto por marco como invariante; las comprobaciones del tipo de memoria rechazan un alias sin caché de la RAM |
| **Gestión de servicios** | Fuera del núcleo | Registro de servicios controlado por capacidad sobre el endpoint; política de dependencias en espacio de usuario |
| **Pruebas** | Isabelle/HOL, sobre el C por refinamiento | Lean 4, junto a las transiciones ejecutables; cero sorry/axiom (recuento en la tabla anterior) |
| **Plataforma** | HAL a nivel de C | Clase de tipos `PlatformBinding` con contratos de frontera tipados y un HAL en Rust |

## Licencia y atribuciones de terceros

seLe4n se distribuye bajo la GNU General Public License v3.0 o posterior
(GPLv3+); consulte [`LICENSE`](../../../LICENSE) para el texto completo. Las
dependencias de compilación de terceros (`cc`, `find-msvc-tools`, `shlex`,
todas con doble licencia `MIT OR Apache-2.0`) se usan bajo la opción MIT; sus
avisos originales de copyright y de permiso se reproducen literalmente en
[`THIRD_PARTY_LICENSES.md`](../../../THIRD_PARTY_LICENSES.md). El binario del
kernel no contiene código de terceros enlazado en tiempo de ejecución: el HAL
es `#![no_std]` y solo usa `core::*`.

---

> Este documento es una traducción del [README en inglés](../../../README.md).
