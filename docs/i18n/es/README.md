<p align="center">
  <picture>
    <source media="(prefers-color-scheme: dark)" srcset="../../../assets/logo_dark.png" />
    <img src="../../../assets/logo.png" alt="seLe4n logo" width="200" />
  </picture>
</p>

<p align="center">
  <a href="https://github.com/hatter6822/seLe4n/actions/workflows/lean_action_ci.yml"><img src="https://github.com/hatter6822/seLe4n/actions/workflows/lean_action_ci.yml/badge.svg?branch=main" alt="CI" /></a>
  <a href="https://github.com/hatter6822/seLe4n/actions/workflows/platform_security_baseline.yml"><img src="https://github.com/hatter6822/seLe4n/actions/workflows/platform_security_baseline.yml/badge.svg" alt="Security" /></a>
  <img src="https://img.shields.io/badge/version-0.29.6-blue" alt="Version" />
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
  <a href="../hi/README.md">हिन्दी</a>
</p>

---

## ¿Qué es seLe4n?

seLe4n es un microkernel construido desde cero en Lean 4. Cada transición del
kernel es una función pura ejecutable. Cada invariante es verificado por máquina
mediante el comprobador de tipos de Lean — cero `sorry`, cero `axiom`. Toda la
superficie de demostraciones compila a código nativo sin pruebas admitidas.

El proyecto conserva el modelo de seguridad basado en capacidades de seL4, al
tiempo que introduce mejoras arquitectónicas habilitadas por el marco de
demostración de Lean 4:

### Planificación y garantías de tiempo real

- **Objetos de rendimiento componibles** — el tiempo de CPU es un objeto de kernel de primera clase. `SchedContext` encapsula presupuesto, período, prioridad, fecha límite y dominio en un contexto de planificación reutilizable al que los hilos se vinculan mediante capacidades. La planificación CBS (Constant Bandwidth Server) proporciona aislamiento de ancho de banda demostrado (teorema `cbs_bandwidth_bounded`)
- **Servidores pasivos** — los servidores inactivos toman prestado el `SchedContext` del cliente durante IPC, consumiendo cero CPU cuando no están sirviendo. El invariante `donationChainAcyclic` previene cadenas de donación circulares
- **Tiempos límite de IPC basados en presupuesto** — las operaciones bloqueantes están acotadas por el presupuesto del invocador. Al expirar, los hilos se extraen de la cola del endpoint y se vuelven a encolar
- **Protocolo de herencia de prioridad** — propagación transitiva de prioridad con libertad de interbloqueo verificada por máquina (`blockingChainAcyclic`) y profundidad de cadena acotada. Previene la inversión de prioridad sin límite
- **Teorema de latencia acotada** — cota WCRT verificada por máquina: `WCRT = D × L_max + N × (B + P)`, demostrada en 7 módulos de vivacidad que cubren monotonicidad de presupuesto, temporización de reposición, semántica de yield, agotamiento de banda y rotación de dominio

### Estructuras de datos e IPC

- **Rutas críticas en O(1) basadas en hash** — todos los almacenes de objetos, colas de ejecución, ranuras de CNode, mapeos de VSpace y colas de IPC utilizan tablas hash Robin Hood verificadas formalmente con invariantes `distCorrect`, `noDupKeys` y `probeChainDominant`
- **IPC de doble cola intrusiva** — punteros inversos por hilo para encolado, desencolado y eliminación en medio de la cola en O(1)
- **Árbol de derivación de capacidades estable por nodo** — índices `childMap` + `parentMap` para transferencia de ranuras, revocación y recorrido de descendientes en O(1)

### Seguridad y verificación

- **Flujo de información de N dominios** — políticas de flujo parametrizadas que generalizan la partición binaria de seL4. Frontera de aplicación de 33 entradas con demostraciones de no interferencia por operación (inductivo `NonInterferenceStep` de 35 constructores)
- **Capa de demostración compuesta** — `proofLayerInvariantBundle` compone 10 invariantes de subsistema (planificador, capacidad, IPC, ciclo de vida, servicio, VSpace, intersubsistema, TLB y extensiones CBS) en una única obligación de nivel superior verificada desde el arranque a través de todas las operaciones
- **Arquitectura de estado en dos fases** — la fase de construcción con testigos de invariantes alimenta una representación inmutable congelada con equivalencia de consulta demostrada. 20 operaciones congeladas replican la API en vivo
- **Conjunto completo de operaciones** — todas las operaciones de seL4 implementadas con preservación de invariantes, incluyendo las 5 operaciones diferidas (suspend/resume, setPriority/setMCPriority, setIPCBuffer)
- **Orquestación de servicios** — ciclo de vida de componentes a nivel de kernel con grafos de dependencia y demostraciones de aciclicidad (extensión de seLe4n, no presente en seL4)

## Estado actual

<!-- Las métricas se sincronizan desde docs/codebase_map.json → sección readme_sync.
     Regenerar con: ./scripts/generate_codebase_map.py --pretty
     Fuente de verdad: docs/codebase_map.json (readme_sync) -->

| Atributo | Valor |
|----------|-------|
| **Versión** | `0.25.5` |
| **Toolchain de Lean** | `v4.28.0` |
| **LoC de producción en Lean** | 83.286 en 132 archivos |
| **LoC de pruebas en Lean** | 10.564 en 15 suites de pruebas |
| **Declaraciones demostradas** | 2.447 declaraciones theorem/lemma (cero sorry/axiom) |
| **Hardware objetivo** | Raspberry Pi 5 (BCM2712 / ARM Cortex-A76 / ARMv8-A) |
| **Última auditoría** | [`AUDIT_COMPREHENSIVE_v0.23.21`](../../../docs/dev_history/AUDIT_COMPREHENSIVE_v0.23.21_LEAN_RUST_KERNEL.md) — Auditoría completa del kernel Lean + Rust (0 CRIT, 5 HIGH, 8 MED, 30 LOW) |
| **Mapa del código** | [`docs/codebase_map.json`](../../../docs/codebase_map.json) — inventario de declaraciones legible por máquina |

Las métricas se derivan del código fuente mediante `./scripts/generate_codebase_map.py`
y se almacenan en [`docs/codebase_map.json`](../../../docs/codebase_map.json) bajo la
clave `readme_sync`. Actualice toda la documentación de forma conjunta usando
`./scripts/report_current_state.py` como verificación cruzada.

## Inicio rápido

```bash
./scripts/setup_lean_env.sh   # instalar el toolchain de Lean
lake build                     # compilar todos los módulos
lake exe sele4n                # ejecutar el arnés de trazas
./scripts/test_smoke.sh        # validar (higiene + compilación + trazas + estado negativo + sinc. docs)
```

## Documentación

| Comience aquí | Después |
|---------------|---------|
| [`docs/DEVELOPMENT.md`](../../../docs/DEVELOPMENT.md) — flujo de trabajo, validación, lista de verificación para PRs | [`docs/spec/SELE4N_SPEC.md`](../../../docs/spec/SELE4N_SPEC.md) — especificación e hitos |
| [`docs/gitbook/README.md`](../../../docs/gitbook/README.md) — manual completo | [`docs/spec/SEL4_SPEC.md`](../../../docs/spec/SEL4_SPEC.md) — semántica de referencia de seL4 |
| [`docs/codebase_map.json`](../../../docs/codebase_map.json) — inventario legible por máquina | [`docs/WORKSTREAM_HISTORY.md`](../../../docs/WORKSTREAM_HISTORY.md) — historial de flujos de trabajo y hoja de ruta |
| [`CONTRIBUTING.md`](../../../CONTRIBUTING.md) — mecánica de contribución | [`CHANGELOG.md`](../../../CHANGELOG.md) — historial de versiones |

[`docs/codebase_map.json`](../../../docs/codebase_map.json) es la fuente de verdad para
las métricas del proyecto. Alimenta [seLe4n.org](https://github.com/hatter6822/hatter6822.github.io)
y se actualiza automáticamente en cada merge vía CI. Regenere con
`./scripts/generate_codebase_map.py --pretty`.

## Comandos de validación

```bash
./scripts/test_fast.sh      # Nivel 0+1: higiene + compilación
./scripts/test_smoke.sh     # + Nivel 2: trazas + estado negativo + sinc. docs
./scripts/test_full.sh      # + Nivel 3: anclajes de superficie de invariantes + Lean #check
NIGHTLY_ENABLE_EXPERIMENTAL=1 ./scripts/test_nightly.sh  # + Nivel 4: determinismo nocturno
```

Ejecute al menos `test_smoke.sh` antes de cualquier PR. Ejecute `test_full.sh`
cuando modifique teoremas, invariantes o anclajes de documentación.

## Arquitectura

seLe4n está organizado como contratos por capas, cada uno con transiciones
ejecutables y demostraciones de preservación de invariantes verificadas por máquina:

```
┌──────────────────────────────────────────────────────────────────────┐
│                 Kernel API  (SeLe4n/Kernel/API.lean)                 │
├──────────────┬─────────────┬────────────┬───────────┬────────────────┤
│   Scheduler  │  Capability │    IPC     │ Lifecycle │  Service (ext) │
│  RunQueue    │  CSpace/CDT │  DualQueue │  Retype   │  Orchestration │
│  SchedContext│             │  Donation  │           │                │
├──────────────┴─────────────┴────────────┴───────────┴────────────────┤
│         Information Flow  (Policy, Projection, Enforcement)          │
├──────────────────────────────────────────────────────────────────────┤
│     Architecture  (VSpace, VSpaceBackend, Adapter, Assumptions)      │
├──────────────────────────────────────────────────────────────────────┤
│                     Model  (Object, State, CDT)                      │
├──────────────────────────────────────────────────────────────────────┤
│             Foundations  (Prelude, Machine, MachineConfig)           │
├──────────────────────────────────────────────────────────────────────┤
│          Platform  (Contract, Sim, RPi5)  ← H3-prep bindings         │
└──────────────────────────────────────────────────────────────────────┘
```

## Estructura del código fuente

```
SeLe4n/
├── Prelude.lean                 Typed identifiers, KernelM monad
├── Machine.lean                 Register file, memory, timer
├── Model/                       Object types, SystemState, builder/freeze phases
├── Kernel/
│   ├── API.lean                 Unified public API + apiInvariantBundle
│   ├── Scheduler/               RunQueue, EDF selection, PriorityInheritance, Liveness (WCRT)
│   ├── Capability/              CSpace ops + CDT tracking, authority/preservation proofs
│   ├── IPC/                     Dual-queue endpoints, donation, timeouts, structural invariants
│   ├── Lifecycle/               Object retype, thread suspend/resume
│   ├── Service/                 Service orchestration, registry, acyclicity proofs
│   ├── Architecture/            VSpace (W^X), TLB model, register/syscall decode
│   ├── InformationFlow/         N-domain policy, projection, enforcement, NI proofs
│   ├── RobinHood/               Verified Robin Hood hash table (RHTable/RHSet)
│   ├── RadixTree/               CNode radix tree (O(1) flat array)
│   ├── SchedContext/             CBS budget engine, replenishment queue, priority management
│   ├── FrozenOps/               Frozen-state operations + commutativity proofs
│   └── CrossSubsystem.lean      Cross-subsystem invariant composition
├── Platform/
│   ├── Contract.lean            PlatformBinding typeclass
│   ├── Boot.lean                Boot sequence (PlatformConfig → IntermediateState)
│   ├── Sim/                     Simulation platform (permissive contracts for testing)
│   └── RPi5/                    Raspberry Pi 5 (BCM2712, GIC-400, MMIO)
├── Testing/                     Test harness, state builder, invariant checks
Main.lean                        Executable entry point
tests/                           15 test suites
```

Cada subsistema sigue la separación **Operations/Invariant**: las transiciones
en `Operations.lean`, las demostraciones en `Invariant.lean`. El
`apiInvariantBundle` unificado agrega todos los invariantes de subsistema en una
única obligación de prueba. Para el inventario completo por archivo, consulte
[`docs/codebase_map.json`](../../../docs/codebase_map.json).

## Comparación con seL4

| Característica | seL4 | seLe4n |
|----------------|------|--------|
| **Planificación** | Servidor esporádico implementado en C (MCS) | CBS con teorema `cbs_bandwidth_bounded` verificado por máquina; `SchedContext` como objeto de kernel controlado por capacidades |
| **Servidores pasivos** | Donación de SchedContext vía C | Donación verificada con invariante `donationChainAcyclic` |
| **IPC** | Cola de endpoint con lista enlazada simple | Doble cola intrusiva con eliminación en medio de la cola en O(1); tiempos límite basados en presupuesto |
| **Flujo de información** | Partición binaria alto/bajo | Política configurable de N dominios con frontera de aplicación de 30 entradas y demostraciones de no interferencia por operación |
| **Herencia de prioridad** | PIP implementado en C (rama MCS) | PIP transitivo verificado por máquina con libertad de interbloqueo y cota WCRT paramétrica |
| **Latencia acotada** | Sin cota WCRT formal | `WCRT = D × L_max + N × (B + P)` demostrada en 7 módulos de vivacidad |
| **Almacenes de objetos** | Listas enlazadas y arreglos | Tablas hash Robin Hood verificadas (`RHTable`/`RHSet`) con rutas críticas en O(1) |
| **Gestión de servicios** | No existe en el kernel | Orquestación de primera clase con grafo de dependencias y demostraciones de aciclicidad |
| **Demostraciones** | Isabelle/HOL, posteriores al hecho | Comprobador de tipos de Lean 4, ubicadas junto a las transiciones (2.447 teoremas, cero sorry/axiom) |
| **Plataforma** | HAL a nivel de C | Typeclass `PlatformBinding` con contratos de frontera tipados |

## Próximos pasos

Todos los flujos de trabajo de nivel de software (WS-B a WS-AB) están completos.
El historial completo se encuentra en [`docs/WORKSTREAM_HISTORY.md`](../../../docs/WORKSTREAM_HISTORY.md).

### Flujos de trabajo completados

| Flujo de trabajo | Alcance | Versión |
|------------------|---------|---------|
| **WS-AB** | Operaciones diferidas y vivacidad — suspend/resume, setPriority/setMCPriority, setIPCBuffer, Protocolo de Herencia de Prioridad, Teorema de Latencia Acotada (6 fases, 90 tareas) | v0.24.0–v0.25.5 |
| **WS-Z** | Objetos de rendimiento componibles — `SchedContext` como 7.o objeto de kernel, motor de presupuesto CBS, cola de reposición, donación de servidor pasivo, endpoints con timeout (10 fases, 213 tareas) | v0.23.0–v0.23.21 |
| **WS-B – WS-Y** | Subsistemas centrales del kernel, tablas hash Robin Hood, árboles radix, estado congelado, flujo de información, orquestación de servicios, contratos de plataforma | v0.9.0–v0.22.x |

Planes detallados: [WS-AB](../../../docs/dev_history/planning/WS_AB_DEFERRED_OPERATIONS_WORKSTREAM_PLAN.md) | [WS-Z](../../../docs/dev_history/planning/WS_Z_COMPOSABLE_PERFORMANCE_OBJECTS.md)

### Próximo hito principal

**Vinculación con hardware Raspberry Pi 5** — recorrido de tablas de páginas
ARMv8, enrutamiento de interrupciones GIC-400, secuencia de arranque. Las
auditorías previas y los cierres de hitos están archivados en
[`docs/dev_history/`](../../../docs/dev_history/README.md).

---

> Este documento es una traducción del [README en inglés](../../../README.md).
