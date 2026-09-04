<p align="center">
  <picture>
    <source media="(prefers-color-scheme: dark)" srcset="../../../assets/logo_dark.png" />
    <img src="../../../assets/logo.png" alt="seLe4n logo" width="200" />
  </picture>
</p>

<p align="center">
  <a href="https://github.com/hatter6822/seLe4n/actions/workflows/lean_action_ci.yml"><img src="https://github.com/hatter6822/seLe4n/actions/workflows/lean_action_ci.yml/badge.svg?branch=main" alt="CI" /></a>
  <a href="https://github.com/hatter6822/seLe4n/actions/workflows/platform_security_baseline.yml"><img src="https://github.com/hatter6822/seLe4n/actions/workflows/platform_security_baseline.yml/badge.svg" alt="Security" /></a>
  <img src="https://img.shields.io/badge/version-0.34.49-blue" alt="Version" />
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
- **Protocolo de herencia de prioridad** — propagación transitiva de prioridad con libertad de interbloqueo verificada por máquina (`blockingAcyclic`) y profundidad de cadena acotada. Previene la inversión de prioridad sin límite
- **Teorema de latencia acotada** — cota WCRT verificada por máquina: `WCRT = D × L_max + N × (B + P)`, demostrada en 8 módulos de vivacidad que cubren monotonicidad de presupuesto, temporización de reposición, semántica de yield, agotamiento de banda y rotación de dominio

### Estructuras de datos e IPC

- **Rutas críticas en O(1) basadas en hash** — todos los almacenes de objetos, colas de ejecución, ranuras de CNode, mapeos de VSpace y colas de IPC utilizan tablas hash Robin Hood verificadas formalmente con invariantes `distCorrect`, `noDupKeys` y `probeChainDominant`
- **IPC de doble cola intrusiva** — punteros inversos por hilo para encolado, desencolado y eliminación en medio de la cola en O(1)
- **Árbol de derivación de capacidades estable por nodo** — índices `childMap` + `parentMap` para transferencia de ranuras, revocación y recorrido de descendientes en O(1)

### Seguridad y verificación

- **Flujo de información de N dominios** — políticas de flujo parametrizadas que generalizan la partición binaria de seL4. Frontera de aplicación de 43 entradas con demostraciones de no interferencia por operación (inductivo `NonInterferenceStep` de 35 constructores), y un registro de auditoría de desclasificación acotado y de cierre ante fallos (fail-closed), con un lector controlado por capacidades
- **Capa de demostración compuesta** — `proofLayerInvariantBundle` compone 16 paquetes de invariantes de subsistema (núcleo del planificador + extensiones CBS, capacidad, IPC + acoplamiento IPC–planificador, ciclo de vida, servicio, VSpace, intersubsistema, consistencia de TLB, consistencia de los esperadores de notificación, cotas de pending/ack del TLB shootdown, invalidación de TLB por núcleo y coherencia de la I-cache, y la cota del registro de auditoría de desclasificación) en una única obligación de nivel superior verificada desde el arranque a través de todas las operaciones
- **Arquitectura de estado en dos fases** — la fase de construcción con testigos de invariantes alimenta una representación inmutable congelada con equivalencia de consulta demostrada. 24 operaciones congeladas replican la API en vivo
- **Conjunto completo de operaciones** — todas las operaciones de seL4 implementadas con preservación de invariantes, incluyendo las 5 operaciones diferidas (suspend/resume, setPriority/setMCPriority, setIPCBuffer)
- **Orquestación de servicios** — ciclo de vida de componentes a nivel de kernel con grafos de dependencia y demostraciones de aciclicidad (extensión de seLe4n, no presente en seL4)

## Estado actual

<!-- Las métricas se sincronizan desde docs/codebase_map.json → sección readme_sync.
     Regenerar con: ./scripts/generate_codebase_map.py --pretty
     Fuente de verdad: docs/codebase_map.json (readme_sync) -->

| Atributo | Valor |
|----------|-------|
| **Versión** | `0.34.49` |
| **Toolchain de Lean** | `v4.28.0` |
| **LoC de producción en Lean** | 286.841 en 286 archivos |
| **LoC de pruebas en Lean** | 64.078 en 69 suites de pruebas |
| **Declaraciones demostradas** | 9.601 declaraciones theorem/lemma (cero sorry/axiom) |
| **Hardware objetivo** | Raspberry Pi 5 (BCM2712 / ARM Cortex-A76 / ARMv8-A) |
| **Auditoría canónica** | [`AUDIT_v0.29.0_COMPREHENSIVE`](../../../docs/dev_history/audits/AUDIT_v0.29.0_COMPREHENSIVE.md) — auditoría integral previa a 1.0 (202 hallazgos; remediados por WS-AK AK1–AK10; archivada) |
| **Última auditoría** | [`AUDIT_v0.30.11_COMPREHENSIVE`](../../../docs/audits/AUDIT_v0.30.11_COMPREHENSIVE.md) + [`AUDIT_v0.30.11_DEEP_VERIFICATION`](../../../docs/audits/AUDIT_v0.30.11_DEEP_VERIFICATION.md) — auditoría de preparación previa a 1.0 realizada tras el cierre de WS-AN (sucede a la ahora archivada [`AUDIT_v0.30.6_COMPREHENSIVE`](../../../docs/dev_history/audits/AUDIT_v0.30.6_COMPREHENSIVE.md), remediada por WS-AN AN0–AN12). WS-RC R0..R5 completados en v0.31.2; WS-RC R6..R14 absorbidos en WS-SM según el mapeo de absorción SM0.Q.1 (véase [`AUDIT_v0.30.11_WORKSTREAM_PLAN.md §15`](../../../docs/audits/AUDIT_v0.30.11_WORKSTREAM_PLAN.md)). Plan de flujo de trabajo activo: [`SMP_MULTICORE_COMPLETION_PLAN.md`](../../../docs/planning/SMP_MULTICORE_COMPLETION_PLAN.md). |
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
| [`docs/codebase_map.json`](../../../docs/codebase_map.json) — inventario legible por máquina | [`docs/REGISTERED_DEBT.md`](../../../docs/REGISTERED_DEBT.md) — historial de flujos de trabajo y hoja de ruta |
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
│        Platform  (Contract, Sim, RPi5)  ← production bindings        │
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
tests/                           Executable test suites + fixtures
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
| **Flujo de información** | Partición binaria alto/bajo | Política configurable de N dominios con frontera de aplicación de 43 entradas (recuento fijado por `enforcementBoundaryExtended_count`), demostraciones de no interferencia por operación, y un registro de auditoría controlado por capacidades para cada desclasificación autorizada |
| **Herencia de prioridad** | PIP implementado en C (rama MCS) | PIP transitivo verificado por máquina con libertad de interbloqueo y cota WCRT paramétrica |
| **Latencia acotada** | Sin cota WCRT formal | `WCRT = D × L_max + N × (B + P)` demostrada en 8 módulos de vivacidad |
| **Almacenes de objetos** | Listas enlazadas y arreglos | Tablas hash Robin Hood verificadas (`RHTable`/`RHSet`) con rutas críticas en O(1) |
| **Gestión de servicios** | No existe en el kernel | Orquestación de primera clase con grafo de dependencias y demostraciones de aciclicidad |
| **Demostraciones** | Isabelle/HOL, posteriores al hecho | Comprobador de tipos de Lean 4, ubicadas junto a las transiciones — cero sorry/axiom (recuento de declaraciones demostradas en la tabla [Estado actual](#estado-actual)) |
| **Plataforma** | HAL a nivel de C | Typeclass `PlatformBinding` con contratos de frontera tipados |

## Próximos pasos

El flujo de trabajo activo es **WS-SM** (finalización SMP multinúcleo), que
fusionó las fases de remediación restantes de WS-RC en el plan de fases
SM0–SM10 específico de SMP y se cierra en **v1.0.0** con un microkernel SMP
verificado y arrancable en Raspberry Pi 5. Las fases SM0–SM9 ya están
completadas: los tipos SMP fundacionales y la jerarquía de bloqueos, la puesta
en marcha SMP del HAL en Rust, las primitivas de bloqueo verificadas, los
bloqueos por objeto, el estado y la planificación del planificador por núcleo,
el IPC entre núcleos, el TLB shootdown y el mantenimiento de caché, el flujo
de información SMP, y la finalización de la desclasificación (SM9, cerrada en
v0.33.100). La fase restante es **SM10** (cierre de lanzamiento → v1.0.0). El
flujo de trabajo del ABI de retorno de llamadas al sistema (**WS-RA**) está
completo.

**SM10 está bloqueada por WS-RR** (preparación de lanzamiento SMP), la fase de remediación previa a 1.0 actualmente en curso ([`SMP_RELEASE_READINESS_PLAN.md`](../../../docs/planning/SMP_RELEASE_READINESS_PLAN.md)): RR0 (v0.34.26), RR1 (v0.34.41), RR2 (v0.34.42), RR3 (v0.34.43) y **RR4 — manejo de fallos: IPC de fallo completo con reinicio basado en respuesta (v0.34.44)**, que impide que un hilo con fallo se reanude en la instrucción que lo provocó: el fallo se registra en el TCB, se entrega al endpoint `faultHandler` del hilo a través de la cadena de llamada entre núcleos activa y se atiende con una respuesta que reinicia el hilo en un PC elegido o lo abandona. Quedan RR5–RR8 y luego **SM10** (cierre de lanzamiento → v1.0.0).

Plan maestro: [`SMP_MULTICORE_COMPLETION_PLAN.md`](../../../docs/planning/SMP_MULTICORE_COMPLETION_PLAN.md),
con planes por fase en `docs/planning/SMP_*.md`. El registro canónico por fase
— que incluye cada cartera de flujos de trabajo completada (WS-B a WS-AB,
WS-AE a WS-AN, WS-RC R0–R5, WS-RA) — es
[`docs/REGISTERED_DEBT.md`](../../../docs/REGISTERED_DEBT.md); las
auditorías previas y los cierres de hitos están archivados en
[`docs/dev_history/`](../../../docs/dev_history/README.md).

---

> Este documento es una traducción del [README en inglés](../../../README.md).
