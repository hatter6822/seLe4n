<!-- Traducción al español del README de seLe4n -->

🌐 [English](../../../README.md) | [简体中文](../zh-CN/README.md) | **Español** | [日本語](../ja/README.md) | [한국어](../ko/README.md) | [العربية](../ar/README.md) | [Français](../fr/README.md) | [Português](../pt-BR/README.md) | [Русский](../ru/README.md) | [Deutsch](../de/README.md) | [हिन्दी](../hi/README.md)

<p align="center">
  <picture>
    <source media="(prefers-color-scheme: dark)" srcset="../../../assets/logo_dark.png" />
    <img src="../../../assets/logo.png" alt="seLe4n logo" width="200" />
  </picture>
</p>

<p align="center">
  <a href="https://github.com/hatter6822/seLe4n/actions/workflows/lean_action_ci.yml"><img src="https://github.com/hatter6822/seLe4n/actions/workflows/lean_action_ci.yml/badge.svg?branch=main" alt="CI" /></a>
  <a href="https://github.com/hatter6822/seLe4n/actions/workflows/platform_security_baseline.yml"><img src="https://github.com/hatter6822/seLe4n/actions/workflows/platform_security_baseline.yml/badge.svg" alt="Security" /></a>
  <img src="https://img.shields.io/badge/version-0.20.3-blue" alt="Version" />
  <img src="https://img.shields.io/badge/Lean-v4.28.0-blueviolet" alt="Lean 4" />
  <a href="../../../LICENSE"><img src="https://img.shields.io/badge/license-GPLv3-blue" alt="License" /></a>
</p>

<p align="center">
  Un microkernel escrito en Lean 4 con demostraciones verificadas por máquina (machine-checked proofs),
  inspirado en la arquitectura de <a href="https://sel4.systems">seL4</a>. Primer objetivo de hardware:
  <strong>Raspberry Pi 5</strong>.
</p>

---

## ¿Qué es seLe4n?

seLe4n es un microkernel construido desde cero en Lean 4. Cada transición del
núcleo (kernel transition) es una función pura ejecutable. Cada invariante
(invariant) es verificado por el comprobador de tipos de Lean — cero `sorry`,
cero `axiom`. Toda la superficie de demostraciones (proof surface) compila a
código nativo sin pruebas admitidas.

El proyecto utiliza un modelo de seguridad basado en capacidades (capability-based
security) e introduce mejoras arquitectónicas novedosas en comparación con otros
microkernels:

- **Rutas críticas del núcleo en O(1) basadas en hash** — todos los almacenes de objetos, colas de ejecución, ranuras de CNode, mapeos de VSpace y colas de IPC utilizan `RHTable`/`RHSet` (tabla hash Robin Hood con invariantes verificados por máquina, cero `Std.HashMap`/`Std.HashSet` en el estado)
- **Capa de orquestación de servicios (service orchestration)** para la gestión del ciclo de vida de componentes y dependencias, con semántica determinista de fallo parcial
- **Árbol de derivación de capacidades (capability derivation tree) estable por nodo** con índices `childMap` + `parentMap` en RHTable para transferencia de ranuras, revocación, consulta de padres y recorrido de descendientes en O(1)
- **IPC de doble cola intrusiva (intrusive dual-queue IPC)** con enlaces `queuePrev`/`queuePPrev`/`queueNext` por hilo para encolado, desencolado y eliminación en medio de la cola en O(1)
- **Marco de flujo de información parametrizado de N dominios (N-domain information-flow)** con políticas de flujo configurables, generalizando las etiquetas heredadas de confidencialidad/integridad (más allá de la partición binaria de seL4)
- **Planificación EDF + prioridad (EDF + priority scheduling)** con semántica de desencolar-al-despachar (dequeue-on-dispatch), contexto de registros por TCB con cambio de contexto en línea, `RunQueue` con agrupamiento por prioridad y particionamiento por dominio

## Estado actual

| Atributo | Valor |
|----------|-------|
| **Versión** | `0.18.6` |
| **Toolchain de Lean** | `v4.28.0` |
| **LoC de producción en Lean** | 55.732 en 98 archivos |
| **LoC de pruebas en Lean** | 7.317 en 10 suites de pruebas |
| **Declaraciones demostradas** | 1.692 declaraciones de teorema/lema (theorem/lemma) (cero sorry/axiom) |
| **Hardware objetivo** | Raspberry Pi 5 (BCM2712 / ARM Cortex-A76 / ARMv8-A) |
| **Última auditoría** | [`AUDIT_COMPREHENSIVE_v0.17.13_PRE_RELEASE.md`](../../../docs/dev_history/audits/AUDIT_COMPREHENSIVE_v0.17.13_PRE_RELEASE.md) — Auditoría completa pre-lanzamiento del núcleo y código Rust |
| **Mapa del código** | [`docs/codebase_map.json`](../../../docs/codebase_map.json) — inventario de declaraciones legible por máquina |

Las métricas se derivan del código fuente mediante `./scripts/generate_codebase_map.py`
y se almacenan en [`docs/codebase_map.json`](../../../docs/codebase_map.json) bajo la
clave `readme_sync`. Para actualizar toda la documentación de forma conjunta, utilice
`./scripts/report_current_state.py` como verificación cruzada.

## Inicio rápido

```bash
./scripts/setup_lean_env.sh   # instalar el toolchain de Lean
lake build                     # compilar todos los módulos
lake exe sele4n                # ejecutar el arnés de trazas (trace harness)
./scripts/test_smoke.sh        # validar (higiene + compilación + trazas + estado negativo + sincronización de docs)
```

## Ruta de incorporación

¿Nuevo en el proyecto? Siga este orden de lectura:

1. **Este README** — identidad del proyecto, arquitectura y estructura del código fuente
2. [`docs/DEVELOPMENT.md`](../../../docs/DEVELOPMENT.md) — flujo de trabajo diario, ciclo de validación, lista de verificación para PRs
3. [`docs/gitbook/README.md`](../../../docs/gitbook/README.md) — manual completo (arquitectura en profundidad, demostraciones, ruta de hardware)
4. [`docs/codebase_map.json`](../../../docs/codebase_map.json) — inventario de módulos y declaraciones legible por máquina

Para la planificación y el historial de flujos de trabajo (workstreams), consulte [`docs/WORKSTREAM_HISTORY.md`](../../../docs/WORKSTREAM_HISTORY.md).

## Documentación del proyecto

| Documento | Propósito |
|-----------|-----------|
| [`docs/spec/SELE4N_SPEC.md`](../../../docs/spec/SELE4N_SPEC.md) | Especificación del proyecto e hitos |
| [`docs/spec/SEL4_SPEC.md`](../../../docs/spec/SEL4_SPEC.md) | Semántica de referencia de seL4 |
| [`docs/DEVELOPMENT.md`](../../../docs/DEVELOPMENT.md) | Flujo de trabajo diario, ciclo de validación, lista de verificación para PRs |
| [`docs/TESTING_FRAMEWORK_PLAN.md`](../../../docs/TESTING_FRAMEWORK_PLAN.md) | Niveles de prueba y contrato de CI |
| [`docs/WORKSTREAM_HISTORY.md`](../../../docs/WORKSTREAM_HISTORY.md) | Historial completo de flujos de trabajo, hoja de ruta e índice de auditorías |
| [`docs/gitbook/README.md`](../../../docs/gitbook/README.md) | Manual completo (arquitectura, diseño, demostraciones, ruta de hardware) |
| [`docs/codebase_map.json`](../../../docs/codebase_map.json) | Inventario del código fuente legible por máquina (sincronizado con el README) |
| [`CONTRIBUTING.md`](../../../CONTRIBUTING.md) | Mecánica de contribución y requisitos de PRs |
| [`CHANGELOG.md`](../../../CHANGELOG.md) | Historial de versiones |

## Comandos de validación

```bash
./scripts/test_fast.sh      # Nivel 0 + Nivel 1 (higiene + compilación, profundidad semántica de pruebas L-08)
./scripts/test_smoke.sh     # + Nivel 2 (trazas + estado negativo + sincronización de docs)
./scripts/test_full.sh      # + Nivel 3 (anclajes de superficie de invariantes + verificación #check de Lean)
NIGHTLY_ENABLE_EXPERIMENTAL=1 ./scripts/test_nightly.sh  # + Nivel 4 (determinismo nocturno)
```

Ejecute al menos `test_smoke.sh` antes de cualquier PR. Ejecute `test_full.sh`
cuando modifique teoremas (theorems), invariantes (invariants) o anclajes de
documentación.

## Arquitectura

seLe4n está organizado como contratos por capas, cada uno con transiciones
ejecutables y demostraciones de preservación de invariantes verificadas por
máquina (machine-checked invariant preservation proofs):

```
┌──────────────────────────────────────────────────────────────────────┐
│                 Kernel API  (SeLe4n/Kernel/API.lean)                 │
├──────────────┬─────────────┬────────────┬───────────┬────────────────┤
│   Scheduler  │  Capability │    IPC     │ Lifecycle │  Service (ext) │
│  RunQueue    │  CSpace/CDT │  DualQueue │  Retype   │  Orchestration │
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

Cada subsistema del núcleo sigue la separación **Operations/Invariant**: las
transiciones residen en `Operations.lean` y las demostraciones en `Invariant.lean`.
El `apiInvariantBundle` unificado agrega todos los invariantes de subsistema en
una sola obligación de prueba.

## Comparación con seL4

| Característica | seL4 | seLe4n |
|----------------|------|--------|
| **Mecanismo de IPC** | Cola de endpoint con lista enlazada simple | IPC de doble cola intrusiva (intrusive dual-queue) con punteros `queuePPrev` para eliminación en medio de la cola en O(1) |
| **Flujo de información (information flow)** | Partición binaria alto/bajo | Política de flujo configurable de N dominios (generaliza etiquetas heredadas de confidencialidad x integridad) |
| **Gestión de servicios** | No existe en el núcleo | Orquestación de servicios (service orchestration) de primera clase con grafo de dependencias y detección de ciclos por DFS |
| **Derivación de capacidades (capability derivation)** | CDT con lista enlazada de hijos | HashMap `childMap` para consulta de hijos en O(1) |
| **Planificador (scheduler)** | Cola de prioridad plana | `RunQueue` con agrupamiento por prioridad, seguimiento en línea de `maxPriority` y EDF |
| **VSpace** | Tablas de páginas del hardware | `HashMap VAddr (PAddr x PagePermissions)` con imposición de W^X |
| **Metodología de pruebas (proof methodology)** | Isabelle/HOL, posterior al hecho | Comprobador de tipos de Lean 4, demostraciones ubicadas junto a las transiciones |
| **Abstracción de plataforma** | HAL a nivel de C | Typeclass `PlatformBinding` con contratos de frontera tipados |

## Próximos pasos

Las prioridades actuales y el historial completo de flujos de trabajo se mantienen en
[`docs/WORKSTREAM_HISTORY.md`](../../../docs/WORKSTREAM_HISTORY.md). Resumen:

- **WS-R** — Remediación integral de auditoría (Comprehensive Audit Remediation) (8 fases, R1–R8, 111 sub-tareas). Aborda los 82 hallazgos de [`AUDIT_COMPREHENSIVE_v0.17.13_PRE_RELEASE.md`](../../../docs/dev_history/audits/AUDIT_COMPREHENSIVE_v0.17.13_PRE_RELEASE.md). R1–R7 completas (v0.18.0–v0.18.6), R8 pendiente. Plan: [`AUDIT_v0.17.14_WORKSTREAM_PLAN.md`](../../../docs/dev_history/audits/AUDIT_v0.17.14_WORKSTREAM_PLAN.md).
- **Vinculación con hardware Raspberry Pi 5** — recorrido de tablas de páginas ARMv8, enrutamiento de interrupciones GIC-400, secuencia de arranque (boot) (los contratos de plataforma RPi5 ya son sustantivos gracias a WS-H15)

Los portafolios anteriores (WS-B a WS-Q) están todos completos. Las auditorías
previas (v0.8.0–v0.9.32), los cierres de hitos y los capítulos heredados de
GitBook están archivados en [`docs/dev_history/`](../../../docs/dev_history/README.md).

---

> Este documento es una traducción de [English README](../../../README.md).
