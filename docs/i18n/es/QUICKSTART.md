<!-- Traducción al español de la guía de inicio rápido de seLe4n -->

🌐 [English](../../../README.md#quick-start) | [简体中文](../zh-CN/QUICKSTART.md) | **Español** | [日本語](../ja/QUICKSTART.md) | [한국어](../ko/QUICKSTART.md) | [العربية](../ar/QUICKSTART.md) | [Français](../fr/QUICKSTART.md) | [Português](../pt-BR/QUICKSTART.md) | [Русский](../ru/QUICKSTART.md) | [Deutsch](../de/QUICKSTART.md) | [हिन्दी](../hi/QUICKSTART.md)

# Guía de inicio rápido

Esta guía le ayudará a configurar el entorno de desarrollo de seLe4n, compilar
el proyecto y ejecutar las pruebas de validación. seLe4n es un microkernel
orientado a producción escrito en Lean 4 con demostraciones verificadas por
máquina (machine-checked proofs), cuyo objetivo de hardware es el
**Raspberry Pi 5**.

## Prerrequisitos

- **Sistema operativo**: Linux (recomendado) o macOS
- **Git**: para clonar el repositorio
- **curl**: necesario para el instalador del toolchain de Lean (`elan`)
- **Conexión a Internet**: para descargar el toolchain de Lean y las dependencias de Lake

No necesita instalar Lean manualmente; el script de configuración se encarga de
todo mediante `elan` (el gestor de versiones de Lean).

## Paso 1: Clonar el repositorio

```bash
git clone https://github.com/hatter6822/seLe4n.git
cd seLe4n
```

## Paso 2: Configurar el entorno

El script de configuración instala `elan` (si no está presente) y configura el
toolchain de Lean v4.28.0:

```bash
./scripts/setup_lean_env.sh
```

Para omitir las dependencias de prueba (shellcheck, ripgrep) y solo configurar
el toolchain de Lean:

```bash
./scripts/setup_lean_env.sh --skip-test-deps
```

Después de la configuración, cargue el entorno:

```bash
source ~/.elan/env
```

## Paso 3: Compilar el proyecto

```bash
lake build
```

Esto compila todos los módulos del núcleo (kernel), las demostraciones
(proofs) y los ejecutables de prueba. La primera compilación puede tardar
varios minutos ya que descarga las dependencias de Lake y compila todo el
árbol de fuentes.

## Paso 4: Ejecutar el arnés de trazas

```bash
lake exe sele4n
```

Esto ejecuta el arnés de trazas principal (main trace harness), que demuestra
las transiciones del núcleo — planificación (scheduling), IPC, gestión de
capacidades (capability management), ciclo de vida (lifecycle), flujo de
información (information flow) y operaciones de servicio (service operations)
— con salida detallada de cada paso.

## Paso 5: Validar

Ejecute la suite de pruebas de humo (smoke tests) para verificar que todo
funciona correctamente:

```bash
./scripts/test_smoke.sh
```

## Niveles de prueba

seLe4n utiliza un sistema de pruebas escalonado con cuatro niveles:

| Nivel | Comando | Qué valida |
|-------|---------|------------|
| **Nivel 0 + 1** | `./scripts/test_fast.sh` | Higiene del código + compilación completa |
| **Nivel 0–2** | `./scripts/test_smoke.sh` | + Trazas de ejecución + pruebas de estado negativo + sincronización de documentación |
| **Nivel 0–3** | `./scripts/test_full.sh` | + Anclajes de superficie de invariantes (invariant surface anchors) + verificación `#check` de Lean |
| **Nivel 0–4** | `NIGHTLY_ENABLE_EXPERIMENTAL=1 ./scripts/test_nightly.sh` | + Pruebas de determinismo nocturnas |

**Recomendación:** ejecute al menos `test_smoke.sh` antes de cualquier pull
request. Ejecute `test_full.sh` cuando modifique teoremas (theorems),
invariantes (invariants) o anclajes de documentación.

## Compilación de módulos específicos

Antes de confirmar (commit) cualquier archivo `.lean`, verifique que el módulo
específico compila correctamente. El objetivo por defecto de `lake build` solo
compila los módulos accesibles desde `Main.lean`, así que los módulos no
importados podrían pasar silenciosamente incluso con errores:

```bash
source ~/.elan/env && lake build <Ruta.Del.Modulo>
```

Ejemplo:

```bash
lake build SeLe4n.Kernel.Scheduler.Operations.Core
```

## Arquitectura en breve

seLe4n está organizado como contratos por capas. Cada subsistema del núcleo
sigue la separación **Operations/Invariant**: las transiciones residen en
`Operations.lean` y las demostraciones en `Invariant.lean`.

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

Los subsistemas principales son:

- **Scheduler (planificador)**: planificación EDF + prioridad con `RunQueue` agrupada por prioridad y particionamiento por dominio
- **Capability (capacidades)**: espacio de capacidades CSpace, árbol de derivación CDT, operaciones mint/copy/move/delete/revoke
- **IPC**: comunicación entre procesos mediante doble cola intrusiva (intrusive dual-queue) con eliminación en O(1)
- **Lifecycle (ciclo de vida)**: creación y destrucción de objetos del núcleo mediante retype
- **Service (servicios)**: orquestación de componentes con grafo de dependencias
- **Information Flow (flujo de información)**: etiquetas de seguridad de N dominios con demostraciones de no interferencia (non-interference)

## Documentación adicional

| Recurso | Descripción |
|---------|-------------|
| [`README.md`](README.md) | README completo en español |
| [`docs/DEVELOPMENT.md`](../../../docs/DEVELOPMENT.md) | Flujo de trabajo diario y lista de verificación para PRs |
| [`docs/gitbook/README.md`](../../../docs/gitbook/README.md) | Manual completo del proyecto |
| [`docs/spec/SELE4N_SPEC.md`](../../../docs/spec/SELE4N_SPEC.md) | Especificación del proyecto |
| [`docs/WORKSTREAM_HISTORY.md`](../../../docs/WORKSTREAM_HISTORY.md) | Historial de flujos de trabajo (workstreams) y hoja de ruta |

## Resolución de problemas

**El script de configuración falla al descargar `elan`:**
Asegúrese de tener `curl` instalado y conexión a Internet. Verifique que su
firewall no bloquee las descargas desde GitHub.

**`lake build` falla con errores de dependencias:**
Ejecute `lake update` para actualizar las dependencias y luego intente
`lake build` de nuevo.

**Las pruebas fallan con "command not found" para `shellcheck` o `rg`:**
Ejecute `./scripts/setup_lean_env.sh` sin la opción `--skip-test-deps` para
instalar las dependencias de prueba.

---

> Este documento es una traducción de [English README](../../../README.md).
