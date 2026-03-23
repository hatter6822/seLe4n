<!-- Traducción al español de CONTRIBUTING.md de seLe4n -->

🌐 [English](../../../CONTRIBUTING.md) | [简体中文](../zh-CN/CONTRIBUTING.md) | **Español** | [日本語](../ja/CONTRIBUTING.md) | [한국어](../ko/CONTRIBUTING.md) | [العربية](../ar/CONTRIBUTING.md) | [Français](../fr/CONTRIBUTING.md) | [Português](../pt-BR/CONTRIBUTING.md) | [Русский](../ru/CONTRIBUTING.md) | [Deutsch](../de/CONTRIBUTING.md) | [हिन्दी](../hi/CONTRIBUTING.md)

# Contribuir a seLe4n

Gracias por contribuir a seLe4n — un microkernel orientado a producción escrito
en Lean 4 con demostraciones verificadas por máquina (machine-checked proofs).

## Licencia

seLe4n está licenciado bajo la [Licencia Pública General de GNU v3.0 o posterior](../../../LICENSE).
Al enviar un pull request o contribuir código a este proyecto, usted acepta que
sus contribuciones se licencien bajo la misma licencia GPL-3.0 o posterior.
También certifica que tiene el derecho de enviar la contribución bajo esta licencia.

## Ruta del colaborador en 5 minutos

1. **Flujo de trabajo y estándares:** [`docs/DEVELOPMENT.md`](../../../docs/DEVELOPMENT.md)
2. **Niveles de prueba:** [`docs/TESTING_FRAMEWORK_PLAN.md`](../../../docs/TESTING_FRAMEWORK_PLAN.md)
3. **Política de CI:** [`docs/CI_POLICY.md`](../../../docs/CI_POLICY.md)
4. **Alcance del proyecto y flujos de trabajo (workstreams):** [`docs/spec/SELE4N_SPEC.md`](../../../docs/spec/SELE4N_SPEC.md)
5. **Hallazgos de auditoría activos:** [`docs/audits/AUDIT_COMPREHENSIVE_v0.18.7_PRE_BENCHMARK.md`](../../../docs/audits/AUDIT_COMPREHENSIVE_v0.18.7_PRE_BENCHMARK.md)
6. **Historial de flujos de trabajo (workstream history):** [`docs/WORKSTREAM_HISTORY.md`](../../../docs/WORKSTREAM_HISTORY.md)

Manual completo: [`docs/gitbook/README.md`](../../../docs/gitbook/README.md)

## Validación obligatoria antes de abrir un PR

```bash
./scripts/test_smoke.sh     # puerta mínima (Nivel 0-2)
./scripts/test_full.sh      # obligatorio para cambios en teoremas/invariantes (Nivel 0-3)
```

Ejecute siempre al menos `test_smoke.sh` antes de enviar cualquier pull request.
Si sus cambios afectan teoremas (theorems), invariantes (invariants) o anclajes
de documentación, ejecute `test_full.sh`.

## Requisitos para Pull Requests

- Identifique el/los ID(s) de flujo de trabajo (workstream) que se avanzan
- Mantenga el alcance en un fragmento coherente
- Las transiciones deben ser deterministas (éxito/fallo explícito)
- Las actualizaciones de invariantes (invariants) y teoremas (theorems) deben acompañar los cambios de implementación
- Sincronice la documentación en el mismo PR
- Consulte la lista de verificación completa en [`docs/DEVELOPMENT.md`](../../../docs/DEVELOPMENT.md)

## Compilación de módulos

Antes de confirmar (commit) cualquier archivo `.lean`, debe verificar que el
módulo específico compila correctamente:

```bash
source ~/.elan/env && lake build <Ruta.Del.Modulo>
```

Por ejemplo, si modificó `SeLe4n/Kernel/IPC/Operations/Endpoint.lean`:

```bash
lake build SeLe4n.Kernel.IPC.Operations.Endpoint
```

**`lake build` (objetivo por defecto) no es suficiente.** El objetivo por defecto
solo compila los módulos accesibles desde `Main.lean` y los ejecutables de prueba.
Los módulos que aún no están importados por el núcleo principal pasarán
silenciosamente `lake build` incluso con demostraciones rotas.

## Convenciones clave

- **Separación Operations/Invariant**: cada subsistema del núcleo tiene `Operations.lean` (transiciones) e `Invariant.lean` (demostraciones). Mantenga esta separación.
- **Sin axiom/sorry**: prohibido en la superficie de demostraciones de producción.
- **Semántica determinista**: todas las transiciones devuelven éxito/fallo explícito. Nunca introduzca ramas no deterministas.
- **Identificadores tipados**: `ThreadId`, `ObjId`, `CPtr`, `Slot`, `DomainId`, etc. son estructuras envolventes (wrappers), no alias de `Nat`. Use `.toNat`/`.ofNat` de forma explícita.

## Comandos de validación completos

```bash
./scripts/test_fast.sh      # Nivel 0 + Nivel 1 (higiene + compilación)
./scripts/test_smoke.sh     # + Nivel 2 (trazas + estado negativo + sincronización de docs)
./scripts/test_full.sh      # + Nivel 3 (anclajes de superficie de invariantes)
NIGHTLY_ENABLE_EXPERIMENTAL=1 ./scripts/test_nightly.sh  # + Nivel 4 (determinismo nocturno)
```

---

> Este documento es una traducción de [English CONTRIBUTING.md](../../../CONTRIBUTING.md).
