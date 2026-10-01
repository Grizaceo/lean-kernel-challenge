# F4 — BLOQUEADO en la ejecución del envío formal

Fecha: 2026-09-30. Estado: **propuesta escrita, envío NO ejecutado**.
Commit: este archivo + el de la propuesta (`2325693`).

## Qué se intentó

Ejecutar la Prioridad 1 de `results/LKC_2026-09-30_F4_propuesta.md`: enviar
formalmente **polydisc** (`eidos-polydisc-baseline-v1`, run 274).

## Por qué quedó bloqueado

### Bloqueo 1 — el candidato no es trabajo nuestro

`eidos-polydisc-baseline-v1` (solutionId 289) es **byte-idéntico al ejemplo
oficial** del repo:

```
examples/polydisc/Submission.lean   sha256 8cf361a14699c741…
    def impl : Nat → Int := discSpec
    theorem impl_correct : ∀ n, impl n = discSpec n := fun _ => rfl
```

Es decir, la "primera entrada" que F4 proponía era enviar el archivo de ejemplo
de los organizadores como si fuera candidato propio. Eso no cumple el sentido de
la propuesta (presencia con trabajo propio) y contradice lo que F4 declaraba
para polydisc: la propuesta ya avisaba "no es un candidato optimizado", pero la
verificación manual revela que es peor: es literalmente el ejemplo oficial.

**Consecuencia:** la Prioridad 1 de F4 **queda anulada tal como está escrita**.
Enviar el ejemplo oficial no aporta nada y consume ladaily evaluation.

### Bloqueo 2 — el envelope del POST /submissions no es adivinable

El API existe y responde:

- `GET /submission-spec` → contrato completo (lee abajo).
- `POST /submissions` → `405 Method Not Allowed` en GET, `allow: POST`.
- El body debe ser "one valid JSON submission object".

Pero **el esquema del envelope no está documentado** en:
- el repo (`lean-kernel-challenge/`) — no hay cliente de submission formal,
  solo `scripts/lk_playground.py` que habla el **Playground**, no `/submissions`;
- las skills (`sair-competition`, `sair-competition-workflow`);
- `GET /submission-spec` (que da el *contrato de contenido*, no el del *envelope*).

Se probaron **9 formas** de envelope por `POST`, todas rechazadas con el mismo
`MALFORMED_BODY`:

```
{problemId, files{Submission.lean}, ruleAck}
{problemId, files[], ruleAck}
{problemId, source, ruleVersion, ruleAck}
{problem, files{}, ruleVersion}
{problemId, files{}}
{submission:{problemId, files}}
[ {problemId, files{}, contractVersion, ruleAck} ]      (array raíz)
{contractVersion, ruleAck, problemId, files[{path,content}]}
{contractVersion, ruleAck, problemId, source{Submission.lean}}
{contractVersion, ruleAck, problemId, paths{Submission.lean}}
```

Los objetos de retorno de `submissions/mine` muestran los campos que el
servidor ya calculó para una submission existente
(`contractVersion`, `manifestSha256`, `rawUploadSha256`,
`canonicalSourceTreeSha256`, `snapshotId`), lo que sugiere que el body lleva un
**manifest de hashes** que el cliente debe construir — pero su forma exacta no es
deducible del material disponible.

**El browser backend no está disponible** (`BU_CDP_URL unreachable`), así que no
se pudo inspeccionar la UI (`competition.sair.foundation`) que sí revelaría el
formulario de envío y por tanto el contrato del envelope.

## Por qué NO se forzó el envío

El pitfall histórico de LKC (runs 291/292, en las skills) es explícito: *"No
repetir el error de enviar mediante /submissions; usar /playground/* hasta elegir
una versión final"*. Además:

- `/submissions` es el judge **competitivo**: una submission consumptiona la
  evaluación diaria del problema y, por la regla *"última entrada gana"*, puede
  **reemplazar** una entrada existente (en polydisc no tenemos ninguna, pero el
  hábito de no disparar a ciegas aplica igual).
- Un `POST` a ciegas contra un endpoint de estado externo, con un envelope no
  verificado, es acción irreversible con riesgo de crear una submission basura
  que **sí** quedaría como última entrada.

Se decidió **no enviar** en lugar de adivinar el payload.

## Contrato de contenido (lo que SÍ está verificado)

De `GET /submission-spec`:

```json
{
  "contractVersion": "ddd9cae8db44a2ace1adea86e908263087aae499",
  "kind": "lean-kernel-package",
  "limits": { "maxPackageFiles": 1, "maxUploadBytes": 1048576 },
  "requiredSubmissionShape": {
    "functionName": "impl",
    "proofName": "impl_correct",
    "proofForm": "forall n, impl n = spec n"
  },
  "source": { "extensions": [".lean"], "requiredRoot": "Submission.lean" }
}
```

El `contractVersion` coincide con el de la sub-866 ya aceptada
(`ddd9cae8…`), confirmando que es el mismo contrato vigente.

## Lo que sí quedó hecho ( útil, sin riesgo)

- El candidato de **fib run 268** (`eidos-fib-fastdoubling-v1`) **sí** es trabajo
  nuestro y sigue siendo la mejor primera entrada real pendiente, siempre que se
  conozca el envelope.
- Se catalogaron todos los runs aceptados del Playground y se guardaron snapshots
  de API (`results/playground/api_runs_2026-09-30.json`,
  `results/leaderboards/api_2026-09-30.json`).

## Recomendación para desbloquear

1. **Conseguir el envelope del POST /submissions.** Opciones, en orden de
   coste:
   a. Inspeccionar la UI `competition.sair.foundation` con el browser (requiere
      el Chrome de automatización levantado).
   b. Zulip stream 24 "Lean Kernel Challenge" — preguntar el formato exacto del
      manifest / si hay un cliente oficial.
   c. Buscar el cliente en el upstream del repo (rama o release) — puede que el
      cliente viva fuera de `lean-kernel-challenge/`.
2. **Mientras tanto, no enviar nada.** La Prioridad 2 de F4 (fib run 268) queda
   como la primera entrada real en cola, lista para cuando el envelope esté
   conhecido.
3. **Reconsiderar polydisc**: si se quiere presencia en ese problema, hace falta
   un candidato **real** (no el ejemplo). Hoy no hay ninguno en `candidates/`.

## Corrección a F4

La propuesta F4 (`results/LKC_2026-09-30_F4_propuesta.md`) queda **corregida**
por este documento en dos puntos:
- Prioridad 1 (polydisc run 274) **anulada**: es el ejemplo oficial, no trabajo
  nuestro.
- Se añade el bloqueo operativo del envío formal por envelope desconocido.