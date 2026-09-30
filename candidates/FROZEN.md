# FROZEN — línea DP con listas (2026-09-30)

Queda **congelada** la línea de DP con listas: `partition-euler`, `partition-euler-cons`,
`partition-stream*` y los sieves basados en recursión. No se escriben más pruebas sobre
ellos.

## Por qué

El bloqueo ya no es *solo* la métrica ni un "piso de 168M" (ese era artefacto de
instrumento; véase `../ERRATA.md`). Es la **estructura**: cada paso de recursión
estructural elabora a `brecOn`/`Nat.rec` y el kernel cobra por iteración, no por
operación. Medido (covariante con instrumento, razón 4.349× reproducida):

| candidato | ops | instr (n=32) |
|---|---:|---:|
| `partition-foldl` | 3.577 | 4,03 B |
| `partition-euler` | 290   | 927 M |

La razón (4.35×) **sí** favorece a la recurrencia dispersa, y todavía con `impl_correct`
falta — `partition-euler` quedó DEAD-END documentado (`ccf09e6`) porque la identidad
pentagonal contra `partAux m m` no cierra con `rfl` ni con una regla de reescritura
local. Ese es el muro, no la métrica. Cualquier reintento tiene que venir con una prueba
nueva y con el muro identificado — no con otra optimización del DP.

Los sieves **sí** están permitidos para seguir (F3) porque su cuellocuello medido ya no
es la recursión estructural sino `count`: la recurrencia exterior son ≤~24 iteraciones
y el resto es un `m &&{ & } ; (m-1)` por bit encendido. Eso sí admite cambio de paradigma
sin Euler.

## Congelados (`candidates/`)

- `partition-euler/` — DEAD-END formal (commit `ccf09e6`)
- `partition-euler-cons/` — scaffold, sorries etiquetados (commit `9120fcb`)
- `partition-stream/` y `partition-stream-addblocks/` — sub-866, **fallback activo**
  pero no iterar; masa congelada a falta de nueva idea

Fin de FROZEN: cualquier modificación requiere un motivo nuevo y citarlo aquí.
