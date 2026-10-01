# F4 — Propuesta de presencia en el tablero (NO EJECUTAR sin OK)

Fecha: 2026-09-30. Datos de la API pública de SAIR (leaderboard + playground/runs),
consultados el 2026-09-30. Equipo `LKC01-T00215`.

## 0. Hallazgo que reencuadra la propuesta

**Tenemos UNA sola entrada formal en todo el tablero**: `LKC01-T00215` aparece
únicamente en **partition, rank 24/29, computationTotal 5,386,432,876** (la
submission 866). En los otros siete problemas **no tenemos ninguna entrada**.

Además, un mismo equipo (`LKC01-T00096`) ocupa rank 2 en casi todos los problemas
(partition 1,451,375 = rank 2; primecount rank 4; mertens rank 2; fib rank 2;
permanent rank 2; polydisc rank 2; ca-rule110 rank 3; sha256 rank 5). El líder de
partition (1,440,816) es otro equipo. La pictured de puntuación muestra que el
puesto 1–5 está en el orden de 1.4M–1.5M para partition/primecount/mertens.

Consecuencia táctica: **cualquier envío formal nuevo es una primera entrada en su
problema**, no una mejora de una existente. No se arriesga una posición ganada
(solo importa partition, donde ya somos 24 y donde el prompt advierte que se
toma la **última** entrada — un envío peor que 5.386B en partition sería
retrocededor).

## 1. Candidatos aceptados en Playground (métrica calibrada, `kernel-replay-v2`)

Fuente: `GET /competitions/lean-kernel-challenge/playground/runs?limit=100`
(23 runs, 19 aceptados). `metrics.official = false`, `scoreable = false` en todos:
son runs de práctica, 3 slots (1 por grupo), **no 6 slots**.

| run | problema | solution | median (instr) | suma 3 slots | full-closure replay | created |
|---:|---|---|---:|---:|---:|---|
| 335 | ca-rule110 | ca-rule110-v3-unrolled-init | 177,765,670 | 527,625,307 | 3,993,085,503 | 09-28 |
| 315 | ca-rule110 | eidos-ca-rule110-v2-v1 | 290,325,903 | 866,130,247 | 3,905,188,427 | 09-28 |
| 314 | permanent | eidos-permanent-tbl-v1 | 23,415,456,005 | 25,671,771,273 | 5,536,824,590 | 09-28 |
| 297 | permanent | eidos-perm-proof-r1 | 23,910,282,522 | 26,146,550,116 | 5,505,735,620 | 09-26 |
| 293 | ca-rule110 | eidos-carule110-v2-…-v2 | 290,491,347 | 865,813,783 | 3,906,653,413 | 09-26 |
| 290 | partition | eidos-partition-proven-v1 | 3,698,796,426 | 5,733,628,769 | 1,964,066,213 | 09-26 |
| 280 | mertens | eidos-mertens-official-0ffe2d | 1,909,405,770 | 2,483,721,600 | 9,400,743,517 | 09-25 |
| 279 | sha256 | eidos-sha256-official-9cdaa1 | 85,421,102,974 | 91,427,595,127 | 379,483,938 | 09-25 |
| 278 | primecount | eidos-primecount-official-c0b4ee | 1,730,280,122 | 2,129,799,630 | 2,699,376,698 | 09-25 |
| 277 | ca-rule110 | eidos-ca-rule110-official-v1 | 361,417,926 | 1,079,552,318 | 3,632,330,813 | 09-25 |
| 276 | sha256 | eidos-sha256-baseline-v1 | 85,467,515,599 | 91,473,831,233 | 379,454,562 | 09-25 |
| 275 | ca-rule110 | eidos-ca-rule110-baseline-v1 | 65,521,889,306 | 115,075,915,674 | 287,036,722 | 09-25 |
| 274 | polydisc | eidos-polydisc-baseline-v1 | 2,416,888,060 | 5,166,429,454 | 332,802,104 | 09-25 |
| 273 | permanent | eidos-permanent-baseline-v1 | 131,722,107,083 | 141,387,931,703 | 292,020,561 | 09-25 |
| 272 | partition | eidos-partition-baseline-v1 | 3,692,491,727 | 5,722,742,022 | 1,964,805,847 | 09-25 |
| 271 | primecount | eidos-primecount-baseline-v1 | 1,729,320,902 | 2,196,858,729 | 4,962,456,854 | 09-25 |
| 270 | mertens | eidos-mertens-baseline-v1 | 2,014,946,562 | 2,586,138,713 | 7,329,400,114 | 09-25 |
| **269** | **fib** | **official-fd-example** | **11,531,540** | **28,824,742** | 2,355,577,701 | 09-25 |
| 268 | fib | eidos-fib-fastdoubling-v1 | 17,714,019 | 45,610,764 | 2,053,110,909 | 09-25 |

Corrección por problema sobre los baselines (comparación pareada, mismo judge inputs):
- ca-rule110 run 293 vs 275: **0.80×** (1.245× menos instrucciones).
- ca-rule110 run 335 vs 293: 527.6M/866.1M = **0.61×** (1.64× mejor que v2).

## 2. Traducción a `computationTotal` oficial (6 slots)

El Playground mide **3 slots** (1 por grupo, `casesPerGroup: 1`); el plan oficial
mide **6 slots** (2 por grupo, `casesPerGroup: 2`). Calibración empírica con el
único par comparable que tenemos — **partition run 272** (practice, 3 slots,
suma 5,722,742,022) contra **submission 866** (formal, 6 slots,
computationTotal 5,386,432,876):

```
factor = practice_sum_3slots / formal_total_6slots = 5.722742.022 / 5.386432.876 = 1.064
```

El practice usa los **endpoints** del rango (más caro) y el formal aplica jitter
hacia adentro; por eso el practice de 3 slots es apenas **1.064×** el formal de
6 slots (no 2×): los 3 casos de practice son los máximos de su grupo.

| problema | run base | est. formal 6 slots | líder | gap | rank proyectado | ranked |
|---|---:|---:|---:|---:|---:|---:|
| **polydisc** | 274 | 4,855,666,780 | 1,232,702,959 | **3.9×** | **11/20** | 20 |
| **fib** | 269 | 27,090,923 | 6,995,749 | **3.9×** | **14/30** | 30 |
| sha256 | 279 | 85,928,190,909 | 9,374,502,160 | 9.2× | 15/22 | 22 |
| ca-rule110 | 335 | 495,888,446 | 3,431,678 | 145× | 19/26 | 26 |
| permanent | 314 | 24,127,604,580 | 51,377,014 | 470× | 18/24 | 24 |
| primecount | 278 | 2,001,691,382 | 1,443,590 | 1.387× | 16/21 | 21 |
| mertens | 280 | 2,334,324,812 | 1,555,053 | 1.501× | 15/20 | 20 |
| partition | 272 | 5,378,516,938 | 1,440,816 | 3.733× | (ya somos 24) | 29 |

**Advertencia metodológica**: el factor 1.064 está calibrado en un solo problema
(partition, cuya curva crece rápido con n). Para problemas con curva plana
(fib, polydisc) la práctica sobreestima más, y para problemas con jitter relativo
distinto puede desviarse ±20%. Los rangos proyectados son **indicativos**, no
cálculo exacto; el único número con factor verificado es partition.

## 3. Propuesta concreta (requiere OK explícito; nada se ha enviado)

Criterio: maximizes presencia sin arriesgar nada. Como no tenemos entrada en
ninguno de los siete, todo envío es una primera entrada. Se **no** propone enviar
nada en partition (ya somos rank 24 y el prompt advierte que se queda con la
última entrada; enviar el baseline 5.38B no mejora nada y podría empeorar por
jitter distinto).

### Prioridad 1 — polydisc, run 274 (`eidos-polydisc-baseline-v1`)

- Gap al líder **3.9×**, el menor de los ocho.
- Rank proyectado **11 de 20** — el mejor puesto alcanzable de cualquier envío.
- Es el baseline, no trabajo derivado nuestro: aceptable como primera entrada,
  pero conviene aclarar que no es un candidato optimizado.
- Riesgo: bajo. No tenemos nada que perder en polydisc.
- **Recomendación: enviar.**

### Prioridad 2 — fib, run 269 (`official-fd-example`)

- Gap **3.9×**. Rank proyectado **14 de 30**.
- Pero `official-fd-example` **no es nuestro**: es el ejemplo del repo. Enviarlo
  como entrada formal sería enviar código de terceros como propio.
  La alternativa propia es **run 268** (`eidos-fib-fastdoubling-v1`, 45,610,764
  en 3 slots → est. 42,875,000 formal), gap 6.1×, rank proyectado ~20/30.
- **Recomendación: enviar run 268 (propio), no el ejemplo oficial.** El ejemplo
  puede consultarse como referencia pero no se presenta como candidato nuestro.

### Prioridad 3 — ca-rule110, run 335 (`ca-rule110-v3-unrolled-init`)

- Gap 145×, rank proyectado 19/26.
- Es nuestro mejor desarrollo relativo (0.61× del v2, 0.005× del baseline), pero
  el problema tiene muchos equipos por encima; entrar en 19 no aporta ranking
  agregado nuevo porque ya estamos fuera del top.
- **Recomendación: enviar solo si hay tiempo de sobra; no es prioritario.**

### No enviar ahora

- permanent (rank 18/24, gap 470×) — solo si aparece una mejora real.
- sha256 (rank 15/22) — mismo caso.
- primecount / mertens — F3 acaba de cerrar negativo para primecount; no reenviar
  el mismo código.

## 4. Orden de ejecución propuesto (con OK)

1. **polydisc run 274** → primera entrada, rank ~11/20.
2. **fib run 268** (`eidos-fib-fastdoubling-v1`) → primera entrada, rank ~20/30.
3. Opcional: ca-rule110 run 335 si se desea cobertura de un tercer problema.

Cada envío debe hacerse **uno por día** (hay 1 evaluación diaria por problema y
el panel muestra `dailyEvaluation` por fecha), y solo con OK explícito del
coordinador. Nada se ha enviado.

## 5. Riesgo de la regla "última entrada gana"

Aplicado a este plan: en los siete problemas.propuestos **no tenemos entrada
previa**, así que enviar no destruye nada. En partition **no se envía nada**.
Por tanto la regla "última entrada formal" no juega en contra en esta propuesta.
Si más adelante se envía una versión mejorada de un problema ya enviado, esa
versión debe ser estrictamente mejor que la anterior, porque la anterior se
pierde.

## 6. Nota de estrategia a medio plazo

El dato más informative de la tabla es que **tres problemas (polydisc, fib,
sha256) están a <10× del líder**, mientras partition/primecount/mertens están a
>1000×. F3 mató el enfoque de primecount (criba bit-packed: 25.0B local, no pasa
4.3M). El_error_ de effort debería ir a **fib** (gap 3.9× con trabajo propio, y
nuestro fastdoubling ya está a 6.1×) y **polydisc** (gap 3.9×, sin trabajo
nuestro todavía — el único donde una primera entrada рядida da rank 11 sin
esfuerzo). Si se decide reintentar primecount, el enfoque correcto según F2/F3
no es criba sino **el costo por literal de k bits**: evitar iteraciones que
construyen literales grandes, buscar una reducción que el kernel trate como
atómica.