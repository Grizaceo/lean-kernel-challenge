# LKC F10–F12 — el suelo se midió en la forma equivocada

**Fecha:** 2026-10-05 · **Commits:** `267311a` (F10 pre-reg), `b8a1c2d` (F10 VOID + F10b),
`7caefa4` (F11 pre-reg), `f23ada8` (F12 pre-reg) · **Instrumento:** sin cambios respecto de
F5/F8/F9 (`KERNEL_TIMING`, frontera `target-declaration-replay-v1`, mediana de 3, sin resta,
`LK_EXCLUDE_KERNEL=1` → **user-space solamente**).

## Resumen ejecutivo

El objetivo de la sesión era resolver si el suelo de ~118k se paga una vez o por unfold
(§4 del handoff) y luego construir el candidato `partition` empaquetado (PASO 2).

**El objetivo se resolvió, pero al revés de lo esperado, y el PASO 2 queda descartado.**

1. **F10 (Serie A) es VOID.** Su cuerpo devolvía una *constante*, así que el kernel
   emparejaba una vez y paraba en todo k. Su veredicto de 0,167× era unaMeasurement de
   "cero emparejamientos → uno", no del suelo.
2. **F10b (válido)**: el suelo se paga **una vez por declaración**, y el margen por unfold
   con un `Nat.rec` es **95.398 ± 1.129** (z=84,5). H10.1 sobrevivió; H10.2 queda descartada.
3. **F11 (con el generador del juez)**: el suelo real en forma puntuada es **199.012**
   (sin recursor), no 118.230. El 118.230 de F8 se midió sobre la forma equivocada.
4. **F12**: el margen estable de una suma plana es **20.140**, pero la **primera** suma
   cuesta **122.520** (prima de 102.380 por abrir el `n` opaco ante GMP).
5. **Consecuencia de diseño**: un `impl` que sea un `Nat.rec` cuesta **356.917 = 1,499×**
   el slot del campeón (238.082). **Ninguna implementación recursiva cabe en un slot,
   ni computando nada.** El `partition` por DP es una recursión → **PASO 2 descartado**.

## La aritmética que reencuadra todo (medida, no supuesta)

| término | instrucciones | fuente | alcance |
|---|---:|---|---|
| slot del campeón (partition rank1 1.428.492 / 6) | **238.082** | leaderboard | user+kernel |
| suelo, `impl` **sin** recursor (`fun _ => 0`) | **199.012** | F11 `J-C-trivial` | user-space |
| suelo, proyección (`fun n => n`) | **183.396** | F12 `chain@0` | user-space |
| suelo, `impl` **con** `Nat.rec`, k=0 | **356.917** | F10b `A@0` | user-space |
| precio de **poseer** un recursor | +157.905 | 356.917 − 199.012 | user-space |
| margen por unfold, cuerpo vacío | **95.398 ± 1.129** | F10b `A` (z=84,5) | user-space |
| margen unfold + una `Nat.add` | **122.142 ± 1.182** | F10b `B` | user-space |
| la `Nat.add` dentro de un paso | 26.744 | B−A | user-space |
| margen estable de una suma plana | **20.140** | F12 (k≥2) | user-space |
| primera suma (prima de apertura de GMP) | **122.520** (extra 102.380) | F12 k=0→1 | user-space |

Las tres aritméticas que corrigen el modelo de F8/F9:

- **El suelo de F8 (118.230) estaba en la forma equivocada.** Era un `Eq.refl` entre
  literales, sin `impl`. En la forma del juez es 199.012: **1,686×** más caro. F8 lo
  leyó como el suelo de un slot puntuado cuando no lo era — una asunción, no una
  medición. F7 ya lo había medido sin saberlo: su intercepto de packing era 244.590
  (**1,019×** de 240.006, el `C@0` de F10b).
- **F5 medía "un unfold + una suma", no "un unfold".** Su 121.247/step era el caso `B` de
  F10b (122.142, **1,007×**), porque su cuerpo era `acc + 1`. El unfold desnudo cuesta
  95.398.
- **La recursión es la forma cara, no la aritmética.** Un unfold de `Nat.rec` cuesta
  4,74× una suma plana (95.398 / 20.140). Esto invierte la intuición de F8/F9, donde
  "toda aritmética cuesta ~1,75× el suelo".

## Veredictos de los guardianes

### F10 — VOID, y por qué no se reportó como resultado

| cell | k=0 | k=1 | k=2 | k=3 | k=5 | k=10 |
|---|---:|---:|---:|---:|---:|---:|
| A (cuerpo constante) | 239.705 | 279.826 | 280.101 | 280.236 | 279.837 | 279.491 |

Dispersión k=1..10: **0,27%**. G3 leyó `c(1)−c(0) = 40.121 = 0,167× c(0)` y declaró
"el suelo se paga una vez". **Eso no lo sostiene la sonda:**

```lean
def impl : Nat → Nat
  | 0 => 0
  | n + 1 => 0      -- devuelve una CONSTANTE
```

Para reducir `impl 5` el kernel empareja el 5, toma la rama 2, y recibe el literal 0:
**tiene su respuesta y para**. Nunca aplica `impl` a 4, 3, 2, 1. k=1..10 son la *misma*
computación. La curva plana no dice "los unfolds son gratis": dice que la escalera
nunca pasó de profundidad 1.

**Por qué G1 no lo atrapó.** La construcción tuvo éxito, el tipo-checking pasó, y el
teorema de autovalidación (`impl 2 = 2`) era **verdadero**. Una sonda puede compilar,
tipar, medir y aun así no ejercitar lo que se está midiendo. Es la lección de F5 ("un
k=0 que contiene un recursor no es un suelo") un nivel más profundo: **una escalera cuyo
cuerpo no fuerza recursión no es una escalera de unfolds, es una escalera de
emparejamientos.**

De aquí sale **G8** (F10b): una escalera que no crece estrictamente con z(β) > 3 es VOID
y la corrida reporta el defecto de sonda, no una ley de coste.

La Serie B de F10 (`impl n + 1`) sí es sólida: reprodujo el 121.537 de F5b al **1,006×**,
o sea el instrumento estaba bien y solo la sonda A estaba mal.

### F10b — válido, ladder verificado

| k | C constante | A recursivo-vacío | B add1 | A−C | B−A |
|---|---:|---:|---:|---:|---:|
| 0 | 240.006 | 356.917 | 358.423 | 116.911 | 1.506 |
| 1 | 280.016 | 474.252 | 549.090 | 194.236 | 74.838 |
| 2 | 280.020 | 568.063 | 677.497 | 288.043 | 109.434 |
| 3 | 280.523 | 662.225 | 796.374 | 381.702 | 134.149 |
| 5 | 280.232 | 849.449 | 1.028.335 | 569.217 | 178.886 |
| 10 | 279.713 | 1.321.912 | 1.615.293 | 1.042.199 | 293.381 |

- **G8**: β_A = 95.398 ± 1.129, **z = 84,5** → la escalera sí crece de forma estricta.
  Serie A válida.
- **G9**: A−C alcanza 373% del coste de C (k=10) → el cuerpo recursivo hace trabajo real
  más allá del primer emparejamiento. No es la misma medición.
- **G5**: β_B = 122.142 vs F5b 121.537 = **1,005×** → instrumento consistente.
- **G3 (sobre β, no sobre el ratio de F10)**: la ley de coste por unfold está
  establecida y es *plana*: 95.398 ± 1.129 a lo largo del rango de k medido, con la
  escalera recorrida de principio a fin (z=84,5). El control equivalente en la Serie C
  —cuyo cuerpo tampoco fuerza recursión, el defecto de F10— da β = 2.109 ± 2.001 con
  **z = 1,05**: no distinguible de cero. Es la reproducción cuantificada del fallo de F10
  desde el propio F10b, y por eso G8 existe.

### F11 — con el generador del juez, el suelo real

| cell | instrucciones | vs F10b | qué es |
|---|---:|---:|---|
| `J-C-trivial` | 199.012 | 0,829× | `fun _ => 0`, no calcula nada |
| `J-C-const` | 199.864 | — | lambda que devuelve constante, sin recursor |
| `J-A-recur` | 848.101 | 0,998× (k=5) | `Nat.rec`, k=5 unfolds |
| `J-B-add1` | 1.027.791 | 0,999× (k=5) | `Nat.rec` + 5 sumas |

**Corrijo mi propio G3 aquí.** El G3 pre-registrado comparó `J-A-recur` (k=5) contra
`A@0` de F10b (k=0): un **desajuste de k** que exageraba el desacuerdo a 137,6%. Las
comparaciones like-for-like son:

| comparación | judge | F10b | ratio |
|---|---:|---:|---:|
| no recursivo, k=5 | 199.012 | 280.232 (`C@5`) | 0,710× |
| recursivo, k=5 | 848.101 | 849.449 (`A@5`) | **0,998×** |
| add1, k=5 | 1.027.791 | 1.028.335 (`B@5`) | **0,999×** |

Así que el artefacto está **solo en la celda sin recursor**: F10b la sobrestimaba en
**1,408×** (40,8%). Las escaleras recursivas de F10b son fieles al juez al 0,2%. El
error de F8 es el mismo defecto, y F11 lo localiza.

- **G4**: los cuatro teoremas salieron de `judge._perf_theorem_source` importado
  literalmente; las fuentes quedan grabadas verbatim en el artefacto.
- **G5**: `LK_EXCLUDE_KERNEL=1` es *user-space solamente* y user+kernel es un
  **supercjunto**, así que estos suelos son **cotas inferiores** de lo que el juez cobra.
  El sesgo hace el slot del campeón verse **más pequeño**, nunca más grande: la
  contradicción corre en la dirección segura.
- **G7**: `Submission.lean`, `Perf.lean` y `Perf.olean` restaurados byte a byte
  (md5 `dcfe4d3e…` antes y después de las tres corridas de F11 y las dos de F12).
- **No representable**: una *constante* de tipo `Nat → Nat` no tiene literal en Lean
  (`OfNat (Nat → Nat) 7` no existe, y la aserción de tipo no ayuda). "impl no aplica
  nada" **no es medible**. `J-C-const` es una lambda que devuelve constante y está
  etiquetada así; una versión anterior de esa celda afirmaba "no aplica nada", que
  habría sido no medido.

### F12 — el margen en la forma alcanzable

| k (sumas) | instrucciones | vs k=0 | impl/add |
|---|---:|---:|---:|
| 0 | 183.396 | 0 | — |
| 1 | 305.916 | 122.520 | 122.520 |
| 2 | 327.473 | 144.077 | 72.038 |
| 3 | 347.376 | 163.980 | 54.660 |
| 5 | 386.270 | 202.874 | 40.575 |
| 10 | 486.550 | 303.154 | 30.315 |
| 20 | 683.907 | 500.511 | 25.026 |

- **G3**: β = 21.888 ± 2.315, z = 9,5 → la escalera sí fuerza k sumas.
- **G5**: cada `Submission.lean` se asertó libre de `Nat.rec` / patrones
  estructurales / `match` / `termination_by` antes de construir.
- **G6 → CORRIDO, la corrida queda DRIFTED.** Mi k=0 (`fun n => n`) dio 183.396 contra
  los 199.012 de F11 (`fun _ => 0`): 7,8% > 5%. **El control estaba mal especificado**,
  no el instrumento: `fun n => n` devuelve su entrada y `fun _ => 0` la descarta; no son
  la misma medición. Lo reescribo así en vez de relajar el umbral.
- El ajuste lineal tiene residuo 42% porque **no es una recta**: ver abajo.

## La prima de apertura: el hallazgo que reencuadra el presupuesto

Los incrementos no son lineales en k:

| de → a | incremento | /add |
|---|---:|---:|
| 0 → 1 | 122.520 | 122.520 |
| 1 → 2 | 21.557 | 21.557 |
| 2 → 3 | 19.903 | 19.903 |
| 3 → 5 | 38.894 | 19.447 |
| 5 → 10 | 100.280 | 20.056 |
| 10 → 20 | 197.357 | 19.736 |

Hay dos regímenes: **la primera suma cuesta 122.520**, de los cuales ~102.380 son una
**prima por abrir el operando opaco `n` ante GMP**; las siguientes cuestan ~20.140 de
margen estable. F8/F9 concluyeron "toda aritmética es plana y cara" desde una sola
operación — no había forma de ver la prima porque su sonda no tenía la forma del juez.

Consecuencia directa sobre el presupuesto:

| suelo | headroom hasta 238.082 | ¿cabe 1 suma? | sumas estables |
|---|---:|---|---:|
| 183.396 (F12) | 54.686 | **NO** (excede en 67.834) | 2,72 |
| 199.012 (F11) | 39.070 | **NO** (excede en 83.450) | 1,94 |

## Veredicto de diseño: el muro es real, y es más alto de lo que se pensaba

El muro de F8/F9 ("el presupuesto compra una operación y nunca dos") **no era un muro
aritmético**: era un artefacto de haber medido el suelo en la forma equivocada. Corregido
el suelo, el presupuesto real es **una operación con prima de apertura, y ni siquiera
una entra en el slot del campeón** si el `impl` parte de un suelo de 183–199k.

Y por encima de eso, el hallazgo que decide el PASO 2:

> **Suelo con un `Nat.rec` = 356.917 = 1,499× el slot del campeón.**
> Ningún `impl` recursivo cabe en un slot, ni computando nada.

El `partition` por DP (fila del DP, recurrencia dispersa, cualquier cosa que pliegue)
es una recursión. Por tanto:

- **PASO 2 (candidato `partition` empaquetado): DESCARTADO**, y no por rendimiento sino
  por estructura del presupuesto. El packing sigue siendo la amortization correcta
  (F7: 1.804× a 4.096 carriles), pero no hay ningún `Nat.rec` que amortizar dentro de
  238.082 instrucciones.
- **PASO 3 (envío): NO PROCEDE.** Sin candidato viable no hay nada que enviar, y la cuota
  (0/2 en `partition` tras la #866) no se gasta. El envelope formal ya está resuelto
  (OpenAPI, rama *Service-owned*: `idempotencyKey` + `contractVersionAcknowledged` +
  `payload:{problem,text}`), pero no se toca.

## Dos guardianses que fallaron, y por qué los mantengo

1. **G1 de F10 no atrapó la sonda mala.** Compilaba, tipaba y autovalidaba. De ahí G8.
2. **G3 de F11 emparejó formas distintas** (k=5 contra k=0) y reportó 137,6% de
   desacuerdo donde el desacuerdo real es 0,2% en las celdas que importan. Lo corregí
   con la tabla like-for-like arriba. La lección general ya estaba en el handoff
   ("comprobar que las sondas tienen la MISMA forma") y reincidí: el guardia estaba
   escrito, mi emparejamiento no.

## Lo que NO se puede concluir

- **Abierto y es lo más importante**: el campeón paga **238.082 por slot**, pero el
  suelo que mido en forma del juez es **183.396–199.012** y una única suma plana lleva la
  declaración a **305.916**, por encima del slot. El campeón computa `p(16) = 231`
  correctamente en 238.082. **O mi suelo todavía sobrestima, o el campeón usa una forma
  estructuralmente distinta de la que mis sondas exercised.** No sé cuál, y las dos
  tienen consecuencias opuestas para el diseño. No lo maquillo: queda declarado abierto,
  y es el primer paso de cualquier sesión siguiente.
- **No sé qué hace el campeón.** Tres candidatas a investigar, ninguna medida:
  (a) `decide`/`rfl` sobre una proposición cerrada, cuyo trabajo de kernel no pasa por
  `Nat.add`; (b) operaciones whose GMP path is cheaper than my probe's; (c) mi suelo
  incluye trabajo que el juez no cobra.
- **Alcance**: todo es user-space (`LK_EXCLUDE_KERNEL=1`). Son **cotas inferiores** de lo
  que cobra el juez. Las razones dentro de una misma corrida son quotables; los
  absolutos contra el leaderboard, no. Los números de leaderboard de esta sesión
  (1.428.492 en `partition`, cov 6/6) se leyeron con `lk_board.py` (GET-only).
- **Las locales no son comparables slot a slot**: `grouped_plan` usa
  `PERF_SEED="local-dev-seed"` y el juez usa semilla oculta por cohorte. Solo las
  formas del plan transfieren.
- **No se tocó `problems/`** más allá del staging temporal que G7 restaura, y no se
  hizo ningún envío.

## Réplica

```bash
python3 scripts/f10_floor_once_or_per_unfold.py    # VOID (Serie A) — superseded
python3 scripts/f10b_traversal_ladder.py           # ladder válida, β por unfold
python3 scripts/f11_judge_generator_shape.py       # suelo con el generador del juez
python3 scripts/f12_champion_shape_marginal.py     # margen en la forma alcanzable
```

Artefactos: `results/cost_model/f1{0,0b,1,2}*.json` y `*.txt`.