# F5 — el impuesto por paso de reducción del kernel (2026-10-05)

Métrica: instrucciones dentro de `KERNEL_TIMING`, frontera
`target-declaration-replay-v1` — la misma ventana que puntúa el juez remoto, leída
con el contador del propio timer. Instrumento: `.verify/timer-kernel-local`
(`LK_EXCLUDE_KERNEL=1`), validado antes de medir (ver §0).

## El hueco que este experimento cubre

F2 (`results/cost_model/README.md`) midió el coste de **una** operación `Nat.<op>`
en función de la **anchura** del operando, con el número de operaciones fijo.
Encontró una meseta de ~234k–248k por declaración replayada y un escalón de
+6,0% en 63 bits.

Nunca varió el **número de pasos de reducción**. Esa es exactamente la magnitud
que toda estrategia de optimización de este repo da por conocida:

- `ca-rule110` se atribuyó a «la recursión estructural»;
- `primecount` a «`count` recursiona una vez por primo encontrado»;
- `partition` a «el rebuild exterior de la fila».

Las tres son afirmaciones sobre una pendiente que nunca se midió.

## 0. Calibración del instrumento (ejecutada antes de cualquier celda)

`scripts/f2_instrument_check.py` — **corregido**: su Q1 usaba un
`theorem check := rfl` a nivel de fuente, que es precisamente el defecto que
`f2_harness` documenta (no llega al entorno exportado → `lean4export` PANIC con
rc=0). El script de calibración había quedado atrás del harness que valida.

| control | resultado |
|---|---|
| Q1 export de un probe `addDecl` de 64 bits | **OK, 25.977 B** |
| Q2 `--count-instructions` (métrica de ventana) | **234.552** instr, spread **0,55%** |
| Q3 mismo export sin el flag | `instructions=null` → confirma que la ventana es la única fuente de métrica |

## 1. Serie A — la escalera de pasos

`iterAdd k 0` con `k` pasos estructurales y un operando en una palabra de máquina.
Todos los operandos son pequeños, así que la pendiente es atribuible **solo** al
número de pasos.

| k (pasos) | instrucciones | Δ vs k=0 | implícito/paso |
|---:|---:|---:|---:|
| 0 | 369.196 | — | — |
| 1 | 583.388 | 214.192 | 214.192 |
| 2 | 715.197 | 346.001 | 173.000 |
| 5 | 1.077.470 | 708.274 | 141.655 |
| 10 | 1.686.932 | 1.317.736 | 131.774 |
| 25 | 3.496.856 | 3.127.660 | 125.106 |
| 50 | 6.517.075 | 6.147.879 | 122.958 |
| 100 | 12.634.827 | 12.265.631 | 122.656 |
| 250 | 30.785.296 | 30.416.100 | 121.664 |
| 500 | 61.065.928 | 60.696.732 | 121.393 |

Ajuste: `coste = 459.595 + (121.247 ± 79) · k`, z(β) = 1535,7.
Dispersión intra-celda peor caso: **0,53%** (umbral 5%).

**Veredictos contra los criterios pre-registrados:**

- **G2** spread 0,53% → PASS.
- **G3** H5.1 (linealidad) → **RECHAZADA**, residuo peor 24,49%. El coste **no**
  es lineal en `k`: hay un coste fijo alto y una meseta que la pendiente lineal
  no captura. La pendiente asintótica (k ≥ 50) sí es estable en ~121k.
- **G4** β resuelto con altísima significance (z=1536) → la pendiente **está
  medida**. Esto evita el error de leer una curva plana como «pendiente cero,
  luego cabecera infinita»: aquí la pendiente es real y grande.
- **G5** H5.2 (α domina) → **RECHAZADA**: β·k_max = 60,6M ≫ α = 459.595. Los
  pasos dominan, no el coste fijo.

**Corrección a la lectura de F2 (importante).** El texto de F2 afirmaba que «lo
que cuesta tiempo en un slot es el número de declaraciones replayadas, no su
tamaño». F5 muestra que eso es **falso para la computación real**: el coste
es ~121k por **paso de reducción**, y una declaración trivial ~235k es
irrelevante al lado de una que dobla muchas veces. La conclusion correcta es
otra: **el kernel cobra por unfoldir un paso de recursor, y ese unfold es lo
que domina; la aritmética dentro del paso es mucho más barata.**

## 2. Control H5.3 — el literal del operando NO explica la meseta

Una sola `Nat.add`, tres anchuras:

| probe | operandos | instrucciones |
|---|---|---:|
| B-tiny | 4 bits | 234.013 |
| B-w64 | 64 bits | 212.539 |
| B-w65 | 65 bits | 212.358 |

65-bit vs tiny: **0,91×**. El literal del operando no explica la meseta; el
escalón de 63 bits de F2 es marginal y no es la fuente de la pendiente. **H5.3
no rechazada** — la lectura de F2 sobre el plateau se mantiene, pero la
atribución del coste a la *anchura* queda desmentida: el coste de la ventana es
sobre todo el **unfold**, no el payload.

## 3. F5b — ¿el impuesto por paso es universal o depende del cuerpo?

F5 mide la pendiente con **un** cuerpo (`acc + 1`). Eso deja abierta una
contradicción: «el kernel cobra por iteración» vs «el kernel cobra por lo que
la iteración calcula». Las dos dan consejos opuestos. F5b lo decide con cuatro
cuerpos a k=100 idéntico, variando solo el trabajo por paso:

| cuerpo | trabajo por paso | instrucciones | por paso |
|---|---|---:|---:|
| empty | (ninguno) | 10.424.391 | **99.648** |
| add1 | 1 suma | 12.613.248 | 121.537 |
| xor1 | 1 xor | 12.666.076 | 122.065 |
| heavy | 16 sumas | 43.268.868 | 428.093 |

- **G2** spread 0,77% → PASS.
- **G4** control: `empty` (10,4M) ≤ `heavy` (43,3M) ✓ — el instrumento mide el
  trabajo del cuerpo, no otra cosa.
- **G3** max/min = heavy/empty = **4,15×** (umbral 1,05) → **lectura (B)
  DEPENDIENTE DEL CUERPO ADOPTADA.**

**Lectura (B) adoptada.** El impuesto por paso tiene dos componentes:

- **unfold fijo**: ~99.648 instr por unfoldir un paso de recursor (cuerpo vacío);
- **más aritmética**: ~20.437 instr por operación aritmética extra dentro del
  paso (`(428.093−121.537)/15`).

Es decir: **desdoblar un recursor cuesta ~5× más que una operación aritmética
dentro de él, pero ambas son caras y se suman.** La lectura (A) — «~121k es un
impuesto universal, el cuerpo da igual» — queda **rechazada** por el propio
control de F5b.

## 4. Reconciliación con el tablero y con la contradicción de F5

Antes de F5 había una contradicción sin explicar: F2 decía que una declaración
trivial cuesta ~234k, y el líder de `partition` tiene `curveWork` 1.428.492 en 6
slots ≈ 238k por slot — **casi exactamente una sola declaración trivial**. Pero
el input grande puntuado es n≈36 y p(36)=17977 necesita del orden de cien
sumas bajo la recurrencia de Euler. Si cada operación costara 234k, la aritmética
honesta daría decenas de millones por slot.

**F5 resuelve la contradicción.** Traducido todo el tablero a pasos de kernel
(β=121.247):

| problema | curveWork líder | slots | instr/slot | **pasos/slot** |
|---|---:|---:|---:|---:|
| partition | 1.428.492 | 6 | 238.082 | **1,96** |
| primecount | 1.443.524 | 6 | 240.587 | 1,98 |
| mertens | 1.554.278 | 6 | 259.046 | 2,14 |
| ca-rule110 | 3.433.778 | 6 | 572.296 | 4,72 |
| permanent | 48.826.699 | 15 | 3.255.113 | 26,85 |
| fib | 6.935.647 | 6 | 1.155.941 | 9,53 |
| polydisc | 1.221.338.805 | 6 | 203.556.468 | 1.678,86 |
| sha256 | 9.372.133.412 | 6 | 1.562.022.235 | 12.882,98 |

**La lectura es ahora coherente y es fuerte:** los líderes de `partition`,
`primecount` y `mertens` pagan **~2 pasos de kernel por slot**. No es que
`curveWork` sea una medida de "coste fijo por declaración" (la lectura de F2) —
es que **su presupuesto entero equivale a desdoblar ~2 recursores**. Para calcular
p(36) con la recurrencia dispersa de Euler (208 términos mult-suma sobre m≤36), si
cada término fuera un paso unfoldable, costaría ≥ **25,2M instr/slot** — al menos
**~106× el presupuesto completo del líder**. Esto cuantifica por qué el clúster de
cabecera de `partition` (1,4M) **no es la recurrencia de Euler** y por qué la vía
Euler, ya marcada dead-end, además nunca habría competir (aunque formalizar
`impl_correct` cueste cero instrucciones: el coste está en el unfold).

Nuestra submission 866 en `partition`: 5.382.233.514 / 6 = 897.038.919 por slot
= **7.398 pasos/slot** — 3.768× el líder. El `partition-stream-addblocks`
optimizado tiene `impl_correct` cerrado y sigue a 7.398 pasos: cerrar la prueba
**no**approxima el ranking; el unfold es la barrera.

## 4b. Verificación de la UNIDAD de `computationTotal` (y lo que NO incluye)

**Este apartado existe porque el §4 se apoyaba en un supuesto que no había
verificado: que `computationTotal` está en instrucciones.** Lo verifiqué contra
el payload crudo del leaderboard (2026-10-05, `partition` rank 1):

```json
{"computationTotal": "1428492", "correctnessWork": "17804040326",
 "curveWork": "1428492", "rankingWork": "1428492",
 "rankingContract": "computation-total-v1",
 "coverage": {"completed": 6, "planned": 6},
 "correctnessRole": "verification-only", "peakMemoryBytes": 720916480}
```

Tres comprobaciones independientes:

1. **Unidad.** 1.428.492 / 6 slots = **238.082 instr/slot** frente a los 234.552
   de un `Nat.add` trivial medido con el timer. Coincide al **1,015×**. No es
   µs (serían ~0,24 ms, incompatible con la escala del tablero), no es un
   recuento de pasos Lean. Es instrucciones, y es **casi exactamente una sola
   operación trivial**.
2. **La métrica puntuada es solo `computationTotal`.** `rankingContract =
   computation-total-v1`; `computationTotal`, `curveWork` y `rankingWork` son el
   mismo valor. `correctnessWork` (17,8 miles de millones) se reporta aparte,
   con `correctnessRole: verification-only` — **no puntúa**.
3. **La brecha de ~700× que me confundió** (`floor.py` = 168,86M para un `impl`
   trivial) es de boundaries, no de unidades: `floor.py` cuenta el **proceso
   entero** (`INSTR_TOTAL`, incluye arranque y parseo), `replay` de `f2_harness`
   cuenta la **ventana puntuada** (`KERNEL_TIMING.instructions`, solo
   `measureReplay`). El docstring de `replay` ya lo decía; yo mezclé las dos
   cifras.
4. **Errata propia en la tabla de arriba: `sha256` tiene 6 slots, no 61.** Lo
   leí mal del campo `coverage` del payload; el número real sale de
   `evaluation/problems/sha256/config.json` → 3 grupos × 2 casos = 6 slots, igual
   que el resto. `permanent` sí tiene 15 (3 grupos × 5). Todos los demás, 6.
   La cifra por slot de `sha256` no cambia por esto.

**Consecuencia estratégica que esto cambia.** La verificación de `impl_correct`
para el líder de `partition` cuesta 17,8Md instr = **2,97Md por slot**, es decir
**24.474 pasos de kernel**, frente a 1,96 pasos del replay puntuado. Es ~12.463×
el coste del replay. Pero **no puntúa**: el ranking es `computation-total-v1`.

Esto significa que la estrategia correcta es **minimizar el replay, no la
verificación**. Un candidato con `impl_correct` costoso pero replay mínimo sigue
ganando si el replay es pequeño. Es contraintuitivo para un challenge que
formaliza: para competir en `partition` no importa cuánto cueste *demostrar* que
`impl` es correcto, importa solo cuánto cueste *ejecutarlo*.

Corrijo el framing del §4: escribí «el presupuesto entero del líder equivale a
desdoblar ~2 recursores». Es correcto para el replay puntuado, y es
específicamente el replay — no el trabajo total — lo que se puntúa.

## 5. Corrección a F5: linealidad

Un matiz de rigor. G3 rechazó la **linealidad** (residuo 24,49%), no la
existencia de la pendiente. El residuo viene de los k pequeños: el incremento de
k=0→1 (214k) es mucho mayor que la pendiente asintótica (121k) porque el primer
unfold paga la instanciación del compilador de recursores. La forma correcta no
es «coste lineal en k» sino **coste ≈ α + β·k con α grande, más un primer
unfold más caro**. Para inferir pasos desde `curveWork` uso la pendiente
asintótica β=121.247 (k≥50), que es la región donde viven todos los casos
relevantes.

## 6. Qué NO se puede concluir (límites honestos)

- β se midió con **un** tipo de recursor (`Nat → Nat → Nat`, ecuación de
  ecuaciones). Otros recursores (sobre `List`, `Finset`, `Fin`) pueden tener otro
  unfold; F5b probó dependencia del *cuerpo*, no del *tipo de recursor*.
- El taxón se midió en ámbito user-space local (`LK_EXCLUDE_KERNEL=1`); el juez
  remoto cuenta user+kernel. La **razón** es la misma máquina/instrumento, pero
  el número absoluto lleva un sesgo constante (ERRATA 2026-09-30).
- «~2 pasos/slot» para los líderes usa la pendiente asintótica y una
  extrapolación razonable a budgets pequeños; es una estimación de orden de
  magnitud, no una auditoría.
- **Los `n` del plan local NO son los del plan oficial.** `grouped_plan` fija
  `PERF_SEED = "local-dev-seed"` y el juez usa «una semilla oculta por cohorte»
  (docstring de `grouped_plan`). La FORMA del plan (grupos, casos, escalas)
  transfiere; los valores concretos de `n` no. Por tanto **las cifras locales
  de `--group-check` son internamente consistentes pero no comparables slot a slot
  con el leaderboard.** Solo el leaderboard da la cifra puntuada.

## 6b. Dos mediciones de control de hoy que desmienten atajos de razonamiento

**(a) El trivial de `polydisc` es 12,8× PEOR que su líder, no mejor.** Por la
escala del tablero (1.221Md de instrucciones) y una cifra de `baseline.py` de
2,093M, la aritmética sugería que `def impl n := discSpec n` (legal, con
`impl_correct := rfl`) se llevaría el #1. **Medido sobre el plan oficial local:
15.665.813.912 instrucciones** — el trivial es 12,8× *peor* que el mejor
submission. Las cifras de `baseline.py` se midieron a n=12 (una entrada) y no
son extrapolables a `computationTotal` (suma sobre 6 slots). **No volver a
comparar una cifra de n=12 contra una de plan completo.**

**(b) Nuestro mejor candidato está 6.631× peor que el líder de `partition`.**
`partition-stream-addblocks` sobre el plan oficial local: 9.471.375.938
instrucciones (suma), frente a 1.428.492 del rank 1. Aunque el plan local usa
otros `n`, la magnitud del hueco (cuatro órdenes) no depende del plan: el
candidato optimizado, con `impl_correct` cerrado, sigue ocupando miles de pasos
de unfold mientras el líder paga ~2. **Cerrar la prueba no acerca al ranking; el
unfold es la barrera** — la misma conclusión de §4, ahora con el número del
candidato a la vista.

**(c) El número de slots NO es una palanca: está fijado por config.** Sospeché
que `permanent` (15 slots) y `sha256` eran atacables vía el número de casos, ya
que `computationTotal` es una suma. **No lo es**: `sampling.count` vive en
`evaluation/problems/<p>/config.json`, que es del harness, no del submission.
Ningún candidato puede cambiarlo. Descartado antes de gastar tiempo.

**(d) El contrato real, leído de la config, es
`{work: curve, proof: gate}`.** Es decir: el trabajo puntuado es la curva de
cómputo, y la prueba es un **gate** (puerta de paso), no una componente sumada.
Esto confirma §4b por la vía estructural y no solo por el payload: el
`correctnessWork` de 17,8Md del líder es el coste de **pasar la puerta**, y no
entra en el ranking.

## 7. Artefactos

- `scripts/f5_step_slope.py` — escalera + control de anchura (pre-registrado).
- `scripts/f5b_body_tax.py` — universal-vs-cuerpo (pre-registrado).
- `scripts/f2_instrument_check.py` — corregido (calibración del instrumento).
- `scripts/lk_readonly.py`, `scripts/lk_board.py` — lectura del API sin poner la
  clave en la línea de comandos.
- `results/cost_model/f5_step_slope.{json,txt}`, `f5b_body_tax.{json,txt}`.