# F8 — el suelo de 118k: por qué existe el coste fijo, y una corrección a F5 (2026-10-05)

Métrica: instrucciones en `KERNEL_TIMING`, frontera
`target-declaration-replay-v1`. Instrumento: `.verify/timer-kernel-local`,
`LK_EXCLUDE_KERNEL=1`, reps 3, harness idéntico a F7.

Pre-registrado en `scripts/f8_fixed_floor.py`. **G1 se relajó deliberadamente**
en este experimento: un fallo de compilación era información (una celda
exploratoria que no compila no invalida a las otras), no una violación del
guardián. Queda registrado como tal en el JSON.

## La contradicción que este experimento resuelve

F7 ajustó siete puntos y obtuvo `coste = 244.590 + 37,1 · carriles`, con el
**intercepto (244.590) por encima del presupuesto de un campeón por slot
(238.082)**. F6 showed que el coste es sublineal en anchura, así que ese
intercepto fijo **no puede ser la aritmética**: si lo fuera, 4.096× más operandos
costaría proporcionalmente más.

F7 deja entonces la pregunta abierta: **¿existe un suelo de ~118k por
declaración que sea removible?** Si existe, caben más de una operación por slot y
el presupuesto deja de ser el muro. F8 lo responde con seis celdas, cada una
aislando una causa distinta del coste fijo.

## 1. Las seis celdas

| celda | instrucciones | vs ref | qué aísla |
|---|---:|---:|---|
| **A-const-refl** | **118.230** | **0,482×** | `Eq.refl` entre literales. **Ninguna aritmética.** |
| B-zero-const | 177.557 | 0,725× | llamada a constante de 0 argumentos |
| D-nat-sub | 234.699 | 0,958× | `Nat.sub` (lo que un DP empaquetado necesita) |
| E-const-unfold | 177.608 | 0,725× | mismo trabajo vía constante de usuario |
| F-nat-add-4bit | 208.895 | 0,852× | `Nat.add` de 4 bits (la referencia) |
| C-nat-succ | FALLÓ | — | `Lean.mkApp1` no existe en esta API |

## 2. Veredictos

| | |
|---|---|
| G2 spread ≤ 5% | PASS (peor 0,55%) |
| G3 H8.1 hay ruta más barata | **NO RECHAZADA** — `A-const-refl` a 118.230 = 0,482× de la referencia |
| G4 H8.2 no es específico de aritmética | **NO RECHAZADA** — la celda sin aritmética más cara (177.608) = 0,725× |
| G5 siempre reportar la más barata | `A-const-refl` es el suelo |

**H8.1 y H8.2 no rechazadas.** El coste fijo de ~234k **no es la aritmética**. Un
`Eq.refl` entre dos literales, que no hace nada, cuesta la mitad. El coste fijo es
la **declaración**, no la operación.

## 3. La descomposición corregida del coste

Antes (F6/F7) creía que ~234k era «coste por operación». F8 lo parte en dos:

- **suelo de declaración: ~118k** — independiente de la aritmética
- **componente dependiente del operando: ~36k** — `Nat.add` de 4 bits (208.895)
  vs de 4.160 bits (245.053) = +36.158

Esa es la firma sublineal de F6, explicada. El ancho del operando importa, pero
apenas: 4.096× más operandos = +36k, no +234k.

## 4. CORRECCIÓN IMPORTANTE — lo que casi escribo mal

Al ver que el suelo (118.230) y el «impuesto por unfold» de F5 (121.247) casi
coinciden (1,026×), estuve a punto de concluir que *«un unfold no cuesta más que
el suelo de la declaración, así que F5 atribuyó al unfold un coste que es en
realidad el suelo»*.

**Eso habría sido una coincidencia numérica, no una identidad.** F5 midió
`k=0` en **369.196**, no 118.230: ese `k=0` incluye el unfold de la ecuación de
ecuaciones *más* el suelo de la declaración (369.196 − 118.230 = **250.966** de
trabajo de recursión incluso con `k=0`). La ley de F5 sigue vigente como
**pendiente marginal** de ~122.656 instr/unfold, no como suelo.

Lo que F8 **sí** confirma, desde el otro lado, es el techo: suelo (118.230) + 1
unfold (122.656) = **240.886 > 238.082** (el presupuesto del campeón). Un
campeón no puede pagar ni **un** unfold completo más el suelo dentro de su slot.
Esto hace consistente el ~2 unfolds/slot que medí en el leaderboard y confirma que
no hay ningún loophole oculto en el desglose.

## 5. La tensión honesta que queda

Si suelo + 1 unfold = 240.886 ya supera el presupuesto (238.082), ¿cómo paga el
campeón ~2 unfolds por slot (238.082/slot medido en el tablero)? Tres
explicaciones, ninguna verificada:

1. **Mi frontera difiere de la del juez.** El juez remoto cuenta user+kernel;
   yo cuento solo user (`LK_EXCLUDE_KERNEL=1`). La **razón** es la misma máquina,
   pero el absoluto lleva un sesgo constante. Comparar mi 118k con su 238k sin
   corregir ese sesgo es impreciso — por eso todo lo anterior son **cifras
   relativas** (cuántas veces cabe X en Y), no medidas absolutas comparables con el
   tablero.
2. **El campeón hace menos trabajo del que creo.** `impl` podría reducir a un
   resultado ya normalizado (por ejemplo, `decide`/`rfl` sobre una expresión
   pequeña), pagando menos suelo del que paga mi sonda.
3. **La operación de microcoste del campeón no es un unfold de Nat.rec.** F5
   midió unfolds de recursor; el campeón podría usar una representación cuyo
   unfold equivalente sea más barato (por ejemplo, `Nat.rec` compilado a una
   función más pequeña, o `decide`-style evaluation).

**No sé cuál es.** No la presents como resuelta. Lo que sí es sólido y no depende
de resolverla: **el desglose suelo-componente**, y que **cabe más de una unidad
de suelo por slot** (118.230 × 2 = 236.460 < 238.082, justo).

## 6. Corregir también la referencia de F7

F7 usó 245.053 (el `Nat.add` de 64 carriles de F6b) como referencia de
aritmética. F8 midió `Nat.add` de 4 bits = **208.895**, un 17% más barato. Eso
significa que F7 **sobreestimaba** su propia referencia, así que los veredictos de
F7 que dependen de esa base se desplazan:

- **F7 G5** (512 carriles bajo 238.082): 263.482 vs 238.082 = 1,11×. **No
  cambia** — el umbral compara contra la config, no contra la referencia.
- **F7 G3** (H7.1 flatness ≤1,25×): con base 208.895 en vez de 245.053, las
  razones «vs 64-carriles» suben ~17%. H7.1 sigue **RECHAZADA** (1,31× → ~1,53×).

Ninguna conclusión de F7 se invierte, pero la referencia estaba mal anclada y
debía decirse.

## 7. Qué NO se puede concluir

- El suelo de 118k se midió con sondas que son `Eq.refl` sobre literales. No es
  necesariamente el mismo suelo que paga un `impl` real con estructura.
- `C-nat-succ` falló por API (`Lean.mkApp1` no existe), así que la aritmética
  estructural (no-GMP) queda **sin medir**. Eso es un hueco real: si `Nat.succ`
  fuera mucho más barato que `Nat.add`, cambiaría el presupuesto por operación.
- Todo es user-space local; la comparación absoluta con el leaderboard arrastra
  el sesgo de §5.1.

## 8. El siguiente paso

El hallazgo accionable: **el suelo por declaración (~118k) es la mitad del coste
de una operación, y es lo primero que un candidato paga.** Dos suelo + 1 unfold
= 359.116 > presupuesto. Un suelo solo = 118.230 < presupuesto. El presupuesto
permite **una** declaración-suelo, o **casi dos**. Eso significa que la
optimización de un candidato no es «hacer la operación más barata» (ya lo es,
4 bits), sino **minimizar el número de declaraciones replayeadas**, porque cada
una paga el suelo.

Esto es coherente con F5 (menos unfolds es mejor) y añade el matiz: cada unfold
no es solo 121k, arrastra además el suelo si implica una declaración nueva. El
siguiente experimento útil sería medir una sola declaración que haga *varios*
unfolds (una recursión que represente varias operaciones en un solo término),
para ver si el suelo se paga una vez o por unfold. Eso decide si hay un
«suelo por declaración» o un «suelo por unfold».

## 9. Artefactos

- `scripts/f8_fixed_floor.py` — sondas del suelo (pre-registrado, G1 relajado).
- `results/cost_model/f8_fixed_floor.{json,txt}`.
- `C-nat-succ` (Nat.succ) sin medir: fallo de API, hueco reconocido.
- Continuación: F5 (impuesto por unfold), F6/F6b (sublineal + empaquetado),
  F7 (techo del empaquetado).