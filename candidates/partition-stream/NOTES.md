# partition — estado 2026-09-28: la vía del plan es imposible, y hay un
# candidato 2,27x más rápido que el único calificable.

## 1. HALLAZGO BLOQUEANTE: `partition` NO tiene Mathlib

El objetivo revisado del encargo era demostrar la convolución del spec vía
`pentagonalSeries` / `PowerSeries.coeff_mul` / `coeff_inv_aux`, apoyándose en
`problems/mertens/EulerAPI.lean`. **Esa vía no existe para `partition`.**

Verificado empíricamente hoy, no inferido:

| Comprobación | Resultado |
|---|---|
| `lake-manifest.json` de `partition` | `"packages": []` |
| `[[require]]` en su `lakefile.toml` | ausente |
| `dependency-lock.json` | solo existe para `fib`, `mertens`, `primecount` |
| `rules/evaluation.md` | "Mathlib pinned v4.33.1 **for fib, mertens, and primecount; core Lean for the other five**" |
| `rules/problems/README.md` | tabla: `partition` → dependencia **Core Lean** |
| `import Mathlib.RingTheory.PowerSeries.Basic` en `problems/partition` | `error: unknown module prefix 'Mathlib'` |
| el mismo probe en `evaluation/problems/partition` | idéntico error |

`problems/mertens/` sí tiene Mathlib porque es un problema Mathlib: por eso
`EulerAPI.lean` compila ahí y es una buena referencia de firmas — pero sus
`.olean` no son importables desde el paquete de `partition`, y
`rules/problems/README.md:66` advierte explícitamente: *"Additional imports may
compile locally but be unavailable in official evaluation."*

Consecuencia: el paso 1 del encargo (el lema de convolución) no es difícil, es
**imposible tal como está redactado**. No hay `PowerSeries` en el lado que
compila. Reimplementar el teorema pentagonal de Euler desde cero en core Lean
es un proyecto de semanas, no el atajo que el plan asumía.

## 2. Lo que sí es viable: la misma identidad, en elemental

La identidad que el plan quería como "convolución" se demuestra en core Lean
con la maquinaria que `partition-foldl` ya tiene probada, sin power series:

    partAux (k+1) m = Σ_j partAux k (m - j*(k+1))
                   = partAux k m + partAux (k+1) (m - (k+1))     -- pelar j=0

Es la recurrencia de una sola parte. Los dos ingredientes existen en core y
están verificados en este toolchain (`leanprover/lean4:v4.33.1`):
`Nat.div_eq` (el mismo que `partition-foldl` usa en su línea 91) y el
`msum_peel` ya probado. Los lemas de `List` necesarios
(`getElem?_take/drop/append/zipWith`, `length_take`, `length_zipWith`,
`take_append_drop`) también existen; `List.getD_eq_getElem?` NO existe.

## 3. Candidato nuevo: `partition-stream`, 2,27x más rápido

`partition-foldl` recalcula cada celda como una suma de multiplicidad
independiente y cada sumando re-camina la fila con `getD`:

    new[m] = Σ_j t.getD (m - j*d) 0

Una fila cuesta O(n²/d) recorridos y el run completo O(n³).

Pero esa misma suma se puede agrupar por su primer término:

    Σ_j t[m - j*d] = t[m] + Σ_i t[m - (i+1)*d] = t[m] + new[m - d]

es decir `new[m] = t[m] + new[m - d]`, con `new[m] = 0` para `m < d`. Como
`new[m]` solo depende de `new[m - d]`, las posiciones se parten en `d` clases
de residuos, y **un bloque de `d` posiciones consecutivas necesita
exactamente el bloque anterior de `d` valores**:

    new[b*d + i] = t[b*d + i] + new[(b-1)*d + i]

Un `zipWith` produce `d` celdas en O(d); una fila cuesta O(n). Sin `getD` en el
bucle interno, sin división, sin tabla precalculada, sin constantekova.

### Medición — métrico oficial, `n = 36` (máximo del rango P3)

| Candidato | Instrucciones | kernel-defeq | `impl_correct` |
|---|---:|---|---|
| `partition-foldl` | 5.148.505.192 | sí (17977) | **PROBADO** |
| `partition-stream` | **2.268.731.802** | sí (17977) | pendiente |
| `partition-euler` | 1.105.322.664 | sin medir | no (partAux n n) |
| floor (impl trivial) | 168.707.266 / slot | — | — |

`2.268.731.802 / 5.148.505.192 = 2,27x` a favor de stream. Es una mejora real
sobre el único candidato calificable, y no usa parámetros precalculados: es la
forma que sobrevive a la regla de YZ sobre "hardcoded parameters", porque no
hay ningún literal de respuesta — solo la forma de la recurrencia del spec.

Nota de coste: el suelo de 168,7M por slot es irreducible y el `curve_work` es
la **suma** de los 6 slots, así que la ganancia de 2,88B instrucciones es
frente a ~1,01B de suelo. Sigue siendo una ganancia neta y creciente, y crece
más con N.

### Estado del gate de `partition-stream`

1. `lake env lean` compila limpio con `warningAsError=true` — **PASA**
2. contiene `impl_correct` — **NO** (pendiente)
3. no hay `sorryAx` — **PASA** (cero `sorry` en el archivo)
4. `gradable.sh` dice CALIFICABLE en n=36 — **PASA** (`GRADEABLE partition
   candidates/partition-stream/Submission.lean (n=36, impl n kernel-defeq to
   17977)`)
5. cross-check AGUAS ARRIBA del crosscheck del juez — **PASA**: `impl n =
   partitionSpec n` para todo `n` en 0..31 (el Spec es una recurrencia
   *distinta*, así que la acuerdo es una comprobación independiente), y
   `p(0..19)` coincide con la sucesión conocida
   `[1,1,2,3,5,7,11,15,22,30,42,56,77,101,135,176,231,297,385,490]`

### Por qué el cross-check no sube a 0..79

El oráculo (`partitionSpec`) es el cuello, no el candidato: `partition-foldl`'s
crosscheck ya Research dónde está el cliff (n=70 instantáneo, n=80 no termina
en 200 s). Un sweep 0..79 con este candidato excede los 400 s de timeout. El
sweep 0..31 cubre los tres inputs del juez y todas las ramas (base `p(0)=1`,
guard `g2 ≤ m`, terminador `g1 > m`, borde de bloque corto) y es lo que está
**medido**. Estirar el rango es trabajo de oráculo, no prioridad.

## 4. Qué falta exactamente

`impl_correct` para `partition-stream`, en tres lemas:

- **A (nuevo, el trabajo real)**: `(updRow d t).getD m 0 = t.getD m 0 +
  (if d ≤ m then (updRow d t).getD (m - d) 0 else 0)`. Inducción sobre la
  estructura de bloques de `chunks`/`zipBlocks`. O, equivalente y posiblemente
  más limpio, el fixpoint de listas
  `updRow d t = t.zipWith (· + ·) (List.replicate d 0 ++ updRow d t)`.
- **B (portado)**: el `msum` del spec satisface la misma recurrencia, vía
  `msum_peel` + `Nat.div_eq`.
- **C (medio)**: por `Nat.strongRecOn` en `m`, A + B dan que la fila del
  candidato es la suma de multiplicidad del spec.
- luego portar verbatim de `partition-foldl`: `rows`, `rows_eq_partAux`,
  `initTable_getD`, `tableItFrom_correct`, `impl_correct`.

Los tres lemas de `List` que C necesita están confirmados en core; la ruta es
viable. **No se ha intentado la prueba todavía** — esta sesión no llegó a
escribirla, así que no hay veredicto sobre si A compila.

## 5. Honestidad sobre lo que NO se hizo

- No se envió ningún run. No se tocó ningún `Submission.lean` versionado
  (`git diff HEAD` sobre `problems/` y `evaluation/` está vacío).
- No se tocó `ca-rule110`.
- `primecount` y `mertens` siguen sin tocar, por las razones ya registradas.
- No se resolvió la pregunta de `noncomputable` (sigue sin respuesta en Zulip).
- No hay committed proof. Lo único nuevo es `candidates/partition-stream/`,
  un candidato **medido y verificado correcto, pero sin `impl_correct`** — no
  es enviable.

## 6. Recomendación

`partition-stream` es el camino, y es 2,27x mejor que lo que tenemos sin
comprometer la corrección (mismo `impl` en valores, probado 0..31). Su prueba es
el bloqueo restante y es trabajo acotado con los lemas ya identificados. La vía
pentagonal queda **descartada para siempre en `partition`**: no es cuestión de
esfuerzo, es que el paquete no tiene Mathlib.
