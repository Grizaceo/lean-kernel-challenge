# F3 — veredicto: primecount-sieve-bits NO PASA el gate (falla documentada)

Fecha: 2026-09-30. Candidato: `candidates/primecount-sieve-bits/Submission.lean`. Commit pendiente.

## Resumen

El piloto de paradigma bit-packed para primecount, medido con el pipeline oficial
local (`scripts/measure.py --group-check primecount candidates/primecount-sieve-bits
--reps 3`), da:

| slot | n    | instr (icount, process-wide) | spread ± |
|---|---:|---:|---:|
| Q1.0 |  85 |  4.123.609.377 | 0.20% |
| Q1.1 | 100 (incluido) | 4.118.435.570* |
| Q2.0 | 167 |  4.135.120.219 | 0.65% |
| Q2.1 | 294 |  4.155.266.172 | 0.59% |
| Q3.0 | 666 |  4.216.939.615 | 0.21% |
| Q3.1 | 991 |  4.281.849.026 | 0.14% |
| **suma** |  | **25.031.035.331** | |

*(spread + median del slot Q1.1 desplazados por truncamiento del tail; su valor
está en el log completo `proc_351372633f5d`).*

**Veredicto: NO PASA.** Gate exigía ≤ **4.3M** (3× líder de primecount = 1.44M);
el resultado bruto es **25.0B** ≈ 5.800× por encima. Aun descontando el piso de
instrumento local estimado en F1 (~4B por proceso = ~24B para 6 slots), el
remanente **~1B sigue siendo ~700× el gate**.

## Diagnóstico de la desviación (F1 explica el sesgo)

La escala de los números es *casi plana en n* (de 4.12B para n=85 a 4.28B para
n=991, +4% sobre un ×12 en n). Esto es **exactamente** el fenómeno de `ERRATA.md`:
el instrumento `icount` cuenta el arranque del proceso timer + parseo del JSON
del export, que es **constante** (~3.5–4B) y **domina** sobre el cómputo real
(~28M/slot por variación entre slots).

Aplicando la calibración aprendida en F1:

- piso por proceso ≈ 4B ⇒ piso total 6 slots ≈ **24B**.
- residuo (cómputo real dentro de la ventana del juez) ≈ 25B − 24B ≈ **~1B**,
  repartido en 6 slots ≈ **~167M/slot**.
- con ratio instrumento:juez ≈ 1.76× (medido en F1 sobre submission-866),
  costo **oficial estimado ≈ 95M/slot ⇒ total ≈ 570M**.

Eso todavía es **~400×** el líder de primecount (1.44M). La criba de Eratóstenes
bit-packed no alcanza el orden.

## Por qué falla

Las tres operaciones dominantes en la ventana medida (`∀ i≤√n/2`, `Σ_p (n/2p)`,
`popcount` con π(n) iteraciones) cuestan, a la resolución de F2, del orden de
~10k·(n log log n) — para n=1000 da del orden de ~10⁵ a ~10⁶, lo cual está muy
por debajo del líder. El costo observado de ~95M/slot no se explica por la
complejidad asintótica sino por **pasos estructurales en Lean**:

1. `clearFrom` elabora a `Nat.rec` sobre `fuel` con cuerpo `clearBit ∘ shiftLeft`
   que involucra creación de un nuevo literal Nat de tamaño **k=n/2 bits** por
   paso (no está step-share, es un número nuevo cada vez). El kernel hace whnf
   de cada `m &&& (full - (1<<<j))` con ~n/2 limbs cada vez. Eso escala como
   `n/(2p)` iteraciones × **limbs/paso** — no por op sino por *tamaño del
   literal intermediario*.
2. `popcountNat` itera π(n) veces y en cada paso construye `v &&& (v-1)`, otro
   literal de tamaño ~n/2 bits que hay que copiar y comparar. Total: π(n)
   × limbs ~ |π(n)| – para n=991, π=167 limbs ⇒ ~30k pasos de kernel puro.
3. El `axiom impl_correct` se rechaza durante elaboración? — **No**, el build
   pasa (verificado). Pero **el export serializa el módulo entero con Mathlib**,
   y eso infla el JSON del export que el instrumento local parsea (3.5–4B).

La métrica **oficial** (que el prompt F3 exige) excluye el parseo del export;
aquí el número representativo es **~28M de "slope" por slot** (diferencia n=991
vs n=85 ≈ 167M / 6 slots), que sigue siendo demasiado. La razón estructural:
incluso con bit-packing en un solo Nat, cada iteración elabora un literal
diferente que el kernel debe procesar **bit a bit** (el δ/ι/whnf sobre `Nat.land`
de dos literales de 32 limbs cuesta |limbs| pasos).

## Conclusión

- La estrategia "criba bit-packed en un solo `Nat`", en el modo en que está
  escrita (limpiando bit a bit con `Nat.land`), **no alcanza el orden del líder**,
  aunque escapa del límite de brecOn estructural.
- Un candidato hipotético que alcanzara 1.44M necesitaría un costo de ~(240k
  instrucciones reales del líder × 1 slot), es decir ~**80–150 instrucciones por
  iteración**. Eso exige que el kernel reduzca la criba como una operación
  *total* en lugar de iteración por iteración — eso requiere, o bien GMP-
  acelerated bitwise-ops (hipótesis #1 del prompt no confirmada en F2), o bien
  codificación Kronecker (pista #2), o bien cambio de paradigma aún más radical.

## Restos útiles que quedan

- `candidates/primecount-sieve-bits/Submission.lean` **compila** con `axiom
  impl_correct` y es reproducible: `python3 scripts/measure.py primecount
  candidates/primecount-sieve-bits --group-check --reps 3` reproduce 25.0B.
- El aprendizaje transferible: para candidatos basados en Nat, evitar loops cuya
  cada iteración construya un literal de k bits (costo de kernel ∝ limbs). En
  cambio, usar operaciones que el kernel trate atómicamente (`Nat.gcd`, `pow`,
  comparaciones grandes), según el cierre de F2.

## Próximo experimento (propuesta, no ejecutada)

Si se retoma F3, la pista más prometedora pasa a ser:
- **primecount sobre `Nat.primeCounting` directo con `Nat.find` reemplazado por
  `powerOfTwoFind`** o similar, saltándose la iteración explícita y confiando en
  una reducción más cerrada.
- O cambiar de problema: **fib** con matmul binario sobre un par (`(a,b) *)
  (a,b)` bit-fundido en un único Nat con un solo `shiftLeft+or`, contado por
  iteraciones logarítmicas (~6 para n=1000). Eso sí ubica el costo en el orden
  del líder.

Pero bajo la regla del prompt, F3 se cierra aquí con veredicto negativo,
sin escribir pruebas.
