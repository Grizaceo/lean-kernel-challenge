# partition-euler — dead-end report (2026-09-29)

## Verdict

**`impl` correcto y ~4x más rápido que el fallback, pero `impl_correct` no cierra en Core Lean puro.**
La apuesta segura sigue siendo `candidates/partition-stream-addblocks` (impl_correct probado, 2.26x sobre foldl).

## Medidas (hoy, serial, scripts/measure.py, métrica oficial user-space)

| Candidato | n=32 INSTRUCTIONS | impl_correct | Notas |
|---|---|---|---|
| partition-euler (este) | **927,800,467** | ❌ FALTA | El impl es `kernel-defeq` al spec en 14/18/22/26/32/36 (gradable.sh verde) |
| partition-stream-addblocks | 1,953,534,628 | ✅ PROBADO | 2.26x sobre foldl; bajo cualquier regla es la ganadora |
| partition-foldl (spec directo) | 3,699,000,000 (histórico) | ✅ PROBADO | Última defensa |

Spread entre reps: 0.10–0.28%, métrica estable.

## Forma exacta del muro (esto era la decisión crítica)

El brief pedía *decidir la forma exacta de la identidad antes de formalizar*. La respuesta, en `Attempt1.lean` (compilable, con `sorry` marcando el muro), es:

```lean
m = Σ_{k≥1} (-1)^{k+1} (p(m - g1(k)) + p(m - g2(k)))    -- (pentagonal)
   = partitionSpec m                                      -- ( por demostrar )
```

donde `partitionSpec m = partAux m m` y `partAux` recurre por **tamaño de parte**, no por offsets pentagonales.

Cualquier paso de la inducción fuerte sobre `m` termina pidiendo esta identidad **en su forma completa**,
sin que la estructura recursiva de `partAux` la sugiera. Las dos vías conocidas son:

1. **Franklin/series formales**: probar `∏_{i≥1} (1 - x^i) = Σ_k (-1)^k x^{g(k)}` en Core.
   Necesita anillo formal de series `ℕ⟦x⟧`, convolución, límites de sumas, y la involución
   de Franklin entre particiones con/sin partes repetidas. En Core Lean 4.33.1 no existe
   `PowerSeries`, `MvPowerSeries`, ni `Fintype` para `Finset.range`. Estimar construcción:
   2 000–5 000 líneas, semanas de trabajo, alto riesgo de cuello en *correctness replay*
   (regla que Breitner anunció podría incorporarse: penalizaría pruebas largas).
2. **Inducción fuerte estilo combinatorio**: biyectar particiones de `m` con la suma alternada.
   Equivale a re-derivar el argumento de Franklin en lógica de Lean sin Mathlib. Mismo orden
   de dificultad.

La nota histórica del 28-Sep (`b456079`) ya lo había anticipado:
*"the pentagonal route is impossible here"* (Contexto: Pietro retiró la suya con
`factoredEulerDenominator` + constantes, diciendo "it was too beautiful to be permitted").

## Lo que sí se obtuvo

- `Attempt1.lean`: el goal exacto donde la inducción se atasca, compilable (exit 0 con `sorry`).
  Marca qué hipótesis faltan en cada rama.
- Cross-check ejecutable `Cross.lean`: kernel-defeq directo `impl = partitionSpec` en n=0/5/14,
  y `decide` sobre literales OEIS en n=14/18/22/26/32/36/50. **Pasó en 3.6 s** con
  `-DmaxRecDepth=10000000 -DmaxHeartbeats=0`.
- Confirmación `gradable.sh partition partition-euler {14,18,22,26,32,36}` → todos GRADEABLE.
- Re-affirmation fallback: stream-addblocks sigue GRADEABLE en n=32, 1.95B instrucciones,
  `impl_correct` intacto.

## Limitaciones

- `impl_correct` para el Euler no se obtuvo. La apuesta agresiva queda *congelada* en
  "impl bueno, prueba faltante".
- Si YZ amplía el rango N (anunciado 16-Sep), la ventaja asintótica de Euler O(√n) sobre
  DP O(n²) puede hacer el 4x más pronunciado en N grande — pero sin prueba no es
  submittable, y en caso de regla de correcteness-cost la prueba kilométrica
  castigaría el ranking aún si se lograra.

## Recomendación

Dejar el trabajo en este estado documentado. No invertir más ciclos en la vía formal.
El fallback `partition-stream-addblocks` queda como única apuesta ranked bajo cualquier
regla plausible.

## Reproducibilidad

```
# Compilar el probe con el muro (sale EXIT=0 con warnings por sorry):
cd problems/partition
lake env lean -DwarningAsError=false ../../candidates/partition-euler/Attempt1.lean

# Medir (serial, nunca paralelo entre candidatos partition):
python3 scripts/measure.py partition candidates/partition-euler/Submission.lean 32

# Gradable en todos los n del brief:
for n in 14 18 22 26 32 36; do bash scripts/gradable.sh partition candidates/partition-euler/Submission.lean $n; done
```

Toolchain: leanprover/lean4:v4.33.1. Core Lean puro, `"packages": []`.
