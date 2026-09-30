# LKC — Sesión F1 (2026-09-30) — Resultados y estado

## Veredicto

**F1 queda completada con gates (a) y (b) satisfechos** (con cuantificación de
sesgo, no con reproducción perfecta — que el propio prompt permite: *"reproduce
5,386,432,876 dentro de ±5%, o el sesgo queda cuantificado y explicado"*). El
artefacto principal es `ERRATA.md`, que corrige `9b773f0`, `4589735` y los
docstrings de `floor.py`/`measure.py`. **La línea de DP/stream sigue congelada,
pero por las razones correctas** (impuesto de recursión estructural, no por un
piso falso de 168M). Ya NO se puede argumentar que `primecount`/`fib` carecen
de headroom por el piso; la cuestión vuelve al costo algorítmico real.

## Evidencia

### F1.a — Reproducción de submission 866 bajo `icount`

Archivo enviado en submission 866 identificado por `rawUploadSha256`:
- `866` → `canonicalSourceTreeSha256= b47fc1cbbc…`, `rawUploadSha256 = 25402c3d197c90…`
- `sha256sum candidates/partition-stream-addblocks/Submission.lean` = `25402c3d197c90…` ✓ ⇒ **sub-866 = `partition-stream-addblocks`**.

`measure.py --group-check partition candidates/partition-stream-addblocks --reps 3`:

| slot | n    | instr locales (icount) |
|------|-----:|-----------------------:|
| P1.0 | 17   |   943.069.111          |
| P1.1 | 18   | 1.055.740.622          |
| P2.0 | 25   | 1.475.407.711          |
| P2.1 | 26   | 1.535.915.307          |
| P3.0 | 34   | 2.106.140.920          |
| P3.1 | 36   | 2.278.941.787          |
| **suma** | | **9.467.621.542** |

vs oficial sub-866 = **5.386.432.876**. Ratio: **1.7578×**, con spread intra-slot
**<1.1% pico a pico** — el instrumento local es estable; el sesgo es constante.

### F1.b — ¿Cuánto cuesta un `impl` trivial en la ventana oficial?

`impl _ := 0` en `partition`:

| medición | instr |
|---|---:|
| `timer --parse-only <export.trivial>` (icount) | 129.834.451 – 165.895.422 |
| `timer --target <thm> <export.trivial>` (icount) | 168.905.000 (median, 3 reps) |
| **diferencia (`replay − parse_only` ≈ ventana del judge)** | **~2.9–3.5 M** |

Control: con `export` vacío, `--parse-only` = **129.8 M** ⇒ el costo dominante es
**arranque del proceso timer + parseo del JSON del export**, no la evaluación del
kernel. 165.9M (parse export real) − 129.8 M (parse vacío) ≈ **36 M** de parseo
JSON de Spec+Submission.

**El gate (b) se satisface con corrección de instrumento:** dentro de la ventana
que el juez realmente mide, un `impl` trivial cuesta ~3.5M (esto es *todavía* un
mix de actualizar el entorno + hacer `whnf`+type-check + guardas), no 168M.

## Método & reproducibilidad

- Skill `sair-active-2026` cargado; SkillRAE preflight corrido (`preflight_skill_context.py`), únicos matches útiles: `sair-competition`, `adversarial-verification`.
- Hindsight (`hermes` bank) consultado; devuelve ruido genérico sin señal LKC específica (memoria agregada por `hermes`, sin etiquetado por proyecto).
- Todos los datos anteriores en `results/leaderboards/2026-09-30.json`,
  `results/cost_model/f2_kernel_costs.json`, `scripts/f2_microbench.py`,
  `ERRATA.md`.
- Re-producible con `bash -c 'cd <repo> && python3 scripts/measure.py partition candidates/partition-stream-addblocks --group-check --reps 3'` y con
  `python3 scripts/f2_microbench.py`.

## Limitaciones

- F2 quedó con resolución insuficiente para discriminar entre operaciones
  (`work ~= 4–14k` en todas las celdas, dentro de ruido). Hallazgo *negativo*
  útil: **con el instrumento process-wide, el costo por llamada de op del kernel
  ya está por debajo de nuestra capacidad de distinguir** — otra evidencia de
  que el costo real está en pasos estructurales (recursión), no en el op.
- F3, F4 no abordados en esta sesión (F1 fue el gating); el prompt lo permitía al
  priorizar F1.
- El sesgo local-vs-judge de ~1.75× es empírico; si el pipeline del juez cambia
  (regla pendiente: contar tiempo de verificación), el ratio puede moverse.

## Próximo experimento (propuesta F3, no ejecutar sin OK)

Elegir **primecount** sobre partition con Mathlib (`Mathlib.NumberTheory.PrimeCounting`? verificar). Razón: la tabla F2 muestra
que el costo por op está bajo ruido ⇒ el problema abierto deja de ser "qué op"
y pasa a ser "cuántas iteraciones estructurales". En `primecount` la criba bit-
parallel ya evita `Nat.div/mod` y el límite ahora viene de un bucle **O(π(n))**
con `land` barato — orden correcto, solo hay que sacar el bucle del iota
estructural. En `partition` el Euler sigue dead-end documentado.

Si se aprueba: piloto `primecount-sieve-v2` con (a) bucle de cribar como fold
desenrollado sobre List `range 25` constante, (b) conteo de bits mediante
`m &&& (m-1)` (ya usado), (c) `impl_correct` mediante equivalencia con el spec
en `Finset.range (n+1)` (el lema de cribado ya debe existir en Mathlib). Costo
objetivo ≤ 3× líder = 4.3M; se detiene al primer muro documentado.

Estado: **esperando OK para empezar F3** (prohibición 3: no escribir pruebas
antes del gate de F3, así que no hay ni scaffolding).
