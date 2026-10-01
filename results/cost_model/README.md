# F2 — modelo de costes del kernel (reconstruido 2026-09-30)

Tabla de coste real de replay para un único `Nat.<op> a b = v`, medido en la
**ventana que puntúa el juez**: el campo `instructions` del registro
`KERNEL_TIMING`, frontera `target-declaration-replay-v1`. No hay restas, no hay
baseline.

## Por qué se reconstruyó

La tabla anterior queda **anulada**. Sus 28 celdas no eran mediciones:

| defecto | consecuencia |
|---|---|
| `scripts/f2_microbench.py` validaba el export con `size != 0` | un export de **173 B** (solo header) pasaba el filtro |
| ese export venía de un `lean4export` que hace `PANIC: Constant F2Probe.check not found` **y sale con rc=0** | los dos guards (`rc != 0` y `size == 0`) lo dejaban pasar |
| `scripts/icount.c` no miraba el exit code del hijo | imprimía `INSTR_TOTAL` de un timer que había fallado |
| el teorema no existía: `theorem check := rfl` a nivel de fuente **no llega al entorno exportado** | se medía el costo de arrancar y fallar |
| el método era proceso-completo menos `--parse-only` | piso de ~1.8e8 contra señal de ~1e4 |

Ninguna de esas celdas era un error de las operaciones: eran el costo de un
proceso muerto.

## El instrumento

Tres cambios, todos verificables:

1. **El teorema se declara como lo hace el juez**, con `Lean.addDecl` dentro de
   `run_meta` (`scripts/f2_harness.py:probe_source`), no con `theorem ... := rfl`.
   El kernel solo tiene que reducir `Nat.op a b` hasta `v`, igual que al
   puntuar una submission real. Los operandos entran como literales: `2^k`
   deja potencias grandes sin evaluar por el elaborador
   (`exponentiation.threshold`), que es otra forma de medir un teorema
   inexistente.

2. **Se mide la ventana, no el proceso.** `.verify/timer-kernel-local/` es una
   copia byte a byte de `evaluation/judge/timer-kernel` con un opt-in
   `LK_EXCLUDE_KERNEL=1`, necesario porque `timer_control.c` pide user+kernel y
   `perf_event_paranoid=2` deniega ese `open()` en esta máquina. Con la variable
   sin poner, el binario se comporta **idéntico al del juez** — ese control
   está registrado abajo.

3. **Abortar, no registrar.** Si el build, el export o el replay fallan, la
   corrida aborta; una celda fallida nunca se escribe como número. El replay
   además exige `phase=complete` **y** que `target` sea exactamente el teorema
   pedido, que es la verificación semántica real.

## Resultado

28/28 celdas válidas, 7 operaciones × {16, 32, 64, 128} bits, 5 reps.
Spread intra-celda peor caso **0.68%** (antes: ruido de 10^7 contra señal de 10^4).

### El coste es una función escalón, no lineal

`f2_threshold_sweep.txt` barre 30 anchos de 4 a 256 bits. El barrido localiza
el escalón y desmonta la lectura lineal de la tabla de 4 puntos:

| región | coste en instrucciones |
|---|---|
| meseta baja (4–62 bits, 19 anchos) | ~234.100, spread interno 0.47% |
| transición (63 bits) | ~241.500 (+3.2%) |
| meseta alta (64–256 bits, 10 anchos) | ~248.100, spread interno 0.43% |

**El escalón está en 63 bits y vale +14.000 instrucciones (+6.0%)**, que es
donde un `Nat` deja de caber en la palabra de máquina del kernel y pasa a
array de dígitos. Replicado en tres corridas independientes: 14.058 / 14.054 /
14.022 (+6.01% / +6.00% / +5.99%).

Un payload de 256 bits cuesta lo mismo que uno de 64. Los `147 instr/bit` que
salían del ajuste lineal no eran una tasa: era el escalón de 63 bits
esparcido sobre una recta.

### Ranking por operación (H2, no rechazada)

`Nat.land` ≈ `Nat.lor` (~182k) < `Nat.mul` (~207k) < `Nat.shiftLeft` (~208k) <
`Nat.sub` (~233k) < `Nat.add` (~234k) < `Nat.xor` (~246k). La separación entre
operaciones es de **4.0x** la pendiente ajustada, muy por encima del
instrumento: las operaciones sí difieren.

## Consecuencia para el modelo de costes de la competición

El payload es una **minoría** del replay de un solo teorema. El coste fijo por
declaración replayada es ~234k–248k instrucciones; la aritmética atribuible al
payload llega como mucho a ~72k.

> Lo que cuesta tiempo en un slot es el **número de declaraciones replayadas**,
> no su tamaño. Los líderes (62–90 µs/slot) pagan ~180k instrucciones por
> teorema sea cual sea su aritmética. La única decisión de anchura que paga es
> quedarse bajo 63 bits, y vale 6%.

Esto confirma cuantitativamente la ERRATA de F1: la lectura de 168M era
instrumental (proceso completo sobre un hijo fallido), no el coste del kernel.

## Reproducir

El instrumento es un artefacto de build, no está versionado (`.verify/` está en
`.gitignore`, y 120 MB no van al repo). Se reconstruye desde el árbol del juez,
que sí está versionado:

```bash
python3 scripts/f2_build_local_timer.py  # reconstruye .verify/timer-kernel-local
python3 scripts/f2_instrument_check.py   # valida el instrumento y el control
python3 scripts/f2_cost_model.py         # tabla de 4 puntos, 28 celdas
python3 scripts/f2_threshold_sweep.py    # barrido denso, localiza el escalón
```

`f2_build_local_timer.py` aborta si el `timer_control.c` del juez cambió: cada
uno de los tres parches debe coincidir exactamente una vez, así que una
derivación del upstream produce un fallo ruidoso en vez de un binario
instrumentado distinto del que se cree.

Salidas: `f2_kernel_costs.json`, `f2_linear_fit.txt`, `f2_threshold_sweep.txt`,
`f2_threshold_sweep.json`.

## Controles registrados

- **Aborta en fallo:** un header de 173 B dispara `ProbeError` y la corrida se
  detiene (ejercido de verdad: cortó en `Nat.add@16` antes de relajar el guard).
- **El guard semántico manda:** `KERNEL_TIMING.target` debe igualar el teorema
  pedido; un export presente pero equivocado no pasa.
- **Fidelidad del timer parcheado:** sin `LK_EXCLUDE_KERNEL=1` el binario local
  falla igual que el juez (`cannot open kernel timing PMU events: Permission
  denied`); con la variable entrega la ventana.
- **El nombre del teorema no se puede comprobar con grep:** el export es
  JSON-lines y cada nombre va registrado en su propia línea, así que
  `F2Probe.check` nunca aparece como cadena contigua. Un guard que lo busque
  rechaza un export válido de 26 kB; por eso la verificación semántica es la del
  timer, no una búsqueda de texto.
- **Premisas verificadas de forma independiente:** `import F2Probe` carga pero
  `F2Probe.check` es *unknown identifier*, luego el teorema nunca se declaraba.
  Eso es lo que hace el export inválido, confirmado sin depender del export.
