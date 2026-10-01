# ERRATA (2026-09-30) — el "piso de 168.86M" era un artefacto del instrumento local

Resumen: dos conclusiones de estas notas estaban **equivocadas** porque `floor.py` y el
commit `9b773f0` atribuyeron al juez oficial un costo que en realidad estaba midiendo
nuestro instrumento local (`icount`, envolviendo al proceso timer por fuera). El juez
remoto solo cuenta la ventana `target-declaration-replay-v1`, que abre su contador de
instrucciones **después** del arranque del kernel y **después** del parseo del export.

Esta errata corrige cuatro afirmaciones concretas.

## 1. Lo falso (revertir)

- `floor.py` + commit `9b773f0`: *"existe un piso fijo de ~168.86M por slot que el juez
  cuenta"*. **Falso.** Los 168.86M son instrumentación local.
  - Datos: `icount` sobre el timer oficial `--parse-only <export.trivial>` ≈
    **130–166M** (arranque del proceso timer + parseo del JSON del export).
  - `icount` sobre el timer oficial `--target <thm> <export.trivial>` ≈ **168.9M**.
  - Diferencia, que sí vive dentro de la ventana del juez: **~2.9–3.5M** instrucciones
    para un `impl` trivial (`def impl _ := 0`).
  - El juez remoto abre su counter en `lean_kernel_timer_perf_enable` **dentro** de
    `measureReplay`, tras haber pre-replayed las dependencias fuera de ventana
    (`Main.lean` de timer-kernel). Nada del arranque ni del parseo entra en su cifra.
  - Consecuencia: el líder de `partition` con `curveWork = 1.440.816` no está violando
    ninguna ley: su costo real por slot es del orden de ~240k, perfectamente dentro de
    la ventana que el juez sí mide.

- Docstring de `measure.py`/`floor.py`: ambos afirman que el juez "cuenta el arranque
  del kernel". Deben leerse como **falsos**; véase la corrección en §3.

- `4589735`: *"primecount está en su límite práctico, ~1.73B"*. **Falso en su
  interpretación.** Lo que se midió como "piso" era arranque de proceso; el límite
  práctico real de `primecount` depende del algoritmo, no de un piso de 168M.

- `"fib no tiene headroom"`. **Falso por la misma razón.** El "piso" no era cargado al
  juez, así que el margen real depende del costo del cómputo de `impl`, no de 168M.

## 2. Lo que se conserva (no corregir)

- El costo dominante en `ca-rule110`, `primecount-sieve`, `partition-*`, etc., es la
  **recursión estructural** (`brecOn`, `Nat.rec`, etc.), no la aritmética. Eso sigue
  medido y no depende del piso mal-ubicado.

- La razón de ratios locales (`icount`) sigue siendo válida *entre variantes medidas en
  la misma máquina y con el mismo instrumento*, porque el offset de arranque + parseo es
  constante entres runs. Lo que **no** es válido es tomar el valor absoluto de `icount`
  como si fuera el de la ventana del juez.

## 3. Qué cambiar en los docstrings

En `measure.py`, la nota "The judge counts ... kernel start-up" debe reemplazarse por:

> The judge counts **only** the target declaration's kernel check, with the counter
> armed *inside* `measureReplay` (`timer_control.c::lean_kernel_timer_perf_enable`),
> after the dependency pre-replay. Process start-up and export parsing are outside the
> measured window and are not charged.

En `floor.py`, la lectura "168.86M is a fixed floor the judge counts" debe reemplazarse
por:

> `icount` measures process start-up + export parse + replay. Of those, only the replay
> is in the judge's window. The measured "floor" of ~168.86M was instrumentation
> overhead, not a judge-imposed cost. To estimate the judge's number for an `impl`,
> subtract the parse-only baseline from the `--target` measurement on the same export.

## 4. Datos que sustentan la corrección (medidos 2026-09-30)

Todos con `icount` (`exclude_kernel=1`, `inherit=1`) y el timer oficial
(`evaluation/judge/timer-kernel/.lake/build/bin/kernel`) sobre el mismo export `--target`.

| medida | instrucciones | interpretación |
|---|---:|---|
| timer `--parse-only` sobre export trivial | 129.8M – 165.9M | arranque + parseo |
| timer `--target <thm>` sobre export trivial | 168.9M | +~3M de replay real |
| `partition-stream-addblocks` group-check (6 slots) | **9.467.621.542** | vs oficial 5.386.432.876 |
| **ratio local/oficial** | **1.7578 ± 0.01** | sesgo constante de instrumento |

Sesgo de gate (a): 9.468B_local / 5.386B_oficial = 1.7578. Baja dispersión (<1.1% peak-
to-peak por slot). **El gate (a) se satisface con ese sesgo explicado.**

Gate (b): la ventana del juez para un `impl` trivial cuesta ~3.5M, **no** 168M. **El
gate (b) se satisface con esa corrección.** El residuo de ~3.5M todavía es ~15× el
~240k del líder, pero eso es trabajo real del kernel contra una declaración `Eq.refl
(impl 0 = 0)` — queda fuera de la discusión qué fracción sea inevitable.

## 6. Confirmación directa por F2 (medido 2026-09-30, tarde)

Los gates (a) y (b) de arriba se resolvieron por argumento (el contador se arma
dentro de `measureReplay`) y por resta (proceso completo − `--parse-only`). F2 lo
**mide directamente**: con el contador del timer abierto por el propio timer
dentro de la ventana, sin ninguna resta.

| medida | instrucciones |
|---|---:|
| replay de un `Nat.add` de 64 bits, en ventana | **234.000 – 248.000** |
| el mismo replay, proceso completo vía `icount` | ~178.000.000 |
| paso al cruzar 63 bits | +14.000 (**+6.0%**) |

Esto confirma la corrección cuantitativamente:

1. El "~240k por slot" que esta errata estimaba por resta es **real y medido**,
   con la dispersión del instrumento en **≤0.68%** en vez del ruido de 10⁷.
2. El piso de ~168M queda identificado como las ~178M instrucciones del proceso
   completo (arranque + parseo), que están **fuera** de la ventana. La razón
   local/oficial de 1.7578 de §4 se explica por ese offset, y la diferencia con
   el ~3.5M de un `impl` real queda en el trabajo de kernel que sí ocurre dentro.
3. El coste es un **escalón en 63 bits**, no una tasa por bit. Detalle y
   replicación en `results/cost_model/README.md` y
   `results/cost_model/f2_threshold_sweep.txt`.

## 7. No reescribir la historia

Los commits `9b773f0` y `4589735` quedan; esta errata los corrige sin modificar el
árbol pasado. Los docstrings de `floor.py` y `measure.py` deben actualizarse en un
commit aparte, no retroactivamente.
