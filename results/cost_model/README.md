# F2 — instrumento de micro-bench para operaciones del kernel

`f2_microbench.py` mide el costo de un único op `Nat.<op> a b` en la métrica
real del judge (kernel replay de `Eq.refl (op a b = v)`) para `bits ∈ {64, 1k,
10k, 100k}`.

Metodología (derivada del hallazgo F1 / `ERRATA.md`):

- El timer oficial solo cuenta instrucciones **dentro** de `measureReplay`, pero
  esta máquina no puede abrir esa ventana (`perf_event_paranoid=2` excluye
  kernel). En lugar de eso corremos el timer binario **bajo `icount`**
  (process-wide, `exclude_kernel=1`) y restamos una baseline `--parse-only` del
  mismo export. El residual aproxima el costo de la ventana del judge.

- 3 repeticiones por celda; spread reportado.

- Las expresiones usan `2^(bits-1)`, `2^(bits/2)`, etc., para no depender de
  constantes derivadas de los inputs oficiales.

`results/cost_model/f2_kernel_costs.json` queda con:

```json
{"Nat.add@64": {"total": N, "parse_only": M, "replay_minus_parse": N-M, "raw": [..]}}
```

`replay_minus_parse` es el número útil para F3.
