# F9 — la aritmética es plana: el coste real es el suelo (2026-10-05)

Métrica: instrucciones en `KERNEL_TIMING`, frontera
`target-declaration-replay-v1`. Instrumento: `.verify/timer-kernel-local`,
`LK_EXCLUDE_KERNEL=1`, reps 3, harness idéntico a F8.

Pre-registrado en `scripts/f9_structural_arith.py`. Cierra el hueco que F8 dejó
explícitamente abierto: `Nat.succ` (aritmética estructural, sin GMP) estaba sin
medir porque `Lean.mkApp1` no existe. Esta vez el fallback documentado (G4:
`Lean.mkApp`) se usó desde el inicio, y queda registrado que se usó.

## La pregunta

F8 había establecido:

```
suelo por declaración (118.230) + 1 unfold (122.656) = 240.886 > slot de campeón (238.082)
```

Es decir: un campeón no puede pagar ni **un** unfold más el suelo. Si existiera
una operación aritmética **notablemente más barata** que `Nat.add`, un candidato
podría pagar varias por slot en vez de una. `Nat.succ` era el candidato natural:
es recursión estructural sobre `Nat`, sin asignación GMP, mientras que `Nat.add`
y `Nat.sub` sí la hacen.

## 1. Las celdas

| celda | instrucciones | vs `Nat.add` | vs suelo | qué |
|---|---:|---:|---:|---|
| **E-add-small** | **206.328** | **0,988×** | 1,745× | `Nat.add 1+1` — la más barata |
| F-add-large | 206.408 | 0,988× | 1,746× | `Nat.add` de 2×10¹² (**40× más operandos**) |
| B-succ-large | 207.383 | 0,993× | 1,754× | `Nat.succ 100000` |
| A-succ-small | 207.597 | 0,994× | 1,756× | `Nat.succ 6` |
| D-xor | 237.850 | 1,139× | 2,012× | `Nat.xor` de 4 bits |
| C-pred | 273.752 | 1,310× | 2,315× | `Nat.pred 9` |

## 2. Veredictos

| | |
|---|---|
| G2 spread ≤ 5% | PASS (peor 0,37%) |
| G3 H9.1 hay aritmética más barata | **RECHAZADA** — la más barata es 0,988× de la referencia |
| G4 fallback documentado | `Lean.mkApp` en todas las celdas; ninguna sustitución silenciosa |
| G5 reportar la más barata | `E-add-small`, 206.328 — el piso de **una** operación |

## 3. El resultado: la aritmética es plana

Tres cosas se Midieron, y las tres apuntan igual:

1. **GMP vs estructural no importa.** `Nat.add` (206.328) y `Nat.succ` (207.597)
   cuestan lo mismo. La asignación GMP no es un componente de coste.
2. **El tamaño del operando no importa.** `Nat.add` de 2×10¹² cuesta 206.408,
   contra 206.328 de `1+1`. **40× más operandos, diferencia de 80
   instrucciones.** Esto es F6 carryover confirmado por segunda vía.
3. **El tipo de operación importa poco.** `add`/`succ`/`xor` están en
   206–238k; solo `Nat.pred` se sale (273.752).

La conclusión que F9 establece: **toda aritmética cuesta ~1,75× el suelo de
declaración, independientemente de cómo se compute.** No hay atajo por elegir una
operación "más barata" — el piso ya está medido.

## 4. La repartición corregida del coste

Con F8 y F9 juntos, el coste de una operación aritmética se descompone:

| componente | instrucciones | fracción |
|---|---:|---:|
| suelo por declaración | ~118.230 | 57% |
| aritmética sobre el suelo | ~88.098 | 43% |
| **total por operación** | **~206.328** | 100% |

El suelo es **más de la mitad** del coste. Ese es el hallazgo estructural de F8/F9
combinados, y es lo que reorganiza el diseño de un candidato.

## 5. El muro duro

Presupuesto de un campeón por slot: **238.082** instrucciones.

| qué cabe | coste | ¿cabe? |
|---|---:|---|
| 1 operación aritmética (suelo ya incluido) | 206.328 | sí, margen 31.754 |
| suelo + 1 operación | 324.558 | **no**, excede en 86.476 |
| suelo + 2 operaciones | 530.886 | **no**, excede en 292.804 |
| 2 declaraciones-suelo puras | 236.460 | sí, justo (99,3% del presupuesto) |

**El presupuesto compra una operación, y nunca dos.** Esto está medido dos veces
(F8 por el suelo, F9 por la aritmética) y coincide. Es el muro real del challenge
bajo esta instrumentación.

## 6. Qué significa para el packing (y corrige el razonamiento de F6/F7)

F6/F7 showed packing winning 33,47× at 64 lanes and up to 4,096 with no cliff. F9
explains **why**, and corrects the implicit explanation:

> El packing no gana porque la anchura sea barata — F9 acaba de medir que la
> anchura **no** cuesta nada (40× más operandos = +80 instr). El packing gana
> porque **amortiza el suelo de declaración entre muchos valores**.

A 4.096 carriles: 396.279 − 118.230 (suelo) = 278.049 de aritmética para 4.096
valores = **~68 instr/valor**, contra los ~122.656 instr/valor de un unfold. Eso
es **~1.804× mejor**. El margen real del packing es ése, y es aún mayor de lo que
F6 sugería, porque F6 atribuyó la ventaja a la anchura cuando en realidad venía
del reparto suelo/aritmética.

## 7. La tensión que sigue abierta (de F8, sin resolver)

F8 dejó una discrepancia honesta: suelo (118.230) + 1 unfold (122.656) = 240.886
**supera** el presupuesto del campeón (238.082), pero el tablero sugiere ~2
unfolds/slot. F9 no la resuelve; la hereda.

Las tres explicaciones de F8 siguen en pie y ninguna se ha verificado:
1. Mi frontera cuenta user-only (`LK_EXCLUDE_KERNEL=1`); el juez cuenta
   user+kernel. La **razón** es la misma máquina, pero el absoluto lleva sesgo.
   Por eso todo lo anterior son cifras **relativas**.
2. El campeón normaliza menos trabajo del que paga mi sonda.
3. La micro-operación del campeón no es un unfold de `Nat.rec`.

**No se afirma cuál es.** Lo que sí es sólido e independiente de resolverla: el
reparto suelo/aritimética, y que el presupuesto compra una operación.

## 8. Qué NO se puede concluir

- El suelo (118.230) se midió con sondas `Eq.refl` sobre literales; puede no ser
  el mismo suelo que paga un `impl` real con estructura.
- Nada de esto es un candidato construido y medido en el plan oficial. Es un
  mapa de costes, no una promesa de ranking.
- Las absolutas no son comparables slot a slot con el leaderboard (semilla
  oculta por cohorte + frontera de instr).

## 9. El siguiente paso

F8 y F9 han establecido el coste con suficiente precisión. La pregunta que queda
no es de microcoste sino de **diseño**: dado que el presupuesto compra ~1
operación, ¿se puede escribir un `impl` de `partition` cuya verificación
reduzca a **una sola operación aritmética** que cubra la fila entera del DP?

Eso no es un experimento de coste, es un problema de construcción de candidato,
con la aritmética ya resuelta: ~36 valores en una operación de ~206k, dentro del
presupuesto. El packing es la herramienta; F9 dice por qué funciona.

## 10. Artefactos

- `scripts/f9_structural_arith.py` — aritmética estructural vs GMP (pre-registrado).
- `results/cost_model/f9_structural_arith.{json,txt}`.
- Continuación: F5 (impuesto por unfold), F6/F6b (packing 33×), F7 (techo y muro),
  F8 (suelo de declaración), F9 (aritmética plana).