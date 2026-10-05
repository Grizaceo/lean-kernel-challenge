# F7 — el techo del empaquetado, y el muro aritmético del challenge (2026-10-05)

Métrica: instrucciones en `KERNEL_TIMING`, frontera
`target-declaration-replay-v1`. Instrumento: `.verify/timer-kernel-local`,
`LK_EXCLUDE_KERNEL=1`. Harness idéntico a F6b (una sola llamada `mkApp2` sobre
`Nat.add`), así que las cifras son comparables con F6b directamente.

Pre-registrado en `scripts/f7_packing_ceiling.py` antes de mirar ningún número.

## La pregunta

F6b mostró que empaquetar gana 33,47× a 64 carriles, pero solo hasta ahí: el
margen crecía sin cota **en el rango medido**, lo cual no dice si hay techo. Y 64
carriles está lejos del rango interesante: `p(36)=17977` cabe en 15 bits, así
que una fila del DP de ~36 entradas necesita ~576 bits — del orden de 540
carriles a 65 bits.

F7 barre **[64, 4096] carriles**, que es donde el operando se acerca al límite
de `Nat` de GMP y la razón puede por fin girar.

## 1. El barrido

| carriles | bits del operando | instrucciones | vs 64 carriles | vs slot de campeón |
|---:|---:|---:|---:|---:|
| 64 | 4.160 | 245.053 | 0,998× | 1,03× |
| 128 | 8.320 | 250.766 | 1,021× | 1,05× |
| 256 | 16.640 | 254.533 | 1,036× | 1,07× |
| 512 | 33.280 | 263.482 | 1,073× | 1,11× |
| 1.024 | 66.560 | 282.595 | 1,150× | 1,19× |
| 2.048 | 133.120 | 320.738 | 1,306× | 1,35× |
| 4.096 | 266.240 | 396.279 | 1,613× | 1,66× |

Coste marginal por carril adicional:

| hasta | instr/carril |
|---:|---:|
| 128 | 89,27 |
| 256 | 29,43 |
| 512 | 34,96 |
| 1.024 | 37,33 |
| 2.048 | 37,25 |
| 4.096 | **36,89** |

**No hay cliff.** El coste marginal por carril se estabiliza en **~37
instrucciones** desde 512 hasta 4.096. G4 (rechazar si el marginal sube
monótonamente) no se dispara; H7.2 no se rechaza. El crecimiento es lineal con
pendiente minúscula: 64× más carriles cuesta 1,61×.

H7.1 (≤1,25× hasta 4.096) **se rechaza** en 2.048 y 4.096 carriles. Ese era el
criterio estricto; la verdad medida es que el crecimiento es lento y regular, no
abrupto.

## 2. El límite duro: el intercepto supera el presupuesto

Ajuste lineal sobre los siete puntos:

```
coste = 244.590 + 37,1 · carriles
```

El **intercepto (244.590) ya supera el presupuesto de un campeón por slot
(238.082)**. Carriles que caben:

```
(238.082 − 244.590) / 37,1 = −176
```

**Negativo.** No existe ningún número positivo de carriles que quepa en el
presupuesto de un campeón. Y el margen es estrecho: el mínimo medido de una
`Nat.add` es 234.175 instr (4 bits), y `floor(238.082 / 234.175) = 1,02` →
**una sola operación**, con 3.907 instrucciones de residuo (1,67%).

Esto es un dato fuerte y hay que decirlo sin adornarlo: **el presupuesto de un
campeón por slot no alcanza ni para una única operación aritmética ancha más
un unfold.** Un unfold cuesta ~121.247, una operación ~234.175: juntos son
~355.422, o sea **1,49×** el presupuesto.

### Tres lecturas posibles, y por qué la conclusión operativa no depende de cuál

1. **El campeón ejecuta ~1 operación por slot**, la más barata posible, y el
   resto es residuo. Un segundo unfold no cabe (121k > 3.907).
2. **El campeón no ejecuta `Nat.add`**: usa operaciones más baratas que nunca
   medimos (`Nat.sub`, comparaciones, o sustitución sin entrar al kernel).
3. **La ventana del campeón se midió con otra instrumentación** (user+kernel,
   LHC con contadores). Entonces las absolutas no son comparables y solo valen
   las relativas.

En las tres, la conclusión operativa coincide:

- **Dos operaciones por slot son imposibles** (~470k = 2× el campeón).
- **Un unfold más una operación no caben** (~355k = 1,49×).
- Cualquier candidato viable paga **una** operación por slot, no dos.
- Y para bajar de ahí no sirve hacer la operación más barata: ya está en el
  suelo. El único margen es **empaquetar más valores por operación**.

## 3. La ventaja por valor, que es la cifra comparable

`instr/valor` para el empaquetado, contra los 121.247 instr/valor de un unfold
(F5):

| carriles | instr/valor | ventaja por valor |
|---:|---:|---:|
| 64 | 3.829 | 32× |
| 256 | 994 | 122× |
| 1.024 | 276 | 439× |
| 4.096 | **96,7** | **1.253×** |

La ventaja por valor **sigue creciendo** con los carriles, pero el coste total
también, y el presupuesto pone el techo. El punto de equilibrio —donde la
ventaja por valor es máxima subjecto a caber en el presupuesto— está en
**1 carril**, porque a partir de ahí ninguna operación cabe.

## 4. Por qué G5 rechazó H7.3, y por qué la pregunta estaba mal enfocada

G5 pedía «512 carriles bajo 238.082 instr». Medido: 263.482 = **1,11×** el
presupuesto → H7.3 rechazada. Pero el criterio estaba mal planteado: un slot no
tiene que empacar 512 valores, tiene que **avanzar la fila**, que son ~36. El
número que importa es «cuántas operaciones caben en el presupuesto», y la
respuesta es **una**.

La conclusión útil de F7 no es «512 carriles no caben», es:

> El empaquetado compra una fila entera de ~36 valores en **una** operación, a
> un coste estimado de ~245.924 instr (1,03× el presupuesto del campeón), frente
> a los **25.219.376** instr (106×) que la recurrencia dispersa de Euler necesita
> para el mismo p(36). El empaquetado compra esa fila **103× más barato**.

Y ese ~245.924 es precisamente el intercepto: una fila de 36 valores cabe en
2.340 bits, muy por debajo de donde el coste se mueve.

## 5. Veredictos

| | |
|---|---|
| G2 spread ≤ 5% | PASS (peor 0,37%) |
| G3 H7.1 ≤1,25× | RECHAZADA (1,31× en 2.048; 1,61× en 4.096) |
| G4 H7.2 sin cliff | NO RECHAZADA (marginal ~37 instr/carril, plano) |
| G5 H7.3 512 bajo presupuesto | RECHAZADA (1,11×) |
| G6 | No se dispara: el marginal sigue plano, no creciente |

## 6. Qué NO se puede concluir

- El barrido llega a 266.240 bits. G6 de F6 pedía declarar «UNRESOLVED» si el
  extremo medido siguiera siendo sublineal, y aquí **lo sigue siendo**: el
  marginal de 36,89 instr/carril no muestra giro. **No hay techo hasta 4.096
  carriles; no hay evidencia de que exista un techo en ninguna parte.** El
  límite real, si existe, está más allá del rango medido.
- El barrido es de **coste por operación**, no de una implementación real. No
  existe todavía un candidato `partition` empaquetado y medido en el plan
  oficial.
- La comparación con el tablero sigue limitada por `PERF_SEED` local frente a
  la semilla oculta por cohorte. F7 usa el mismo plan local que F2–F6, así que
  es comparable con ellos, **no** slot a slot con el leaderboard.
- El intercepto de 244.590 se extrapoló desde un ajuste; la pendiente de 37,1
  es estable pero el intercepto depende del punto de partida.

## 7. El siguiente paso exacto

F7 decide el microcoste. Lo que falta es **la ruta**: construir el candidato
`partition` con la fila del DP empaquetada en un `Nat` y medirlo en el plan
oficial. La aritmética dice que la fila cabe en una operación; F7 dice que esa
operación cuesta ~1,03× el presupuesto de un campeón. Las dos cosas juntas son
un mapa, no una promesa: hay que construirlo y medirlo antes de afirmar nada
sobre el ranking.

## 8. Artefactos

- `scripts/f7_packing_ceiling.py` — barrido del techo (pre-registrado).
- `results/cost_model/f7_packing_ceiling.{json,txt}`.
- Continuación: `LKC_2026-10-05_F5_step_tax.md` (impuesto por paso),
  `LKC_2026-10-05_F6_packing.md` (sublineal + margen del empaquetado).