# F6 — el cliff de empaquetado, y por qué el challenge tiene una dirección (2026-10-05)

Métrica: instrucciones en `KERNEL_TIMING`, frontera
`target-declaration-replay-v1`. Instrumento: `.verify/timer-kernel-local`,
`LK_EXCLUDE_KERNEL=1`, calibrado (234.552 instr, spread 0,55%).

## La contradicción que este experimento resuelve

El tablero dice que el rank 1 de `partition` puntúa 1.428.492 instrucciones
sobre 6 slots = **238.082 por slot**. Mi coste medido de **una sola**
`Nat.add` trivial en la ventana puntuada es **234.552** (F2/F5). Es decir: el
presupuesto entero de un campeón por slot es **algo menos que una única
operación trivial**.

Y `p(36) = 17977`. F5 ya demostró que la recurrencia dispersa de Euler necesita
208 términos unfoldables para p(36) = ≥106× el presupuesto de un campeón. El
clúster de cabecera **no puede** estar haciendo la aritmética que el spec
sugiere.

La única lectura que queda es **empaquetado**: la fila entera del DP dentro de
un `Nat` ancho, una operación que hace avanzar muchos valores a la vez, y un
«paso» es una operación sobre un número grande en vez de una sobre un número
pequeño. F2 ya había visto que el coste es plano de 4 a 65 bits — la firma de
esa hipótesis — pero paró en 65 bits, y el rango interesante está mucho más
arriba: los mayores slots de `polydisc` llevan coeficientes de 3484 bits.

Si eso es lo que hace la cabeza, el objetivo de optimización de todo el
challenge es **un solo número: el punto donde el coste por operación deja de
ser plano.**

## 1. Serie A — ¿dónde está el cliff?

`scripts/f6_packing_cliff.py`, pre-registrado. Un `Nat.add`, anchura barriendo
muy por encima del techo de 65 bits de F2.

| bits | instrucciones | vs 4-bit | Δ |
|---:|---:|---:|---:|
| 4 | 234.175 | 1,000× | — |
| 16 | 234.798 | 1,003× | 623 |
| 64 | 242.107 | 1,034× | 7.932 |
| 256 | 249.614 | 1,066× | 15.439 |
| 1.024 | 250.358 | 1,069× | 16.183 |
| 4.096 | 252.324 | 1,078× | 18.149 |
| 16.384 | 262.507 | 1,121× | 28.332 |

**Coste marginal por bit añadido, por octava:**

| intervalo | Δ instr | Δ bits | instr/bit |
|---|---:|---:|---:|
| 4 → 16 | 623 | 12 | 51,9 |
| 16 → 64 | 7.309 | 48 | 152,3 |
| 64 → 256 | 7.507 | 192 | 39,1 |
| 256 → 1.024 | 744 | 768 | **1,0** |
| 1.024 → 4.096 | 1.966 | 3.072 | **0,6** |
| 4.096 → 16.384 | 10.183 | 12.288 | **0,8** |

**Lectura honesta: el coste es SUBLINEAL en anchura.** 4.096× más operandos
(4 → 16.384 bits) cuesta solo **1,121×**. La aritmética del kernel **no** es
lineal en bits: el coste por operación está dominado por un fijo de ~234k que
no mira el operando, más una parte pequeña dependiente de la anchura.

G3 rechazó H6.1 («meseta plana») con 1,121× > 1,10×. Pero el rechazo es de la
*forma exacta* de la curva, no de la idea: sí hay una región grande y barata
por bit (1,0 / 0,6 / 0,8 instr/bit entre 256 y 16.384 bits), y eso es lo que
hace viable el empaquetado.

## 2. Serie B/C — el margen del empaquetado

Empaquetado: un solo `Nat.add` sobre un operando de `carriles × 65` bits con un
bit de guarda por carril, de modo que ninguna suma de carril pueda acarrear
hasta el vecino. Estrecho: el mismo trabajo como `carriles` unfolds, una suma
cada uno.

| carriles | empaquetado (1 op ancha) | estrecho (N unfolds) | estrecho/emp. |
|---:|---:|---:|---:|
| 1 | 347.741 | 584.260 | 1,68× |
| 4 | 361.211 | 959.473 | 2,66× |
| 16 | 361.711 | 2.414.200 | 6,67× |
| 64 | 367.207 | 8.226.602 | **22,40×** |

G2 spread 0,40% → PASS. G4 → el empaquetado gana en todos los anchos probados.
G6 → el margen **crece** con el número de carriles (1,68× → 22,40×), no es un
factor constante.

## 3. F6b — el control que F6 necesitaba, y sale MÁS fuerte

F6 tenía un defecto de diseño real: el brazo empaquetado pasaba por un helper
de 4 argumentos (`lanewise`) que costaba un overhead **constante** de ~113.566
instrucciones sobre un `Nat.add` de 2 argumentos a la misma anchura — un 39% de
handicap en el brazo del tratamiento. Un overhead aditivo constante no puede
fabricar un cociente (el lado estrecho crece linealmente, el empaquetado casi
no), así que el mecanismo sobreviva el chequeo — pero un handicap del 39% es
diseño experimental malo: subestima el efecto y hace los números absolutos
interpretable.

`scripts/f6b_packing_symmetric.py` repite la comparación con **harness simétrico**:
los dos brazos son una sola llamada `mkApp2` de 2 argumentos, así que la única
diferencia es cuánto trabajo hace cada llamada.

| carriles | empaquetado | estrecho | estrecho/emp. | F6 dijo |
|---:|---:|---:|---:|---:|
| 1 | 234.476 | 583.948 | 2,49× | 1,68× |
| 4 | 242.739 | 958.237 | 3,95× | 2,66× |
| 16 | 243.193 | 2.415.743 | 9,93× | 6,67× |
| 64 | 245.646 | 8.222.982 | **33,47×** | 22,40× |

**G3: el margen simétrico (33,47×) SUPERA al de F6 (22,40×) → H6.4 no rechazada.**
El confound de F6 **subestimaba** el efecto. G4 PASS: el empaquetado es más
barato en todos los anchos probados.

## 4. El mecanismo, que es lo que hace esto accionable

- **Brazo empaquetado: casi PLANO.** 234.476 → 245.646 instr para 64× más
  carriles. Es un +4,8% por 64× el trabajo.
- **Brazo estrecho: LINEAL.** 583.948 → 8.222.982 para la misma progresión.
- Por tanto el margen **crece sin cota** en el rango medido. No es un factor
  constante que se pueda agotar: es la razón por la que el empaquetado es la
  palanca y no una optimización más.

Esto reconcilia todo lo anterior sin contradicción: F5 midió el precio de un
*unfold* (~121k) y concluded que menos unfolds es mejor; F6 mide que **una
operación ancha también avanza 64 valores**, así que el objetivo no es solo
«menos unfolds» sino «menos operaciones totales, y una operación puede ser
ancha».

## 5. Qué NO resuelve esto, y el siguiente paso exacto

**El puzzle que queda abierto:** un slot de campeón = 238.082 instr, y un solo
`Nat.add` empaquetado de 64 carriles = 245.646 instr — **1,54× MÁS que el
presupuesto entero de un campeón**. Un `Nat.add` de 1 carril = 234.476, o sea
0,64× del presupuesto del campeón. La conclusión honesta: **el clúster de
cabecera no está haciendo ni siquiera un paso de 64 carriles**; su replay es
*inferior* a una única operación ancha. Cualquier candidato que:
- pague ~2 pasos de kernel por slot (≈240k) competirá en el mismo orden de
  magnitud que el líder, y
- la única forma conocida de bajar de ahí es **reducir el número de operaciones
  anchas**, no hacerlas más baratas.

Esto convierte el challenge en un problema de **cuántas operaciones anchas se
necesitan**, con un coste medido por operación de ~234k–246k en el rango
[1, 16.384] bits, y un margen de 33× frente a la aritmética estrecha equivalente.

**Lo que falta para hacerlo accionable:** el empaquetado tiene un techo. El
número de carriles por operación está limitado por la anchura del resultado
(los valores del DP para p(36) caben en ~15 bits por carril; p(36)=17977 <
2^15), así que caben ~1.000 carriles en un `Nat` de 16k bits. El siguiente
experimento concreto es medir el margen en el rango **[256, 4.096] carriles**,
donde la razón puede empezar a cambiar porque el operando se acerca al límite
de `Nat` de GMP. Ese es el cliff real que queda por encontrar, y decide si
`partition` tiene o no un techo.

## 6. Correcciones y bugs de hoy

- `check_step` en `f2_harness.py` capturaba solo la **primera línea** que
  casaba con el patrón de error, cortada a 400 chars. Los errores de Lean ocupan
  6 líneas: un `mkAppN` mal tipado lee «Application type mismatch: The argument»
  y la causa real («has type List Expr but is expected to have type Array Expr»)
  está dos líneas más abajo. Costó **tres iteraciones ciegas** en F6 antes de
  compilar el probe a mano. Arreglado: captura el bloque completo del
  diagnóstico hasta la línea en blanco. Beneficia a todo experimento futuro.
- `mkAppN` toma un **`Array Expr`**, no una lista: `#[...]`, no `[...]`.
- El límite de 4.300 dígitos de CPython cortaba la celda de 16384 bits
  (~4.933 decimales). Es un límite del **instrumento**, no una medición:
  `sys.set_int_max_str_digits(200_000)`.
- Expectations siempre simuladas, nunca escritas a mano (F5b ya lo enseñó y
  lo repetí en F6: el primer run abortó con un type mismatch por calcular el
  esperado a partir de la aritmética de carriles cuando el cuerpo Lean sumaba
  1 por unfold).

## 7. Artefactos

- `scripts/f6_packing_cliff.py` — barrido de anchura + margen (pre-registrado).
- `scripts/f6b_packing_symmetric.py` — control de harness simétrico.
- `scripts/f2_harness.py` — `check_step` corregido (diagnósticos completos).
- `results/cost_model/f6_packing_cliff.{json,txt}`,
  `f6b_packing_symmetric.{json,txt}`.
- Continuación: `results/LKC_2026-10-05_F5_step_tax.md` (el impuesto por paso).