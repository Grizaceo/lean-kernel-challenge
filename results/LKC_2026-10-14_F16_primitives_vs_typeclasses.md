# LKC F16 — Primitivas del kernel vs. Typeclasses y `brecOn` (2026-10-14)

**Autores:** Devin + Eidos · **Script pre-registrado:** `scripts/f16_primitives_vs_typeclasses.py` · **Artefactos:** `results/cost_model/f16_primitives_vs_typeclasses.{json,txt}` · **Instrumento:** `.verify/timer-kernel-local` (`KERNEL_TIMING`, frontera `target-declaration-replay-v1`, mediana de 3, `LK_EXCLUDE_KERNEL=1`, `k_bias = 0.9927` de F13).

## Resumen ejecutivo

**H0 queda refutada y H1 queda confirmada en todas las dimensiones medidas.**

La paradoja que había quedado abierta entre F12 y F14 (*"el suelo sin recursor cuesta ~200k y una sola suma `fun n => n + 1` sube a ~308k, superando los 238,082 del campeón de `partition`; por tanto ningún `impl` que haga aritmética sobre `n` cabe en el presupuesto"*) era un **artefacto de la elaboración de typeclasses de Lean 4**, no una prima de GMP por abrir `n`:

1. **Impuesto de `HAdd.hAdd` + `OfNat.ofNat` en `n + 1`:**
   - `C3_hadd_1` (`fun n => n + 1`) elabora a `@HAdd.hAdd Nat Nat Nat (@instHAdd Nat instAddNat) n (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))` y cuesta **307,069** local (**309,327** oficial estimado).
   - `C4_natadd_ofnat1` (`fun n => Nat.add n 1`, eliminando `HAdd.hAdd` pero dejando `OfNat.ofNat` en el `1`) baja a **222,109** local (**223,742** oficial): **`HAdd.hAdd` por sí solo costaba 84,960 instrucciones**.
   - `C5_natadd_raw1` (`fun n => Nat.add n (nat_lit 1)`, eliminando también `OfNat.ofNat` en el literal) baja a **208,769** local (**210,304** oficial): **`OfNat.ofNat` en el argumento costaba otras 13,340 instrucciones**.
   - En total, reemplazar `n + 1` por `Nat.add n (nat_lit 1)` ahorra **98,300 instrucciones (-32.0%)**, dejando la operación **27,778 instrucciones por debajo del slot del campeón (238,082)**.

2. **Costo marginal real por suma primitiva (`3,869 instr/add` vs. `20,140 instr/add` en F12):**
   - En `C7_natadd_chain5_raw` (5 llamadas anidadas `Nat.add ... (nat_lit 1)`), el costo total es **224,246** local (**225,895** oficial), que **también entra holgadamente en el slot del campeón (238,082)**.
   - El costo marginal por `Nat.add` crudo es `(224,246 − 208,769) / 4 = 3,869 instr/add`, es decir **5.2× más barato** que el marginal de 20,140 medido en F12 con `+ 1`. Los ~16,270 extra por suma en F12 eran el unfold repetido de `HAdd.hAdd` + `OfNat.ofNat` en cada eslabón de la cadena.

3. **Impuesto de `if ... then ... else ...` (`ite` + `Decidable`) vs. `Bool.rec` + `Nat.beq`:**
   - `C8_ite_decidable` (`fun n => if n = 16 then 0 else n`) elabora a `@ite` + `instDecidableEqNat` y cuesta **364,209** local (**366,887** oficial).
   - `C9_boolrec_beq_raw` (`noncomputable def impl := fun n => Bool.rec n (nat_lit 0) (Nat.beq n (nat_lit 16))`) cuesta **198,637** local (**200,098** oficial) para `n ≠ 16` (y 216,943 en `n = 16`), ahorrando **165,572 instrucciones (-45.5%)**.

4. **Impuesto de recursión por pattern-matching (`brecOn`) vs. `@Nat.rec` directo:**
   - En F14, `C6_recursor` (`| 0 => 0 | n + 1 => impl n`, que compila vía `brecOn`) costó **1,882,457** local en `n = 16` (~105,000 instr/paso).
   - En F16, `C10_natrec_raw` (`noncomputable def impl := fun n => @Nat.rec (fun _ => Nat) (nat_lit 0) (fun _ acc => acc) n`) cuesta **544,773** local en `n = 16` (**3.46× más barato**, con una pendiente de `~19,522 instr/paso` entre `n = 15` y `n = 17` frente a los ~95k–121k de `brecOn` en F5/F10b).

5. **Sonda de Kronecker (`C11_kronecker_raw`):**
   - Evaluando $p(n)$ exacto en $n \in \{15, 16, 17\}$ mediante el denominador pentagonal de Euler y una única división `Nat.div` + `Nat.land` con primitivas crudas (`C11_kronecker_raw`), el costo por slot es **317,099** local (**319,431** oficial estimado, **~1.91M en 6 slots**), donde ~80k provienen de reducir las 12 operaciones aritméticas que construyen `eulerDenom` en cada slot.

## Tabla completa de resultados (mediana sobre `n ∈ {15, 16, 17}`, 3 repeticiones/celda)

| Celda | Definición de `impl` | Mediana local (instr) | Oficial est. (`local / 0.9927`) | Razón vs `C1` | ¿Cabe en 238,082? |
|---|---|---:|---:|---:|---|
| `C1_ofnat_0` | `fun _ => 0` *(control F11/F14)* | 198,674 | 200,135 | 1.000× | **FITS** |
| `C2_raw_0` | `fun _ => (nat_lit 0)` | 191,390 | 192,797 | 0.963× | **FITS** |
| `C3_hadd_1` | `fun n => n + 1` *(control F12/F14)* | 307,069 | 309,327 | 1.546× | exceeds |
| `C4_natadd_ofnat1` | `fun n => Nat.add n 1` | 222,109 | 223,742 | 1.118× | **FITS** |
| `C5_natadd_raw1` | `fun n => Nat.add n (nat_lit 1)` | 208,769 | 210,304 | 1.051× | **FITS** |
| `C6_natadd_raw1_wrap` | `let r := Nat.add n (nat_lit 1); @OfNat.ofNat Nat r ...` | 232,078 | 233,785 | 1.168× | **FITS** |
| `C7_natadd_chain5_raw` | 5× `Nat.add ... (nat_lit 1)` encadenados | 224,246 | 225,895 | 1.129× | **FITS** |
| `C8_ite_decidable` | `fun n => if n = 16 then 0 else n` *(control F14)* | 364,209 | 366,887 | 1.833× | exceeds |
| `C9_boolrec_beq_raw` | `Bool.rec n (nat_lit 0) (Nat.beq n (nat_lit 16))` | 198,637 | 200,098 | 1.000× | **FITS** |
| `C10_natrec_raw` | `@Nat.rec (fun _ => Nat) (nat_lit 0) (fun _ acc => acc) n` | 544,773 | 548,779 | 2.742× | exceeds |
| `C11_kronecker_raw` | `Nat.land (Nat.div (Nat.shiftLeft ...) eulerDenom) (nat_lit 32767)` | 317,099 | 319,431 | 1.596× | exceeds |
| `C12_kronecker_wrap` | `C11` envuelto en `@OfNat.ofNat` | 340,463 | 342,967 | 1.714× | exceeds |

## Guardianes verificados

- **G1 (sin fallos silenciosos):** 36/36 celdas (`12 × 3`) compilaron, exportaron y completaron replay (`phase=complete`).
- **G2 (dispersión intra-celda ≤ 5%):** peor spread **0.70%** (`C10_natrec_raw` a `n=15`).
- **G3 (controles contra F11/F12/F14 ≤ 5%):**
  - `C1_ofnat_0`: 0.12% / 0.17% / 0.34% vs 199,012 → **PASS**.
  - `C3_hadd_1`: 0.97% / 0.38% / 0.13% vs 305,916 → **PASS**.
  - `C8_ite_decidable`: 0.45% / 3.32% / 0.30% vs 362,584 → **PASS**.
- **G5 (inspección del término elaborado con `set_option pp.all true` + `#print Submission.impl`):** verificado automáticamente antes de exportar cada celda y guardado en `results/cost_model/f16_primitives_vs_typeclasses.json`.
- **G7 (restauración de `problems/partition`):** `Submission.lean` y `Perf.lean` restaurados byte a byte al finalizar.

## Consecuencias de diseño para Paso B

1. **Regla de oro para todo `impl` competitivo en el kernel:**
   - Prohibido usar `+`, `-`, `*`, `/`, `%`, `<<<`, `>>>`, `&&&`, `|||`, `^^^`, `==`, `≤`, `<` o literales numéricos con `OfNat` dentro del camino crítico de `impl`.
   - Usar siempre `Nat.add`, `Nat.sub`, `Nat.mul`, `Nat.div`, `Nat.mod`, `Nat.shiftLeft`, `Nat.shiftRight`, `Nat.land`, `Nat.lor`, `Nat.xor`, `Nat.beq`, `Nat.ble` y literales crudos `(nat_lit k)`.
   - Prohibido usar `if ... then ... else ...` (`ite` + `Decidable`) o recursión del compilador de ecuaciones (`brecOn`). Usar `noncomputable def` con `@Bool.rec` y `@Nat.rec` / `@List.rec` directos.
2. **Impacto inmediato en los candidatos existentes:**
   - En `ca-rule110-v3`, `initBits` (desenrollado 256 veces) y `bstep` contienen cientos de instancias de `*`, `+`, `%`, `<<<`, `>>>`, `&&&`, `|||`, `^^^` y literales `OfNat`. Cada operador con typeclass paga entre 13k y 85k instrucciones. Reemplazarlos por primitivas crudas y `(nat_lit ...)` eliminará la mayor parte de los ~495M actuales sin cambiar la estructura lógica de la prueba.
   - En `fib`, reemplazar el bucle `fd` (que usa `match`, `Prod`, `/`, `%`, `if/else` con `Decidable`, `*`, `+`, `-`) por `@Nat.rec` + `@Bool.rec` + primitivas `Nat.mul`/`Nat.add`/`Nat.sub` y `(nat_lit ...)` reducirá drásticamente el costo por paso en los ~17 niveles logarítmicos.
   - En `sha256`, cada una de las 64 rondas por paso ejecuta decenas de operaciones de 32 bits (`add32`, `rotr32`, `ch`, `maj`, `bigSigma`, `smallSigma`). Pasar esas funciones a primitivas crudas + `(nat_lit ...)` recortará un factor grande sobre el baseline de 85B.
