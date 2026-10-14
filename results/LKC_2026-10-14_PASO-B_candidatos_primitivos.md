# LKC Paso B — Candidatos con Primitivas Crudas del Kernel (`fib-v2`, `ca-rule110-v4`, `sha256-v2`) (2026-10-14)

**Autores:** Devin + Eidos · **Instrumento:** `.verify/timer-kernel-local` (`KERNEL_TIMING`, frontera `target-declaration-replay-v1`, mediana de 3, `LK_EXCLUDE_KERNEL=1`, `k_bias = 0.9927`).

## 1. Resumen Ejecutivo

Aplicando las reglas de diseño demostradas en **F16** (<ref_file file="/home/gris96/.hermes/workspace/repos/SAIR/lean-kernel-challenge/results/LKC_2026-10-14_F16_primitives_vs_typeclasses.md" />), construimos, demostramos formalmente (`impl_correct` sin `sorry` ni `native_decide`) y medimos en el plan completo de 6 slots tres nuevos candidatos listos para envío:

| Problema | Candidato anterior (6 slots est.) | Nuevo candidato (`Paso B`) | Total 6 slots local | Total 6 slots oficial est. (`/ 0.9927`) | Mejora | Gate (`verify_candidate.sh`) | Rank proyectado |
|---|---:|---|---:|---:|---:|---|---|
| **`fib`** | `starter` (`Nat.fastFib`): 93,440,663<br>`example_fd`: 59,537,194 | `candidates/fib-v2/Submission.lean` | **13,207,902** | **13,305,029** | **7.07×** vs starter<br>**4.51×** vs example | **PASS** (`[propext, Classical.choice, Quot.sound]`) | **~#10 / 30** (antes #29/30) |
| **`ca-rule110`** | `ca-rule110-v3`: 1,051,345,595 | `candidates/ca-rule110-v4/Submission.lean` | **143,270,536** | **144,324,102** | **7.34×** vs v3<br>**~1,600×** vs baseline | **PASS** (`[propext, Classical.choice, Quot.sound]`) | **~#16 / 26** (y sonda SWAR en **7.91M**, ~#10) |
| **`sha256`** | `sha256-official`: ~182,800,000,000 | `candidates/sha256-v2/Submission.lean` | **36,810,366,084** | **37,081,057,806** | **4.97×** vs baseline | **PASS** (`[propext, Quot.sound]`) | **~#11 / 22** (antes #22/22) |

---

## 2. Detalle Técnico por Candidato

### 2.1 `candidates/fib-v2/Submission.lean` (7.07× sobre `Nat.fastFib`, 4.51× sobre `example_fd`)

- **Arquitectura de `impl`:**
  1. Reemplaza `Prod` (`Nat × Nat`), `match`, `brecOn` e `ite`+`Decidable` por **Continuation-Passing Style (`(Nat → Nat → Nat) → Nat`)** con `@Nat.rec` y `@Bool.rec` directos y primitivas `Nat.div`, `Nat.mod`, `Nat.mul`, `Nat.add`, `Nat.sub`, `Nat.beq` con literales `(nat_lit k)`.
  2. En la rama impar ($n = 2m+1$), usa la identidad $F(2m+2) = F(m+1)(2F(m) + F(m+1))$, eliminando la resta truncada y el cálculo redundante de $F(2m)$ en pasos impares.
  3. Desenrolla 18 niveles del combinador `step1` mediante el macro `unroll1%` alrededor de `fdCps n`. Como `fdCps (fuel + 1)` es definicionalmente igual (`rfl`) a `step1 (fdCps fuel)`, `impl n` es definicionalmente igual a `fdCps (n + 18) n (fun a _ => a)`:
     - En el replay puntuado ($n \le 150,000 < 2^{18}$), el kernel ejecuta **cero pasos de `@Nat.rec`** y **cero δ-unfolds de `step1`**.
     - En la prueba de `impl_correct`, cierra en **una sola línea**: `exact fdCps_spec (n + 18) n (by omega) (fun a _ => a)`.
- **Desglose por slot (plan local 6 slots):**
  - `n = 5,369`: `1,414,842` (vs `13,014,156` starter / `7,974,040` example)
  - `n = 9,257`: `1,527,868` (vs `13,863,936` starter / `8,485,286` example)
  - `n = 22,257`: `1,741,809` (vs `14,793,878` starter / `9,238,965` example)
  - `n = 39,540`: `1,956,652` (vs `15,759,313` starter / `9,946,538` example)
  - `n = 90,534`: `2,770,997` (vs `17,230,512` starter / `11,232,992` example)
  - `n = 139,516`: `3,795,734` (vs `18,778,868` starter / `12,659,373` example)
  - **Suma 6 slots:** `13,207,902` local (`13,305,029` oficial est.).

### 2.2 `candidates/ca-rule110-v4/Submission.lean` (7.34× sobre `ca-rule110-v3`)

- **Arquitectura de `impl`:**
  1. Reemplaza las 254 llamadas a `if (caMix32 ...).testBit 31 then 1 else 0` (donde cada `Nat.testBit` desplegaba `@bne`, `@instBEqOfDecidableEq`, `instDecidableEqNat`, `HAnd`, `HShiftRight` y `@ite`) por la extracción directa `Nat.land (nat_lit 1) (Nat.shiftRight x (nat_lit 31))` demostrada igual vía `bit31_eq` en 8 líneas.
  2. Inlina `caMix32Raw` con `let` bindings y primitivas crudas (`Nat.land`, `Nat.mul`, `Nat.xor`, `Nat.shiftRight`) y precalcula los offsets `(i + 1) * 0x9e3779b9` como `(nat_lit ...)`.
  3. **Técnica clave de prueba para evitar el timeout $2^{256}$ en `isDefEq`:** En Lean 4, comparar por `isDefEq` dos árboles de profundidad 256 con `Nat.mul` en la espina (`2 * acc + b`) despliega `Nat.mul` recursivamente ($2^{256}$ pasos) si las hojas difieren aunque sea en `OfNat.ofNat` vs `nat_lit`. En `v4`, `initUnrolledG (stepF : Nat → Nat → Nat) (cellF : Nat → Nat) (z : Nat)` abstrae el acumulador y la celda como variables de función libres: `initUnrolledG_eq` cierra por `rfl` en **0.4 segundos**, y `foldr_cell_eq` reescribe la lista por inducción estándar en 5 líneas.
- **Desglose por slot (plan local 6 slots):**
  - `steps = 2`: `23,498,685` / `23,576,529` (vs `173,382,549` / `173,560,906` en v3)
  - `steps = 4`: `23,834,703` / `23,827,202` (vs `175,038,349` / `175,083,922` en v3)
  - `steps = 8`: `24,264,185` / `24,269,232` (vs `177,216,971` / `177,062,898` en v3)
  - **Suma 6 slots:** `143,270,536` local (`144,324,102` oficial est.).
- **Hallazgo adicional para `ca-rule110-v5` (SWAR de 256 carriles de 64 bits):**
  - Empaquetando las 256 evaluaciones de `caMix32` en un único `Nat` de 16,384 bits (carriles de 64 bits: `x = seed * REP_64 + OFFSETS_FULL_64`, ya que $s + (i+1)K < 2^{41}$ y los productos por `0x7feb352d` y `0x846ca68b` son $< 2^{64}$ sin acarreo entre carriles) seguido de 3 pasos butterfly (`>>> 63`, `>>> 126`, `>>> 252`) y una multiplicación recolectora `GATHER_512`, el total medido de 6 slots cae de `143.27M` a **`7,907,941` instrucciones** (`927k` en C1, `1.22M` en C2, `1.80M` en C3), explicando exactamente cómo opera el clúster líder de 3.43M–5.01M.

### 2.3 `candidates/sha256-v2/Submission.lean` (4.97× sobre `sha256` baseline)

- **Arquitectura de `impl`:**
  1. Desenrolla por completo las 48 expansiones del message schedule y las 64 rondas de compresión dentro de `fastStepR`, eliminando `Window`, `List.append`, `K.zip`, `generate`, `rounds` y las 64 construcciones/proyecciones intermedias de `Digest` por bloque.
  2. Inlina todas las operaciones de 32 bits (`add32`, `rotr32` con desplazamientos precalculados `32 - r`, `smallSigma0/1`, `bigSigma0/1`, `ch`, `maj`) directamente con `Nat.add`, `Nat.land`, `Nat.lor`, `Nat.xor`, `Nat.shiftLeft`, `Nat.shiftRight` y `(nat_lit ...)`.
  3. **Prueba en < 1 segundo sin explosión simbólica:** `stepUnrolledG_eq` abstrae `t1F`, `t2F`, `addF` y `nxt` como parámetros funcionales libres, demostrando por `rfl` en 0.4s que el bloque desenrollado de 64 rondas sin estructuras intermedias es idéntico a `roundsG (mkRoundG ...) (K.zip (w0.toList ++ genG nxt 48 w0)) s0`.
- **Desglose por slot (plan local 6 slots):**
  - `H1 (steps = 4)`: `135,294,264` / `135,091,296`
  - `H2 (steps = 32)`: `1,074,945,779` / `1,075,358,608`
  - `H3 (steps = 512)`: `17,202,392,025` / `17,187,284,112`
  - **Suma 6 slots:** `36,810,366,084` local (`37,081,057,806` oficial est., frente a ~182.8B del baseline).

---

## 3. Tabla Actualizada de Payloads Listos para Envío Formal (Pendiente OK de Cristóbal)

| Problema | Archivo verificado (`GATE: PASS`) | Bytes | SHA-256 | Total 6 slots est. | Rank proyectado |
|---|---|---:|---|---:|---|
| **`fib`** | `candidates/fib-v2/Submission.lean` | 5,020 B | `405e095e2bf04732…` | **13.31M** | **~#10 / 30** |
| **`ca-rule110`** | `candidates/ca-rule110-v4/Submission.lean` | 133,496 B | `28f640e5b2b87af9…` | **144.32M** | **~#16 / 26** |
| **`sha256`** | `candidates/sha256-v2/Submission.lean` | 143,727 B | `b628f69e2e5f3408…` | **37,081M** | **~#11 / 22** |
| **`permanent`** | `candidates/permanent-tbl/Submission.lean` | 26,692 B | `2d007c036c58e315…` | **24,127M** | **~#18 / 24** |
