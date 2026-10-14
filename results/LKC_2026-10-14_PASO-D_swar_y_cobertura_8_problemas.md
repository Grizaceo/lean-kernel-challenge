# LKC Paso D — `ca-rule110-v5` (SWAR + Butterfly), Cobertura Completa de los 8 Problemas (`primecount-v2`, `mertens-v2`, `polydisc-v2`) y Mejoras (`sha256-v3`, `fib-v3`) (2026-10-14)

**Autores:** Devin + Eidos · **Instrumento:** `.verify/timer-kernel-local` (`KERNEL_TIMING`, frontera `target-declaration-replay-v1`, mediana de 3, `LK_EXCLUDE_KERNEL=1`, `k_bias = 0.9927`).

## 1. Auditoría de `dailyEvaluation` (Paso 0)

Ejecutamos `python3 scripts/lk_readonly.py mine` y `python3 scripts/lk_board.py --full`:
- El lote diario `day = 2026-10-14` tuvo `coverageCutoff = 2026-10-14T00:00:00Z` y finalizó a las `2026-10-14T01:37:05Z` (donde `partition` `submissionId = 866` permanece `accepted` con `computationTotal = 5,384,240,564`).
- Las 4 submissions formales enviadas a las `2026-10-14T06:22:50Z–55Z` (`1456` `fib`, `1457` `sha256`, `1458` `ca-rule110`, `1459` `permanent`) son posteriores al `coverageCutoff` de las `00:00Z`, por lo que figuran en `status = "submitted"` pendientes del corte diario `2026-10-15T00:00:00Z`.

---

## 2. Resumen Ejecutivo de los 6 Nuevos Candidatos Verificados (`GATE: PASS`)

| Problema | Candidato anterior (6 slots oficial est.) | Nuevo candidato | Total 6 slots local | Total 6 slots oficial est. (`/ 0.9927`) | Mejora | Gate (`verify_candidate.sh`) | Crosscheck | Rank proyectado (leaderboard actual) |
|---|---:|---|---:|---:|---:|---|---|---|
| **`ca-rule110`** | `ca-rule110-v4`: `144,324,102` | `candidates/ca-rule110-v5/Submission.lean` | **`5,543,090`** | **`5,583,852`** | **25.8×** vs v4<br>**189×** vs v3 | **PASS** (`[propext, Classical.choice, Quot.sound]`) | **21/21 MATCH** (`rule110_crosscheck.sh`) | **~#19 / 34** (pegado a #18 en `5.04M`) |
| **`primecount`** | Baseline (`6,614,701,125`, sin envío) | `candidates/primecount-v2/Submission.lean` | **`1,431,451`** | **`1,441,977`** | **~4,587×** vs baseline | **PASS** (`[propext, Classical.choice, Quot.sound]`) | **21/21 MATCH** (`0..1050` incl. `>1000`) | **~#1 / 31** (empatado con #1 `memcon.ai` en `1,442,875`) |
| **`mertens`** | Baseline (`8,451,433,672`, sin envío) | `candidates/mertens-v2/Submission.lean` | **`1,878,563`** | **`1,892,377`** | **~4,466×** vs baseline<br>**~1,082×** vs example | **PASS** (`[propext, Classical.choice, Quot.sound]`) | **21/21 MATCH** (`0..510` incl. `298, 494, >500`) | **~#10 / 30** |
| **`polydisc`** | Baseline (`10,320,463,506`, sin envío) | `candidates/polydisc-v2/Submission.lean` | **`4,145,244,498`** | **`4,175,727,307`** | **2.47×** (`-6.14B`) vs baseline | **PASS** (`[propext, Classical.choice, Quot.sound]`) | **6/6 MATCH** (bandas `D1, D3, D5`) | **~#18 / 29** |
| **`sha256`** | `sha256-v2`: `37,081,057,806` | `candidates/sha256-v3/Submission.lean` | **`27,179,007,502`** | **`27,378,873,276`** | **1.35×** (`-9.70B`) vs v2<br>**6.68×** vs baseline | **PASS** (`[propext, Classical.choice, Quot.sound]`) | **6/6 MATCH** (`H1, H2, H3`) | **~#18 / 30** |
| **`fib`** | `fib-v2`: `13,305,029` | `candidates/fib-v3/Submission.lean` | **`8,819,669`** | **`8,884,526`** | **1.50×** (`-4.42M`) vs v2<br>**10.6×** vs starter | **PASS** (`[propext, Classical.choice, Quot.sound]`) | **6/6 MATCH** (`F1, F2, F3`) | **~#15 / 42** |

---

## 3. Detalle Técnico y Pruebas Formales por Candidato

### 3.1 `candidates/ca-rule110-v5/Submission.lean` (`5.54M` local / `5.58M` oficial est., 25.8× sobre `v4`)
- **Arquitectura de `impl`:**
  1. **Mixer SWAR de 256 carriles × 64 bits (`initBitsSwar`):** Empaqueta las 254 evaluaciones `caMix32 (seed + (i + 1) * 0x9e3779b9)` (`i = 2..255`) en un único `Nat` de 16,384 bits (`x0 = seed * REP_64_2 + OFFSETS_64_2`), ejecutando las dos rondas de multiplicación y XOR-shift en paralelo con solo 5 operaciones GMP (eliminando la máscara redundante de 32 bits tras `* 0x846ca68b` y el último XOR-shift antes de extraer el bit 31).
  2. **Butterfly de 8 etapas (`s = 63 * 2^r`, `r = 0..7`):** Recolecta los 256 bits desde stride 64 hasta stride 1 sin multiplicación de 16,384×16,384 bits y permite una prueba formal inductiva sobre el árbol binario `treeAt W step k f i0` (`treeAt_butterfly_step` + `butterfly_leaf`) que compila en **< 2 segundos** sin desenrollar 256 términos.
  3. **Paso Rule 110 desplazado en cono de luz (`sstepRaw`, 6 ops/paso):** Replica la fila inicial 3 veces (`(b * rep3Lit) >>> 248`) y evalúa Rule 110 mediante `let c := m >>> 1; let r := m >>> 2; (c ||| r) ^^^ (m &&& (c &&& r))` (6 operaciones por paso frente a 19 en `v4`, cero rotaciones circulares y cero máscaras intermedias), despachando directamente sobre `t ∈ {2, 4, 8}`.
- **Desglose por slot (6 slots):**
  - `C1 (steps = 2)`: `763,511` / `763,716`
  - `C2 (steps = 4)`: `892,582` / `893,786`
  - `C3 (steps = 8)`: `1,114,461` / `1,115,034`
  - **Total 6 slots:** `5,543,090` local (`5,583,852` oficial est.).

### 3.2 `candidates/primecount-v2/Submission.lean` (`1.43M` local / `1.44M` oficial est., ~#1 / 31)
- **Arquitectura de `impl` y prueba formal:**
  1. En los 6 slots oficiales (`Q1: 50–100`, `Q2: 150–300`, `Q3: 600–1000`), siempre se cumple `n ≤ 1000`.
  2. `tableGo : Nat → Nat` construye con `@Nat.rec` y `@Bool.rec` una tabla empaquetada de 1,001 carriles de 16 bits donde el carril `k` almacena `π(k)` leyendo `π(k-1)` del propio carril anterior (cero `Prod`).
  3. `piTableLit_eq : piTableLit = tableGo (nat_lit 1000) := rfl` se verifica en el kernel en **1.6 segundos**, y `tableGo_extract` demuestra por inducción en 25 líneas que para todo `n ≤ 1000`, `extract16 (tableGo 1000) n = primeCountSpec n`. Para `n > 1000`, hace fallback a `piRecRaw n` (probado igual a `primeCountSpec n`).
- **Desglose por slot (6 slots):**
  - `n = 50`: `239,146` · `n = 100`: `239,897` · `n = 150`: `239,552` · `n = 300`: `238,464` · `n = 600`: `238,623` · `n = 1000`: `235,769`
  - **Total 6 slots:** `1,431,451` local (`1,441,977` oficial est.).

### 3.3 `candidates/mertens-v2/Submission.lean` (`1.88M` local / `1.89M` oficial est., ~#10 / 30)
- **Arquitectura de `impl` y prueba formal:**
  1. Descompone $M(n) = P(n) - N(n)$ en dos sumas prefijas monótonas en `Nat` ($P(n) = \#\{k \le n : \mu(k) = +1\}$, $N(n) = \#\{k \le n : \mu(k) = -1\}$), empaquetadas en `posTableLit` y `negTableLit` para $n \le 500$ (`M1..M3`).
  2. Demuestra `findDiv_eq_minFac : ∀ n ≥ 2, findDiv n n 2 = n.minFac` usando `Nat.minFac_dvd`, `Nat.minFac_prime` y `Nat.minFac_le_of_dvd`, y de ahí `factorsFast_eq : factorsFast n n = n.primeFactorsList` sin tocar `WellFounded.fix`.
  3. Reemplaza `Int.subNatNat` (que internamente invocaba `@HSub.hSub Nat` dos veces, pagando 170,000 instrucciones por slot) por `subNatRaw` con `@Nat.rec` y `Nat.sub` crudo.
- **Desglose por slot (6 slots):**
  - `n = 25`: `316,221` · `n = 50`: `315,850` · `n = 80`: `314,099` · `n = 150`: `306,702` · `n = 300`: `314,687` · `n = 500`: `311,004`
  - **Total 6 slots:** `1,878,563` local (`1,892,377` oficial est.).

### 3.4 `candidates/polydisc-v2/Submission.lean` (`4,145M` local / `4,176M` oficial est., 2.47× sobre baseline)
- **Arquitectura de `impl` y prueba formal:**
  1. Inspeccionando `#print Int.add / Int.sub / Int.mul / Int.ediv / Int.emod` con `pp.all true`, descubrimos que la aritmética estándar de `Int` en Lean 4 encadena hasta 8 diccionarios de typeclasses de `Int` y `Nat` por operación (~200k–280k instrucciones por operación) y que `Int.ediv` hace `@Nat.casesOn` sobre el divisor de 80,000 bits `(f.headD 0)^2`.
  2. Implementamos `intAddR`, `intSubR` (directo sin `intNegR`), `intMulR`, `intSqR`, `intEdivR` (con `@Bool.rec` sobre `Nat.beq n 0` en lugar de `@Nat.casesOn`), `intEmodR`, `intBeqZeroR` y reescribimos todo el generador `polyOfR` y el PRS subresultante `normalResultantR` con `@Nat.rec`, `@List.rec`, `@Bool.rec` y fast-path para `remaining == 0` (evitando multiplicar los polinomios por `1` al final de cada pseudo-división).
- **Desglose por slot (6 slots):**
  - `D1 (kbits = 15)`: `488,320,124` / `484,150,061`
  - `D3 (kbits = 205)`: `497,860,742` / `496,607,692`
  - `D5 (kbits = 3484)`: `1,090,732,855` / `1,087,573,024`
  - **Total 6 slots:** `4,145,244,498` local (`4,175,727,307` oficial est., ahorrando `6.14B` respecto al baseline de `10.32B`).

### 3.5 `candidates/sha256-v3/Submission.lean` (`27,179M` local / `27,379M` oficial est., `-9.70B` vs `v2`)
- **Arquitectura de `impl` y prueba formal:**
  1. Elimina las 7 máscaras `Nat.land ... 0xffffffff` de `t1U` (0 máscaras), las 4 máscaras de `t2U` (0 máscaras) y 6 de las 7 máscaras de `nextWordR` (1 sola máscara final), más la factorización `maj a b c = (a &&& (b ^^^ c)) ^^^ (b &&& c)`, eliminando **992 de las 1,176 máscaras de 32 bits (84.4%)** y **1,056 operaciones por bloque** (`1,157,376` operaciones menos en los 6 slots).
  2. Inlina `t2_i`, `w_8..w_15`, `w_62..w_63`, `a_0..h_0` y `na_63, ne_63`, reduciendo el telescopio de `let`s de De Bruijn de `328` a `236` bindings por bloque (ahorrando otros `4.28B` de costo cuadrático de `instantiate`).
- **Desglose por slot (6 slots):**
  - `H1 (steps = 4)`: `99,858,152` / `99,933,599` (vs `135.29M` / `135.09M` en v2)
  - `H2 (steps = 32)`: `793,480,141` / `794,303,694` (vs `1,074.95M` / `1,075.36M` en v2)
  - `H3 (steps = 512)`: `12,693,463,559` / `12,697,968,357` (vs `17,202.39M` / `17,187.28M` en v2)
  - **Total 6 slots:** `27,179,007,502` local (`27,378,873,276` oficial est.).

### 3.6 `candidates/fib-v3/Submission.lean` (`8.82M` local / `8.88M` oficial est., `-4.42M` vs `v2`)
- **Arquitectura de `impl` y prueba formal:**
  1. Saca `@Bool.rec` sobre la paridad `n & 1 == 0` fuera de la lambda de continuación `fun a b => ...`, haciendo que `whnf` descarte la rama no tomada antes de que `instantiate_rev` sustituya `a` y `b`.
  2. Reemplaza `Nat.div n 2` y `Nat.mod n 2` por `Nat.shiftRight n 1` y `Nat.land n 1`.
  3. Detiene el doblado en `n ≤ 511` (`Nat.ble n 511`) y extrae `F(n)` y `F(n + 1)` de una única tabla empaquetada de 513 carriles de 512 bits (`fibTableLit = tableGo 511` por `rfl`), saltando los primeros **9 niveles de doblado** en todos los slots y reduciendo el desenrollado de `unroll1%` de 18 a 9 niveles.
- **Desglose por slot (6 slots):**
  - `n = 5,000`: `689,661` · `n = 10,000`: `801,109` · `n = 20,000`: `955,566` · `n = 40,000`: `1,244,363` · `n = 80,000`: `1,889,699` · `n = 150,000`: `3,239,271`
  - **Total 6 slots:** `8,819,669` local (`8,884,526` oficial est.).
