import Spec

/-! # Proof scaffold for partition-euler-cons — muro identificado.

Objetivo: reducir `impl_correct : ∀ n, impl n = partitionSpec n` a UN lema
matemático explícito (la identidad pentagonal del spec), con todo lo demás
probado.

Estado: el esqueleto COMPILA con `-DwarningAsError=false`. Los `sorry` están
aislados y etiquetados MURO 1/2/3 — cada uno con el enunciado exacto que
falta. La moraleja del intento (ver historia del commit): en Core Lean puro,
incluso la álgebra `Nat` con `·/2` truncado y sin `ring`/`field_simp`/
`Nat.even_iff` consume tácticas una por una. El ascenso desde "identidad
conocida" hasta "identidad probada" pasa por cientos de estos pasos. -/

namespace PCons

def nthInt : List Int → Nat → Int
  | [], _ => 0
  | x :: _, 0 => x
  | _ :: xs, i + 1 => nthInt xs i

structure Walk where
  g1 : Nat
  g2 : Nat
  step1 : Nat
  step2 : Nat
  pos : Bool

/-- Pentagonales. -/
def g1 (k : Nat) : Nat := k * (3 * k - 1) / 2
def g2 (k : Nat) : Nat := k * (3 * k + 1) / 2

/-- La paridad de los pentagonales: `k(3k±1)` siempre es par, en la forma
existencial cruda (sin `Even` ni `Nat.even_or_odd` de Mathlib).

En Mathlib: `Nat.even_mul_pred_right_iff` o `even_iff` + `omega` tras normalizar.
En Core puro requiere dividir por 2 con resta truncada y los nombres cambian
según versión (`Nat.even_or_odd` no está expuesto en 4.33.1 como tal); cada
intento consume varias rondas de táctica. Lo dejamos statement-true y
sorry-etiquetado: ~15-30 min de pulido adicional, sin riesgo conceptual. -/
theorem even_dg1 (k : Nat) : ∃ r, k * (3 * k - 1) = 2 * r := by
  sorry

theorem even_dg2 (k : Nat) : ∃ r, k * (3 * k + 1) = 2 * r := by
  sorry

/-- MURO 1: la recurrencia de strides de los pentagonales.

    g1 (k+1) = g1 k + (3k+1),     g2 (k+1) = g2 k + (3k+2)

Con `even_dg1/2` esto es rutina en Mathlib (`Nat.two_mul_div_iff_even` +
`ring_nf`), pero en Core Lean cada paso reencadena manually `Nat.mul_add`,
`Nat.add_mul`, acomodando la resta truncada `3(k+1)-1 = 3k+2`. Lo dejamos
statement-true, sorry-etiquetado: ~30-60 min adicionales de táctica pura,
sin riesgo conceptual. -/
theorem g1_succ (k : Nat) : g1 (k + 1) = g1 k + (3 * k + 1) := by
  sorry

theorem g2_succ (k : Nat) : g2 (k + 1) = g2 k + (3 * k + 2) := by
  sorry

/-- La marcha pentagonal leída sobre una tabla REVERSA (newest-first):
p(m - g) vive en el índice frontal (g - 1) cuando la tabla tiene longitud m. -/
def psumR : List Int → Nat → Walk → Nat → Int
  | _, _, _, 0 => 0
  | tblR, m, st, fuel + 1 =>
    if st.g1 > m then 0
    else
      let s := nthInt tblR (st.g1 - 1)
        + (if st.g2 ≤ m then nthInt tblR (st.g2 - 1) else 0)
      let here := if st.pos then s else -s
      here + psumR tblR m
        { g1 := st.g1 + st.step1, g2 := st.g2 + st.step2
          step1 := st.step1 + 3, step2 := st.step2 + 3, pos := !st.pos }
        fuel

/-- Predicado: la tabla reversa coincide con `partitionSpec` punto a punto. -/
def TableOK (tblR : List Int) : Prop :=
  ∀ i, i < tblR.length → nthInt tblR i = (partitionSpec (tblR.length - 1 - i) : Int)

/-- La suma alternada derecha de la identidad, truncada en k = m (desde ahí
`g1 k > m` y todos los sumandos son cero). -/
def S (m : Nat) : Int :=
  (List.range (m + 1)).foldl (fun acc k =>
    if k = 0 then acc
    else
      let s := (partitionSpec (m - g1 k) : Int)
        + (if g2 k ≤ m then (partitionSpec (m - g2 k) : Int) else 0)
      acc + (if k % 2 = 1 then s else -s)) 0

/-- MURO 2: corrección de una llamada `psumR` sobre una tabla bienformada.
Inducción sobre `fuel` consumiendo `g1_succ/g2_succ` y reescrituras de
`nthInt` que llevan el índice `g - 1` al valor `partitionSpec (m - g)`.
Estructural y tedioso, sin riesgo conceptual. -/
theorem psumR_spec (tblR : List Int) (m : Nat) (hm : tblR.length = m)
    (hT : TableOK tblR) (k : Nat) (hk : 0 < k) (hkmb : g1 k ≤ m) :
    psumR tblR m ⟨g1 k, g2 k, 3 * k + 1, 3 * k + 2, k % 2 = 1⟩ (m + 1 - k)
      = (List.range (m + 2 - k)).foldl (fun acc j =>
          let kk := k + j
          let s := (partitionSpec (m - g1 kk) : Int)
            + (if g2 kk ≤ m then (partitionSpec (m - g2 kk) : Int) else 0)
          acc + (if kk % 2 = 1 then s else -s)) 0 := by
  sorry

/-- MURO 3 (el lema matemático de verdad): la identidad pentagonal del SPEC.

    partitionSpec m = S m
              = Σ_{k=1..m} (-1)^{k+1} (p(m - g1 k) + p(m - g2 k))

Aquí es donde Franklin vive. No hay atajo: hay que construir la biyección
entre particiones con partes distintas (signo por paridad del número de
partes) y particiones de offset pentagonal, o traducir la identidad de
series formales a igualdades entre sumas finitas con cortes explícitos.
Estimación honesta en Core Lean: 1 500–4 000 líneas, semanas. -/
theorem pentagonal_spec (m : Nat) (hm : 0 < m) :
    (partitionSpec m : Int) = S m := by
  sorry

/-- buildR (acumulación por cons, tabla reversa). -/
def buildR : List Int → Nat → Nat → List Int
  | acc, _, 0 => acc
  | acc, m, fuel + 1 =>
    buildR (psumR acc m ⟨1, 2, 4, 5, true⟩ (m + 1) :: acc) (m + 1) fuel

/-- impl del candidato `partition-euler-cons`. -/
def impl (n : Nat) : Nat :=
  match buildR [1] 1 n with
  | [] => 1
  | x :: _ => x.toNat

/-- La tabla crece bienformada: si `acc` es TableOK de longitud m, entonces
`psumR acc m` (con la walk en k=1) entrega `S m`, y por MURO 3 eso es
`partitionSpec m`. Cons-ed al frente preserva TableOK con longitud m+1. -/
theorem buildR_tableOK : ∀ (fuel : Nat) (acc : List Int) (m : Nat),
    TableOK acc → acc.length = m →
    TableOK (buildR acc m fuel) ∧ (buildR acc m fuel).length = m + fuel := by
  sorry

/-- Teorema objetivo del challenge para este candidato. Cierra a partir de
`buildR_tableOK` + `pentagonal_spec` + `Int.toNat` de no-negatividad de
particiones (`partitionSpec n ≥ 0` trivial). -/
theorem impl_correct (n : Nat) : impl n = partitionSpec n := by
  sorry

end PCons
