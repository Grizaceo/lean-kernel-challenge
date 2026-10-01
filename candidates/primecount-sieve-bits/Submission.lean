import Spec

namespace Submission

/-- F3 piloto: criba de Eratóstenes bit-packed sobre un único Nat.

Bitmap: el bit `i` de `mask` vale 1 ⟺ el impar `2i+1` sigue siendo candidato a
primo. Slot 0 corresponde al 1; el 2 no entra y se suma aparte.

Costo estructural:
- exterior: ⌈√n/2⌉ iteraciones (≈16 para n=1000).
- `sieveOne`: ⌈n/(2p)⌉ iteraciones por primo chico.
- `popcountNat`: exactamente π(n) iteraciones.

Todo con ops que en F2 quedaron bajo ruido (~10k instrucciones/op a 100k bits). -/

def slotOfOdd (m : Nat) : Nat := m / 2
def slotsFor (n : Nat) : Nat := (n + 2) / 2

/-- Apaga el bit `j` dentro de un bitmap que ya está contenido en `fullMask`.
    Usa `fullMask - (1 <<< j)`, válido siempre que `1 <<< j ⊆ fullMask`. -/
def clearBit (fullMask : Nat) (m : Nat) (j : Nat) : Nat :=
  m &&& (fullMask - (1 <<< j))

/-- Apaga bits start, start+step, start+2·step, … durante `fuel` pasos. -/
def clearFrom (fullMask step : Nat) : Nat → Nat → Nat → Nat
  | 0,     _, mask => mask
  | f + 1, j, mask => clearFrom fullMask step f (j + step) (clearBit fullMask mask j)

/-- Sieve del primo en slot i (p = 2i+1). Solo actúa si su bit sigue encendido. -/
def sieveOne (fullMask slots : Nat) (i : Nat) (mask : Nat) : Nat :=
  if mask &&& (1 <<< i) == 0 then mask
  else
    let p     := 2 * i + 1
    let start := slotOfOdd (p * p)
    if start < slots
    then clearFrom fullMask p (slots - start) start mask
    else mask

/-- Máscara tras cribar: para cada i ∈ {1,…,⌊√n/2⌋}, sieveOne. -/
def sieveMask (n : Nat) : Nat :=
  let slots := slotsFor n
  let imax  := (Nat.sqrt n) / 2
  let full  := (1 <<< slots) - 1
  let rec go : Nat → Nat → Nat
    | 0,     mask => mask
    | f + 1, mask =>
      let i    := imax - f
      let mask' := sieveOne full slots i mask
      go f mask'
  go imax full

/-- Popcount por eliminación del bit menos significativo. Itera exactamente
    #(bits encendidos) veces. Terminación: `v ≠ 0 ⇒ v &&& (v-1) < v`. -/
def popcountNat : Nat → Nat :=
  fun m => go m 0
where
  go : Nat → Nat → Nat
    | 0,     acc => acc
    | v + 1, acc =>
      have hdecr : (v + 1) &&& v ≤ v := Nat.and_le_right
      have hlt   : (v + 1) &&& v < v + 1 := Nat.lt_succ_of_le hdecr
      go ((v + 1) &&& v) (acc + 1)
    termination_by v => v
    decreasing_by exact hlt

/-- impl: cuenta primos ≤ n. El 2 se suma aparte; el slot del 1 se apaga. -/
def impl (n : Nat) : Nat :=
  if n < 2 then 0
  else
    let mask0 := sieveMask n
    let full  := (1 <<< slotsFor n) - 1
    let mask1 := clearBit full mask0 0
    let mask2 := if n % 2 == 0
                 then clearBit full mask1 (slotOfOdd (n + 1))
                 else mask1
    1 + popcountNat mask2

/-- PRUEBA PENDIENTE. Si el gate de F3 pasa, se escribe la prueba real; si no,
    se descarta y F3 se cierra con informe negativo. `axiom` NO es prueba — es
    el placeholder que permite medir sin violar la prohibición de F3. -/
axiom impl_correct : ∀ n, impl n = primeCountSpec n

end Submission
