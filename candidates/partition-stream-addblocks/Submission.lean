import Spec

namespace Submission

def nthNat : List Nat → Nat → Nat
  | [], _ => 0
  | x :: _, 0 => x
  | _ :: xs, i + 1 => nthNat xs i

def chunks (d : Nat) : Nat → List Nat → List (List Nat)
  | 0, _ => []
  | _ + 1, [] => []
  | fuel + 1, l => l.take d :: chunks d fuel (l.drop d)

def addBlocks : List Nat → List Nat → List Nat
  | a :: as, b :: bs => (a + b) :: addBlocks as bs
  | _, _ => []

def zipBlocksAdd : List Nat → List (List Nat) → List Nat
  | _, [] => []
  | prev, blk :: rest =>
    let bn := addBlocks blk prev
    bn ++ zipBlocksAdd bn rest

def updRowAdd (d : Nat) (t : List Nat) : List Nat :=
  zipBlocksAdd (List.replicate d 0) (chunks d t.length t)

def initTable (n : Nat) : List Nat := 1 :: List.replicate n 0

def itAdd : Nat → List Nat → List Nat
  | 0, t => t
  | k + 1, t => itAdd k (updRowAdd (k + 1) t)

def impl (n : Nat) : Nat := nthNat (itAdd n (initTable n)) n

end Submission
