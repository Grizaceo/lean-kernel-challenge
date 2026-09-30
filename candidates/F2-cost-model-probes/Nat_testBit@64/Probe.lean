import Spec

set_option maxRecDepth 4000000
set_option maxHeartbeats 0

def big_0 : Nat := (2^(64-1))
def big_1 : Nat := (64//2)

theorem check : Nat.testBit (2^(64-1)) (64//2) = false := rfl
