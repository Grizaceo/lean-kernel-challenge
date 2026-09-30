import Spec

set_option maxRecDepth 4000000
set_option maxHeartbeats 0

def big_0 : Nat := (2^(1000-1))
def big_1 : Nat := (1000//2)

theorem check : Nat.testBit (2^(1000-1)) (1000//2) = false := rfl
