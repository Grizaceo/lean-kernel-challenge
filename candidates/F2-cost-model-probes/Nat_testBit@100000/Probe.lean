import Spec

set_option maxRecDepth 4000000
set_option maxHeartbeats 0

def big_0 : Nat := (2^(100000-1))
def big_1 : Nat := (100000//2)

theorem check : Nat.testBit (2^(100000-1)) (100000//2) = false := rfl
