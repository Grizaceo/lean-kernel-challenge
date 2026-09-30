import Spec

set_option maxRecDepth 4000000
set_option maxHeartbeats 0

def big_0 : Nat := (2^(10000-1) + 1)
def big_1 : Nat := (2^(10000//2) + 1)

theorem check : Nat.gcd (2^(10000-1) + 1) (2^(10000//2) + 1) = 1 := rfl
