import Spec

set_option maxRecDepth 4000000
set_option maxHeartbeats 0

def big_0 : Nat := (2^(64//2))
def big_1 : Nat := (2^(64//2) + 1)

theorem check : Nat.mul (2^(64//2)) (2^(64//2) + 1) = 18446744078004518912 := rfl
