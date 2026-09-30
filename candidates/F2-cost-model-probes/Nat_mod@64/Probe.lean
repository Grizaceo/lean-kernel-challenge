import Spec

set_option maxRecDepth 4000000
set_option maxHeartbeats 0

def big_0 : Nat := (2^(64-1) - 1)
def big_1 : Nat := (2^(64//2) + 1)

theorem check : Nat.mod (2^(64-1) - 1) (2^(64//2) + 1) = 2147483648 := rfl
