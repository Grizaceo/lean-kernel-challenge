import Spec

set_option maxRecDepth 4000000
set_option maxHeartbeats 0

def big_0 : Nat := (2^(64-1))
def big_1 : Nat := 13

theorem check : Nat.shiftLeft (2^(64-1)) 13 = 75557863725914323419136 := rfl
