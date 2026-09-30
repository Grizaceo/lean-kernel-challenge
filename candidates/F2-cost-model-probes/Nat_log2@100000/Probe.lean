import Spec

set_option maxRecDepth 4000000
set_option maxHeartbeats 0

def big_0 : Nat := (2^100000 - 1)


theorem check : Nat.log2 (2^100000 - 1) = 99999 := rfl
