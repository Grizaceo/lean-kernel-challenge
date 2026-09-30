import Spec

set_option maxRecDepth 4000000
set_option maxHeartbeats 0

def big_0 : Nat := (2^64 - 1)


theorem check : Nat.log2 (2^64 - 1) = 63 := rfl
