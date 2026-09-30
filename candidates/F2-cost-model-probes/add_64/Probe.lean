import Spec

set_option maxRecDepth 4000000
set_option maxHeartbeats 0

def big_0 : Nat := (2^63)
def big_1 : Nat := (2^63 - 1)

theorem check : Nat.add big_0 big_1 = 18446744073709551615 := rfl
