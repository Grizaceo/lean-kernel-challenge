import Spec

set_option maxRecDepth 4000000
set_option maxHeartbeats 0

def big_0 : Nat := (2^10)
def big_1 : Nat := 13

theorem check : Nat.pow (2^10) 13 = 1361129467683753853853498429727072845824 := rfl
