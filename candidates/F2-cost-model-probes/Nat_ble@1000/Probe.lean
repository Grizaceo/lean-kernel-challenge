import Spec

set_option maxRecDepth 4000000
set_option maxHeartbeats 0

def big_0 : Nat := (2^(1000-1))
def big_1 : Nat := (2^(1000-1) + 1)

theorem check : Nat.ble (2^(1000-1)) (2^(1000-1) + 1) = true := rfl
