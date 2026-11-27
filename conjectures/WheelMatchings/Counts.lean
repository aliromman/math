module

public import conjectures.WheelMatchings.Geometry

@[expose] public section

namespace WheelMatchings

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem convex_count : countCode (m := 6) (extend (convexSigns _)) 10 = 252 := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem wheel_count : countCode (m := 6) (extend (wheelSigns 6)) 10 = 176 := by decide +kernel

end WheelMatchings
