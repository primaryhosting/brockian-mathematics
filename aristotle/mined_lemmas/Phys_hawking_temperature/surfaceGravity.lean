/-
# Hawking Temperature
Category: Frontier Phys
Target: Phys.hawking_temperature
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Hawking Temperature
Category: Frontier Phys
Target: Phys.hawking_temperature
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace Phys

/-- The Schwarzschild radius `r_s = 2GM/c²` of a mass `M`. -/

noncomputable def surfaceGravity (G M c : ℝ) : ℝ :=
  c ^ 2 / (2 * schwarzschildRadius G M c)

/-- The Hawking temperature `T = ℏ κ / (2π c k)` associated with a surface gravity `κ`. -/
