/-
# Stride Ray Walk Classification
Category: Cone Line
Target: Brockian.ConeLine.stride_ray_walk_classification
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Brockian.ConeLine

/-- The ray reached after `k+1` strides only depends on the previous ray and `s % 5`. -/

private theorem walk_of (s : ℕ) (r : ℕ) (h : s % 5 = r) :
    (List.range 5).map (fun k => ((k + 1) * s) % 5)
      = (List.range 5).map (fun k => ((k + 1) * r) % 5) := by
  simp only [List.map_inj_left]
  intro k _
  rw [stride_mul_mod, h]

/-- **Stride ray walk classification.**
The step rule is constant (the ray advances by `s % 5` each stride), and the walk of the
first five strides is determined by `s % 5`: strides `≡ 2 (mod 5)` trace the pentagram order
`[2,4,1,3,0]`, `≡ 3` its mirror `[3,1,4,2,0]`, `≡ 1` the pentagon `[1,2,3,4,0]`, `≡ 4` its
mirror `[4,3,2,1,0]`, and `≡ 0` never leaves ray `0`. -/
