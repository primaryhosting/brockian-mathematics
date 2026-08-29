import Mathlib
/-!
# Stride Ray Walk Classification
Category: Cone Line
Target: Brockian.ConeLine.stride_ray_walk_classification
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Brockian.ConeLine

/-- Rewriting the ray index of the `(k+1)`-st multiple of `s` in terms of the
`k`-th one: the walk advances by the constant step `s % 5`. -/

theorem stride_ray_list (s : ℕ) :
    (List.range 5).map (fun k => ((k + 1) * s) % 5)
      = (List.range 5).map (fun k => ((k + 1) * (s % 5)) % 5) := by
  refine List.map_congr_left ?_
  intro k _
  simp [Nat.mul_mod]

/-- **Stride ray walk classification.**

The successive multiples of a stride `s` visit the five rays (indices mod `5`)
by advancing a constant step `s % 5` each time, and consequently the first five
rays visited are determined by `s % 5`: stride `≡ 2` traces the pentagram order
`[2,4,1,3,0]`, stride `≡ 3` its mirror `[3,1,4,2,0]`, stride `≡ 1` the pentagon
`[1,2,3,4,0]`, stride `≡ 4` its mirror `[4,3,2,1,0]`, and stride `≡ 0` never
leaves ray `0`. -/
