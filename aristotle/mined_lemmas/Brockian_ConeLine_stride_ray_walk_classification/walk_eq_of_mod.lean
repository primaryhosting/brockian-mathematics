/-!
# Stride Ray Walk Classification
Category: Cone Line
Target: Brockian.ConeLine.stride_ray_walk_classification
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

set_option relaxedAutoImplicit false
set_option autoImplicit false

namespace Brockian.ConeLine

/-- Only the residue `s % 5` of the stride matters for the ray index `(a * s) % 5`. -/

theorem walk_eq_of_mod (s r : Nat) (hs : s % 5 = r) :
    (List.range 5).map (fun k => ((k + 1) * s) % 5)
      = (List.range 5).map (fun k => ((k + 1) * r) % 5) := by
  have h : ∀ k : Nat, ((k + 1) * s) % 5 = ((k + 1) * r) % 5 := by
    intro k
    rw [mul_mod_five_stride, hs]
  simp only [h]

/-- **Stride ray walk classification.**  The ray index advances by the constant step
`s % 5` at each stride, and consequently the first five rays visited are determined by
`s % 5`: stride `≡ 2` (terminal digits 2, 7) traces the pentagram order `[2,4,1,3,0]`,
stride `≡ 3` (digits 3, 8) its mirror `[3,1,4,2,0]`, stride `≡ 1` the pentagon
`[1,2,3,4,0]`, stride `≡ 4` its mirror `[4,3,2,1,0]`, and stride `≡ 0` never leaves
ray `0`. -/
