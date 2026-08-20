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

theorem mul_mod_five_stride (a s : Nat) : (a * s) % 5 = (a * (s % 5)) % 5 := by
  rw [Nat.mul_mod a (s % 5), Nat.mod_mod_of_dvd s (Nat.dvd_refl 5), ← Nat.mul_mod]

/-- Key intermediate lemma (constant ray-step): each stride advances the ray index by the
constant amount `s % 5`. -/
