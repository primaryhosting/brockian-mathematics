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

/-- The constant ray-step law: each successive multiple of `s` advances the ray index
by `s % 5`. -/

theorem ray_step (s k : Nat) : ((k + 1) * s) % 5 = (k * s % 5 + s % 5) % 5 := by
  induction k with
  | zero => simp
  | succ n _ => rw [Nat.add_mul, Nat.one_mul, Nat.add_mod]

/-- The multiples of a stride `s` walk the five rays in a fixed cyclic order determined
by `s % 5`: strides `≡ 2 (mod 5)` trace the pentagram order `(2,4,1,3,0)`, strides
`≡ 3` its mirror `(3,1,4,2,0)`, strides `≡ 1` the pentagon `(1,2,3,4,0)`, strides `≡ 4`
its mirror `(4,3,2,1,0)`, and strides `≡ 0` never leave ray `0`. -/
