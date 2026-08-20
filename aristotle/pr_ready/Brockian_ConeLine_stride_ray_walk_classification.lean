/-!
# Stride Ray Walk Classification
Category: Brockian External
Target: Brockian.ConeLine.stride_ray_walk_classification
Statement: The multiples of s walk the rays in the fixed cyclic order determined by s mod 5: strides ≡ 2 (terminal digits 2,7) trace the pentagram order (2,4,1,3,0); ≡ 3 (digits 3,8) its mirror (3,1,4,2,0); ≡ 1 the pentagon (1,2,3,4,0); ≡ 4 its mirror; ≡ 0 never leave ray 0.
Verified: AXLE cloud (Lean 4.32.0, Mathlib), axiom-clean
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

open scoped BigOperators
open scoped Real
open scoped Nat
open scoped Classical
open scoped Pointwise

set_option maxHeartbeats 8000000
set_option maxRecDepth 4000
set_option synthInstance.maxHeartbeats 20000
set_option synthInstance.maxSize 128

set_option relaxedAutoImplicit false
set_option autoImplicit false

set_option grind.warning false

namespace Brockian.ConeLine

/-- The ray reached after `k+1` strides of length `s`, i.e. `((k+1)*s) % 5`. -/
def rayWalk (s : ℕ) : List ℕ := (List.range 5).map (fun k => ((k + 1) * s) % 5)

/-- Each stride advances the ray by the constant `s % 5`. -/
theorem ray_step (s k : ℕ) : ((k + 1) * s) % 5 = (k * s % 5 + s % 5) % 5 := by
  rw [Nat.add_mul, one_mul, Nat.add_mod]

/-- The walk of `s` on the five rays is determined by `s % 5`:
    `≡ 2` traces the pentagram order `[2,4,1,3,0]`, `≡ 3` its mirror `[3,1,4,2,0]`,
    `≡ 1` the pentagon `[1,2,3,4,0]`, `≡ 4` its mirror `[4,3,2,1,0]`,
    and `≡ 0` never leaves ray `0`. -/
theorem stride_ray_walk_classification :
    (∀ s k : ℕ, ((k + 1) * s) % 5 = (k * s % 5 + s % 5) % 5) ∧
    (∀ s : ℕ, s % 5 = 2 → rayWalk s = [2, 4, 1, 3, 0]) ∧
    (∀ s : ℕ, s % 5 = 3 → rayWalk s = [3, 1, 4, 2, 0]) ∧
    (∀ s : ℕ, s % 5 = 1 → rayWalk s = [1, 2, 3, 4, 0]) ∧
    (∀ s : ℕ, s % 5 = 4 → rayWalk s = [4, 3, 2, 1, 0]) ∧
    (∀ s : ℕ, s % 5 = 0 → rayWalk s = [0, 0, 0, 0, 0]) := by
  refine ⟨ray_step, ?_, ?_, ?_, ?_, ?_⟩ <;>
    intro s hs <;>
    simp [rayWalk, List.range_succ, Nat.mul_mod, hs]

end Brockian.ConeLine

