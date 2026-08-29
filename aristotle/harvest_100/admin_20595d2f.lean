import Mathlib

/-!
# Stride Ray Walk Classification
Category: Cone Line
Target: Brockian.ConeLine.stride_ray_walk_classification
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

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

namespace Brockian.ConeLine

/-- **Stride ray walk classification.**

The successive multiples of a stride `s` walk the five rays (residues mod 5) by a constant
step: passing from `k*s` to `(k+1)*s` always advances the ray index by `s % 5`.
Consequently the first five multiples visit the rays in a fixed cyclic order determined by
`s % 5`: strides `≡ 2` trace the pentagram order `[2,4,1,3,0]`, strides `≡ 3` its mirror
`[3,1,4,2,0]`, strides `≡ 1` the pentagon `[1,2,3,4,0]`, strides `≡ 4` its mirror
`[4,3,2,1,0]`, and strides `≡ 0` never leave ray `0`. -/
theorem stride_ray_walk_classification :
    (∀ s k : ℕ, ((k + 1) * s) % 5 = (k * s % 5 + s % 5) % 5) ∧
    (∀ s : ℕ, s % 5 = 2 → (List.range 5).map (fun k => ((k + 1) * s) % 5) = [2, 4, 1, 3, 0]) ∧
    (∀ s : ℕ, s % 5 = 3 → (List.range 5).map (fun k => ((k + 1) * s) % 5) = [3, 1, 4, 2, 0]) ∧
    (∀ s : ℕ, s % 5 = 1 → (List.range 5).map (fun k => ((k + 1) * s) % 5) = [1, 2, 3, 4, 0]) ∧
    (∀ s : ℕ, s % 5 = 4 → (List.range 5).map (fun k => ((k + 1) * s) % 5) = [4, 3, 2, 1, 0]) ∧
    (∀ s : ℕ, s % 5 = 0 → (List.range 5).map (fun k => ((k + 1) * s) % 5) = [0, 0, 0, 0, 0]) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro s k
    rw [add_mul, one_mul, Nat.add_mod]
  · intro s hs
    simp [List.range_succ, Nat.mul_mod, hs]
  · intro s hs
    simp [List.range_succ, Nat.mul_mod, hs]
  · intro s hs
    simp [List.range_succ, Nat.mul_mod, hs]
  · intro s hs
    simp [List.range_succ, Nat.mul_mod, hs]
  · intro s hs
    simp [List.range_succ, Nat.mul_mod, hs]

end Brockian.ConeLine

