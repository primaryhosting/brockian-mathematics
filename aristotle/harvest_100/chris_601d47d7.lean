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
theorem stride_ray_step (s k : ℕ) : ((k + 1) * s) % 5 = (k * s % 5 + s % 5) % 5 := by
  conv_lhs => rw [Nat.add_mul, one_mul, Nat.add_mod]

/-- Multiplying by `s` mod `5` only depends on `s % 5`. -/
theorem stride_mul_mod (n s : ℕ) : (n * s) % 5 = (n * (s % 5)) % 5 := by
  simp [Nat.mul_mod]

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
theorem stride_ray_walk_classification :
    (∀ s k : ℕ, ((k + 1) * s) % 5 = (k * s % 5 + s % 5) % 5) ∧
    (∀ s : ℕ, s % 5 = 2 →
      (List.range 5).map (fun k => ((k + 1) * s) % 5) = [2, 4, 1, 3, 0]) ∧
    (∀ s : ℕ, s % 5 = 3 →
      (List.range 5).map (fun k => ((k + 1) * s) % 5) = [3, 1, 4, 2, 0]) ∧
    (∀ s : ℕ, s % 5 = 1 →
      (List.range 5).map (fun k => ((k + 1) * s) % 5) = [1, 2, 3, 4, 0]) ∧
    (∀ s : ℕ, s % 5 = 4 →
      (List.range 5).map (fun k => ((k + 1) * s) % 5) = [4, 3, 2, 1, 0]) ∧
    (∀ s : ℕ, s % 5 = 0 →
      (List.range 5).map (fun k => ((k + 1) * s) % 5) = [0, 0, 0, 0, 0]) := by
  refine ⟨stride_ray_step, ?_, ?_, ?_, ?_, ?_⟩ <;>
  · intro s h
    rw [walk_of s _ h]
    decide

end Brockian.ConeLine

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

set_option pp.fullNames true
set_option pp.structureInstances true
set_option pp.coercions.types true
set_option pp.funBinderTypes true
set_option pp.letVarTypes true
set_option pp.piBinderTypes true

set_option grind.warning false

