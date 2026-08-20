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
theorem ray_step (s k : Nat) : ((k + 1) * s) % 5 = (k * s % 5 + s % 5) % 5 := by
  rw [Nat.add_mul, Nat.one_mul, Nat.add_mod]

/-- With `s % 5 = r`, the first five rays visited only depend on `r`. -/
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
theorem stride_ray_walk_classification :
    (∀ s k : Nat, ((k + 1) * s) % 5 = (k * s % 5 + s % 5) % 5) ∧
    (∀ s : Nat, s % 5 = 2 →
      (List.range 5).map (fun k => ((k + 1) * s) % 5) = [2, 4, 1, 3, 0]) ∧
    (∀ s : Nat, s % 5 = 3 →
      (List.range 5).map (fun k => ((k + 1) * s) % 5) = [3, 1, 4, 2, 0]) ∧
    (∀ s : Nat, s % 5 = 1 →
      (List.range 5).map (fun k => ((k + 1) * s) % 5) = [1, 2, 3, 4, 0]) ∧
    (∀ s : Nat, s % 5 = 4 →
      (List.range 5).map (fun k => ((k + 1) * s) % 5) = [4, 3, 2, 1, 0]) ∧
    (∀ s : Nat, s % 5 = 0 →
      (List.range 5).map (fun k => ((k + 1) * s) % 5) = [0, 0, 0, 0, 0]) := by
  refine ⟨ray_step, ?_, ?_, ?_, ?_, ?_⟩ <;>
    · intro s hs
      rw [walk_eq_of_mod s _ hs]
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

