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
theorem stride_ray_step (s k : ℕ) : ((k + 1) * s) % 5 = (k * s % 5 + s % 5) % 5 := by
  rw [add_mul, one_mul, Nat.add_mod]

/-- The first five ray indices only depend on `s % 5`. -/
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
    · intro s hs
      rw [stride_ray_list, hs]
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

