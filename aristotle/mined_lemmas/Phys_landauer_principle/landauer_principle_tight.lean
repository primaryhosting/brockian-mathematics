/-
# Landauer Principle
Category: Frontier Phys
Target: Phys.landauer_principle
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Landauer Principle
Category: Frontier Phys
Target: Phys.landauer_principle
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

set_option pp.fullNames true
set_option pp.structureInstances true
set_option pp.coercions.types true
set_option pp.funBinderTypes true
set_option pp.letVarTypes true
set_option pp.piBinderTypes true

set_option grind.warning false

namespace Phys

/-- Shannon entropy (in nats) of a finitely supported probability vector `p`.
Terms with `p x = 0` contribute `0`, since `Real.log 0 = 0`. -/

theorem landauer_principle_tight (k T : ℝ) (hT : 0 < T) :
    ∃ (p q : Bool → ℝ) (Q : ℝ), (∀ b : Bool, p b = 1 / 2) ∧ IsDeterministic q ∧
      0 ≤ k * (shannonEntropy q - shannonEntropy p) + Q / T ∧ Q = k * T * Real.log 2 := by
  refine ⟨fun _ => 1 / 2, fun b => if b = false then 1 else 0, k * T * Real.log 2,
    fun _ => rfl, ⟨false, fun _ => rfl⟩, ?_, rfl⟩
  have hpE : shannonEntropy (fun _ : Bool => (1 : ℝ) / 2) = Real.log 2 :=
    shannonEntropy_uniform_bool (fun _ => rfl)
  have hqE : shannonEntropy (fun b : Bool => if b = false then (1 : ℝ) else 0) = 0 :=
    shannonEntropy_eq_zero_of_isDeterministic ⟨false, fun _ => rfl⟩
  rw [hpE, hqE]
  have hdiv : k * T * Real.log 2 / T = k * Real.log 2 := by
    field_simp
  rw [hdiv]
  have hzero : k * (0 - Real.log 2) + k * Real.log 2 = 0 := by ring
  rw [hzero]

end Phys

