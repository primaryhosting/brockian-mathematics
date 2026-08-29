import Mathlib

/-!
# Ghz 5 Normalized
Category: Quantum Computing
Target: QC.ghz5_normalized
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace QC

/-- The 5-qubit GHZ state `(|00000⟩ + |11111⟩)/√2`, as a vector in the
Hilbert space `EuclideanSpace ℂ (Fin 5 → Bool)` whose computational basis is
indexed by bit strings of length 5. -/
noncomputable def ghz5 : EuclideanSpace ℂ (Fin 5 → Bool) :=
  WithLp.toLp 2 fun q =>
    if q = (fun _ => false) ∨ q = (fun _ => true) then ((Real.sqrt 2)⁻¹ : ℂ) else 0

/-- `ghz5` is indeed `(1/√2) • (|00000⟩ + |11111⟩)`, where `|00000⟩` and `|11111⟩`
are the computational basis vectors for the all-zeros and all-ones bit strings. -/
theorem ghz5_eq_smul_add_single :
    ghz5 = ((Real.sqrt 2)⁻¹ : ℂ) •
      (EuclideanSpace.single (fun _ => false) (1 : ℂ)
        + EuclideanSpace.single (fun _ => true) (1 : ℂ)) := by
  have hz : ((fun _ => false : Fin 5 → Bool)) ≠ (fun _ => true) := by
    intro h; have := congrFun h 0; simp at this
  ext q
  rcases eq_or_ne q (fun _ => false) with h | h
  · subst h; simp [ghz5, hz, EuclideanSpace.single_apply]
  · rcases eq_or_ne q (fun _ => true) with h' | h'
    · subst h'; simp [ghz5, h, EuclideanSpace.single_apply]
    · simp [ghz5, h, h', EuclideanSpace.single_apply]

/-- The 5-qubit GHZ state `(|00000⟩ + |11111⟩)/√2` is a unit vector. -/
theorem ghz5_normalized : ‖ghz5‖ = 1 := by
  have hz : ((fun _ => false : Fin 5 → Bool)) ≠ (fun _ => true) := by
    intro h; have := congrFun h 0; simp at this
  have hsum : ∀ q : Fin 5 → Bool, ‖ghz5 q‖ ^ 2
      = (if q = (fun _ => false) then (1 / 2 : ℝ) else 0)
        + (if q = (fun _ => true) then (1 / 2 : ℝ) else 0) := by
    intro q
    rcases eq_or_ne q (fun _ => false) with h | h
    · subst h; simp [ghz5, hz]
    · rcases eq_or_ne q (fun _ => true) with h' | h'
      · subst h'; simp [ghz5, h]
      · simp [ghz5, h, h']
  rw [EuclideanSpace.norm_eq]
  simp only [hsum]
  rw [Finset.sum_add_distrib, Finset.sum_ite_eq' Finset.univ, Finset.sum_ite_eq' Finset.univ]
  norm_num

end QC

#print axioms QC.ghz5_normalized
#print axioms QC.ghz5_eq_smul_add_single

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

