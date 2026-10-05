import Mathlib

/-!
# Quantum Singleton
Category: Frontier Qi
Target: QI.quantum_singleton
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open scoped BigOperators
open scoped Real
open scoped Nat
open scoped Classical
open scoped Pointwise
open scoped Matrix
open scoped ComplexOrder

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

-- Note: the header block above is placed directly after `import Mathlib` because Lean requires
-- every `import` to precede all other commands, including module documentation comments.

namespace QI

/-! ## Auxiliary linear algebra: rank factorizations -/

/-- `LinearMap.toMatrix'` is inverse to `Matrix.mulVecLin`. -/

theorem exists_full_code (n q : ℕ) :
    ∃ ψ : Fin (q ^ n) → (Fin n → Fin q) → ℂ,
      (∀ i j : Fin (q ^ n),
        (∑ x : Fin n → Fin q, ψ i x * (starRingEnd ℂ) (ψ j x)) = if i = j then 1 else 0) ∧
      ∀ S : Finset (Fin n), S.card ≤ 1 - 1 → ErasureCorrectable ψ S := by
  classical
  have hcard : Fintype.card (Fin n → Fin q) = q ^ n := by simp
  let ee : Fin (q ^ n) ≃ (Fin n → Fin q) := (Fintype.equivFinOfCardEq hcard).symm
  refine ⟨fun i x => if x = ee i then 1 else 0, ?_, ?_⟩
  · intro i j
    by_cases h : i = j
    · subst h
      simp
    · have h' : ee i ≠ ee j := fun hc => h (ee.injective hc)
      simp [h, Ne.symm h', Finset.sum_ite_eq', apply_ite (starRingEnd ℂ)]
  · intro S hS
    have : S = ∅ := Finset.card_eq_zero.mp (by omega)
    subst this
    refine erasureCorrectable_empty _ ?_
    intro i j
    by_cases h : i = j
    · subst h
      simp
    · have h' : ee i ≠ ee j := fun hc => h (ee.injective hc)
      simp [h, Ne.symm h', Finset.sum_ite_eq', apply_ite (starRingEnd ℂ)]

end QI

