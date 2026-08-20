/-
# Quantum Singleton
Category: Frontier Qi
Target: QI.quantum_singleton
Statement: Quantum Singleton bound: an [[n,k,d]] code obeys n−k ≥ 2(d−1).
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Quantum Singleton
Category: Frontier Qi
Target: QI.quantum_singleton
Statement: Quantum Singleton bound: an [[n,k,d]] code obeys n−k ≥ 2(d−1).
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open Matrix Finset Module Kronecker ComplexOrder

namespace QI

/-! ## Linear algebra preliminaries -/

/-- Swap the first two factors of a triple product type. -/

lemma hasDistanceGE_one (hq : 0 < q) (M : Matrix (Fin n → Fin q) (Fin K) ℂ) (hM : Mᴴ * M = 1) :
    HasDistanceGE M 1 := by
  classical
  rintro T E hT ⟨F, hFdep, hE⟩
  have hT0 : T = ∅ := Finset.card_eq_zero.mp (by omega)
  subst hT0
  set x₀ : Fin n → Fin q := fun _ => ⟨0, hq⟩ with hx0
  refine ⟨F x₀ x₀, ?_⟩
  have hEeq : E = (F x₀ x₀) • (1 : Matrix (Fin n → Fin q) (Fin n → Fin q) ℂ) := by
    ext x y
    rw [hE x y]
    have hcond : (∀ i ∉ (∅ : Finset (Fin n)), x i = y i) ↔ x = y := by
      constructor
      · intro h; funext i; exact h i (by simp)
      · intro h i _; rw [h]
    have hFc : F x y = F x₀ x₀ := hFdep x x₀ y x₀ (by simp) (by simp)
    simp only [hcond, hFc]
    by_cases hxy : x = y <;> simp [hxy]
  rw [hEeq, Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_one, hM]

/-- A code of distance at least `d` corrects the erasure of any block of fewer than `d`
coordinates: the "reduced density matrix" on such a block does not depend on the codeword. -/
