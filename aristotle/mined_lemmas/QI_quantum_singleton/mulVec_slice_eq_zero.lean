/-
# Quantum Singleton
Category: Frontier Qi
Target: QI.quantum_singleton
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Quantum Singleton
Category: Frontier Qi
Target: QI.quantum_singleton
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open Matrix ComplexConjugate
open scoped BigOperators ComplexOrder

namespace QI

/-! ## Linear-algebra preliminaries -/

section RankLemmas

variable {X Y : Type*}

/-- Rank–nullity for the linear map `v ↦ M *ᵥ v`. -/

lemma mulVec_slice_eq_zero [Fintype X] [DecidableEq X] [Fintype Y] [DecidableEq Y]
    (ρ : Matrix (X × Y) (X × Y) ℂ) (hρ : ρ.PosSemidef) (u : X → ℂ)
    (hu : (Matrix.of fun x x' : X => ∑ y, ρ (x, y) (x', y)) *ᵥ u = 0) (y0 : Y) :
    ρ *ᵥ (fun p : X × Y => if p.2 = y0 then u p.1 else 0) = 0 := by
  classical
  have hquad : ∀ y : Y, star (fun p : X × Y => if p.2 = y then u p.1 else 0) ⬝ᵥ
        ρ *ᵥ (fun p : X × Y => if p.2 = y then u p.1 else 0)
      = ∑ x, ∑ x', (starRingEnd ℂ) (u x) * (ρ (x, y) (x', y) * u x') := by
    intro y
    simp [dotProduct, Matrix.mulVec, Fintype.sum_prod_type, ite_mul, apply_ite,
      Finset.sum_ite_eq', Finset.mul_sum]
  have htot : star u ⬝ᵥ (Matrix.of fun x x' : X => ∑ y, ρ (x, y) (x', y)) *ᵥ u
      = ∑ y, ∑ x, ∑ x', (starRingEnd ℂ) (u x) * (ρ (x, y) (x', y) * u x') := by
    simp only [dotProduct, Matrix.mulVec, Matrix.of_apply, Pi.star_apply, RCLike.star_def,
      Finset.mul_sum, Finset.sum_mul]
    conv_rhs => rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun x _ => ?_
    conv_rhs => rw [Finset.sum_comm]
  have hzero : ∑ y : Y, star (fun p : X × Y => if p.2 = y then u p.1 else 0) ⬝ᵥ
      ρ *ᵥ (fun p : X × Y => if p.2 = y then u p.1 else 0) = 0 := by
    rw [Finset.sum_congr rfl (fun y _ => hquad y), ← htot, hu]
    simp
  have hnn : ∀ y ∈ (Finset.univ : Finset Y),
      (0 : ℂ) ≤ star (fun p : X × Y => if p.2 = y then u p.1 else 0) ⬝ᵥ
        ρ *ᵥ (fun p : X × Y => if p.2 = y then u p.1 else 0) :=
    fun y _ => hρ.dotProduct_mulVec_nonneg _
  have hy := (Finset.sum_eq_zero_iff_of_nonneg hnn).1 hzero y0 (Finset.mem_univ _)
  exact (hρ.dotProduct_mulVec_zero_iff _).1 hy

/-- For a positive semidefinite bipartite matrix, the rank is at most the rank of the partial
trace over the second factor, times the dimension of that factor. -/
