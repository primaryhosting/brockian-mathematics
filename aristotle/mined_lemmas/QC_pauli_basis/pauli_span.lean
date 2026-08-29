import Mathlib

/-!
# Pauli Basis
Category: Quantum Computing
Target: QC.pauli_basis
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

set_option grind.warning false

namespace QC

/-- The 2×2 identity (Pauli `I`). -/

lemma pauli_span : Submodule.span ℂ (Set.range pauli) = ⊤ := by
  refine Submodule.eq_top_iff'.2 fun M => ?_
  set c : Fin 4 → ℂ :=
    ![(M 0 0 + M 1 1) / 2, (M 0 1 + M 1 0) / 2,
      Complex.I * (M 0 1 - M 1 0) / 2, (M 0 0 - M 1 1) / 2] with hcdef
  have hc0 : c 0 = (M 0 0 + M 1 1) / 2 := by rw [hcdef]; rfl
  have hc1 : c 1 = (M 0 1 + M 1 0) / 2 := by rw [hcdef]; rfl
  have hc2 : c 2 = Complex.I * (M 0 1 - M 1 0) / 2 := by rw [hcdef]; rfl
  have hc3 : c 3 = (M 0 0 - M 1 1) / 2 := by rw [hcdef]; rfl
  have e00 : c 0 + c 3 = M 0 0 := by rw [hc0, hc3]; ring
  have e11 : c 0 - c 3 = M 1 1 := by rw [hc0, hc3]; ring
  have e01 : c 1 - Complex.I * c 2 = M 0 1 := by
    rw [hc1, hc2]; linear_combination ((M 1 0 - M 0 1) / 2) * Complex.I_sq
  have e10 : c 1 + Complex.I * c 2 = M 1 0 := by
    rw [hc1, hc2]; linear_combination ((M 0 1 - M 1 0) / 2) * Complex.I_sq
  have hM : M = ∑ i, c i • pauli i := by
    rw [pauli_comb, e00, e01, e10, e11]
    exact (Matrix.etaExpand_eq M).symm
  rw [hM]
  refine Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ ?_
  exact Submodule.subset_span ⟨i, rfl⟩

/-- The Pauli matrices `{I, X, Y, Z}` form a basis of the ℂ-vector space of
2×2 complex matrices. -/
