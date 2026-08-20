/-
# Pauli Basis
Category: Quantum Computing
Target: QC.pauli_basis
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

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

namespace QC

/-- The identity Pauli matrix `I`. -/
def pauliI : Matrix (Fin 2) (Fin 2) ℂ := !![1, 0; 0, 1]

/-- The Pauli matrix `X`. -/
def pauliX : Matrix (Fin 2) (Fin 2) ℂ := !![0, 1; 1, 0]

/-- The Pauli matrix `Y`. -/
def pauliY : Matrix (Fin 2) (Fin 2) ℂ := !![0, -Complex.I; Complex.I, 0]

/-- The Pauli matrix `Z`. -/
def pauliZ : Matrix (Fin 2) (Fin 2) ℂ := !![1, 0; 0, -1]

/-- The family `(I, X, Y, Z)` of Pauli matrices, indexed by `Fin 4`. -/
def pauli : Fin 4 → Matrix (Fin 2) (Fin 2) ℂ := ![pauliI, pauliX, pauliY, pauliZ]

lemma pauli_linearIndependent : LinearIndependent ℂ pauli := by
  rw [Fintype.linearIndependent_iff]
  intro g hg i
  have h : ∀ p q : Fin 2,
      (∑ j : Fin 4, g j • pauli j) p q = (0 : Matrix (Fin 2) (Fin 2) ℂ) p q := by
    intro p q; rw [hg]
  have h00 := h 0 0
  have h01 := h 0 1
  have h10 := h 1 0
  have h11 := h 1 1
  simp [pauli, pauliI, pauliX, pauliY, pauliZ, Fin.sum_univ_four,
    Matrix.add_apply, Matrix.zero_apply, smul_eq_mul] at h00 h01 h10 h11
  -- `h00 : g 0 + g 3 = 0`, `h11 : g 0 - g 3 = 0`, and similarly for `g 1`, `g 2`.
  have hI : Complex.I ≠ 0 := Complex.I_ne_zero
  have h0 : g 0 = 0 := by linear_combination (h00 + h11) / 2
  have h3 : g 3 = 0 := by linear_combination (h00 - h11) / 2
  have h1 : g 1 = 0 := by
    have h2 : (2 : ℂ) * g 1 = 0 := by linear_combination h01 + h10
    rcases mul_eq_zero.mp h2 with h | h
    · exact absurd h (by norm_num)
    · exact h
  have h2 : g 2 = 0 := by
    have hkey : Complex.I * (2 * g 2) = 0 := by
      linear_combination h10 - h01
    rcases mul_eq_zero.mp hkey with h | h
    · exact absurd h hI
    · rcases mul_eq_zero.mp h with h | h
      · exact absurd h (by norm_num)
      · exact h
  fin_cases i <;> assumption

lemma pauli_span : Submodule.span ℂ (Set.range pauli) = ⊤ := by
  rw [eq_top_iff]
  rintro M -
  have hdecomp : M = ((M 0 0 + M 1 1) / 2) • pauli 0 + ((M 0 1 + M 1 0) / 2) • pauli 1
      + (Complex.I * (M 0 1 - M 1 0) / 2) • pauli 2 + ((M 0 0 - M 1 1) / 2) • pauli 3 := by
    ext p q
    fin_cases p <;> fin_cases q <;>
      simp [pauli, pauliI, pauliX, pauliY, pauliZ, Matrix.add_apply, smul_eq_mul] <;>
      field_simp <;>
      ring_nf <;>
      simp [Complex.I_sq] <;>
      ring
  rw [hdecomp]
  refine Submodule.add_mem _ (Submodule.add_mem _ (Submodule.add_mem _ ?_ ?_) ?_) ?_ <;>
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨_, rfl⟩)

/-- The Pauli matrices `{I, X, Y, Z}` form a basis of the `ℂ`-vector space of `2 × 2`
complex matrices. -/
noncomputable def pauliBasis : Module.Basis (Fin 4) ℂ (Matrix (Fin 2) (Fin 2) ℂ) :=
  Module.Basis.mk pauli_linearIndependent (le_of_eq pauli_span.symm)

@[simp] lemma pauliBasis_apply (i : Fin 4) : pauliBasis i = pauli i :=
  Module.Basis.mk_apply _ _ _

/-- **Pauli basis**: the family `![I, X, Y, Z]` is linearly independent over `ℂ` and spans
the space of `2 × 2` complex matrices, i.e. it is a basis of that `ℂ`-vector space. -/
theorem pauli_basis :
    LinearIndependent ℂ pauli ∧ Submodule.span ℂ (Set.range pauli) = ⊤ ∧
      ∃ b : Module.Basis (Fin 4) ℂ (Matrix (Fin 2) (Fin 2) ℂ), ⇑b = pauli :=
  ⟨pauli_linearIndependent, pauli_span, pauliBasis, funext pauliBasis_apply⟩

end QC

