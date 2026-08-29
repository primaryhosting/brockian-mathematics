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

namespace QC

open Matrix

/-- The identity Pauli matrix `I`. -/
def pauliI : Matrix (Fin 2) (Fin 2) ℂ := !![1, 0; 0, 1]

/-- The Pauli matrix `X`. -/
def pauliX : Matrix (Fin 2) (Fin 2) ℂ := !![0, 1; 1, 0]

/-- The Pauli matrix `Y`. -/
def pauliY : Matrix (Fin 2) (Fin 2) ℂ := !![0, -Complex.I; Complex.I, 0]

/-- The Pauli matrix `Z`. -/
def pauliZ : Matrix (Fin 2) (Fin 2) ℂ := !![1, 0; 0, -1]

/-- The family `{I, X, Y, Z}` of Pauli matrices, indexed by `Fin 4`. -/
def pauli : Fin 4 → Matrix (Fin 2) (Fin 2) ℂ := ![pauliI, pauliX, pauliY, pauliZ]

lemma pauli_linearIndependent : LinearIndependent ℂ pauli := by
  rw [Fintype.linearIndependent_iff]
  intro g hg
  have h : ∀ a b, (∑ i, g i • pauli i) a b = 0 := by
    intro a b; rw [hg]; simp
  have h00 := h 0 0
  have h01 := h 0 1
  have h10 := h 1 0
  have h11 := h 1 1
  simp [Fin.sum_univ_four, pauli, pauliI, pauliX, pauliY, pauliZ] at h00 h01 h10 h11
  have hI : (Complex.I : ℂ) ≠ 0 := Complex.I_ne_zero
  have hg0 : g 0 = 0 := by linear_combination (h00 + h11) / 2
  have hg3 : g 3 = 0 := by linear_combination (h00 - h11) / 2
  have hg1 : g 1 = 0 := by linear_combination (h01 + h10) / 2
  have hg2 : g 2 = 0 := by
    have h2 : Complex.I * g 2 = 0 := by linear_combination (h10 - h01) / 2
    exact (mul_eq_zero.1 h2).resolve_left hI
  intro i
  fin_cases i <;> assumption

lemma pauli_span : Submodule.span ℂ (Set.range pauli) = ⊤ := by
  rw [eq_top_iff]
  rintro M -
  rw [Submodule.mem_span_range_iff_exists_fun]
  refine ⟨![(M 0 0 + M 1 1) / 2, (M 0 1 + M 1 0) / 2,
      Complex.I * (M 0 1 - M 1 0) / 2, (M 0 0 - M 1 1) / 2], ?_⟩
  ext a b
  fin_cases a <;> fin_cases b <;>
    simp [Fin.sum_univ_four, pauli, pauliI, pauliX, pauliY, pauliZ] <;>
    ring_nf <;> (try simp [Complex.I_sq]) <;> (try ring)

/-- `{I, X, Y, Z}` is a basis of the `ℂ`-vector space of `2 × 2` complex matrices. -/
noncomputable def pauliBasis : Module.Basis (Fin 4) ℂ (Matrix (Fin 2) (Fin 2) ℂ) :=
  Module.Basis.mk pauli_linearIndependent (le_of_eq pauli_span.symm)

@[simp] lemma coe_pauliBasis : ⇑pauliBasis = pauli := Module.Basis.coe_mk _ _

/-- **Pauli basis.** The four Pauli matrices `I, X, Y, Z` form a basis of the
`ℂ`-vector space of `2 × 2` complex matrices: they are linearly independent, they
span, and hence they underlie a `Module.Basis (Fin 4) ℂ (Matrix (Fin 2) (Fin 2) ℂ)`. -/
theorem pauli_basis :
    LinearIndependent ℂ pauli ∧ Submodule.span ℂ (Set.range pauli) = ⊤ ∧
      ∃ B : Module.Basis (Fin 4) ℂ (Matrix (Fin 2) (Fin 2) ℂ), ⇑B = pauli :=
  ⟨pauli_linearIndependent, pauli_span, pauliBasis, coe_pauliBasis⟩

end QC

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

