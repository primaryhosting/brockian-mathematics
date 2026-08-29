/-
/-!
# No Cloning
Category: Quantum Computing
Target: QC.no_cloning
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/
-/

import Mathlib

/-!
# No Cloning
Category: Quantum Computing
Target: QC.no_cloning
Verification: verified (axioms: propext, Classical.choice, Quot.sound)
Provenance: Aristotle theorem prover (Harmonic)
-/
namespace QC

/-- The qubit Hilbert space `H = ℂ²`. -/
abbrev Qubit := EuclideanSpace ℂ (Fin 2)

/-- The two-qubit space `H ⊗ H`, realized concretely as `ℂ^(2×2)`. -/
abbrev QubitPair := EuclideanSpace ℂ (Fin 2 × Fin 2)

/-- The computational basis states `|0⟩` and `|1⟩`. -/
noncomputable def ket (i : Fin 2) : Qubit := EuclideanSpace.single i 1

/-- The (elementary) tensor product `|a⟩ ⊗ |b⟩ ∈ H ⊗ H`. -/
noncomputable def tens (a b : Qubit) : QubitPair :=
  WithLp.toLp 2 (fun p => a p.1 * b p.2)

@[simp] lemma tens_apply (a b : Qubit) (p : Fin 2 × Fin 2) : tens a b p = a p.1 * b p.2 := rfl

lemma tens_add_left (a b c : Qubit) : tens (a + b) c = tens a c + tens b c := by
  ext p; simp [add_mul]

lemma tens_smul_left (r : ℂ) (a c : Qubit) : tens (r • a) c = r • tens a c := by
  ext p; simp [mul_assoc]

/-- The uniform superposition `|+⟩ = (|0⟩ + |1⟩)/√2`. -/
noncomputable def plus : Qubit := ((Real.sqrt 2 : ℝ) : ℂ)⁻¹ • (ket 0 + ket 1)

lemma norm_ket (i : Fin 2) : ‖ket i‖ = 1 := by simp [ket]

lemma norm_plus : ‖plus‖ = 1 := by
  have h2 : ‖ket 0 + ket 1‖ = Real.sqrt 2 := by
    rw [EuclideanSpace.norm_eq]
    norm_num [ket, Fin.sum_univ_two, EuclideanSpace.single_apply]
  rw [plus, norm_smul, h2, norm_inv, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (Real.sqrt_nonneg 2)]
  field_simp

lemma plus_apply (i : Fin 2) : plus i = ((Real.sqrt 2 : ℝ) : ℂ)⁻¹ := by
  fin_cases i <;> simp [plus, ket, EuclideanSpace.single_apply]

/-- **No-cloning theorem.**  There is no unitary `U` on `H ⊗ H` (here `H = ℂ²`,
represented as a surjective linear isometry of `H ⊗ H`) satisfying
`U (|ψ⟩ ⊗ |0⟩) = |ψ⟩ ⊗ |ψ⟩` for every state `|ψ⟩` (i.e. every unit vector).

The obstruction is linearity: cloning `|0⟩` and `|1⟩` forces `U` to send
`|+⟩ ⊗ |0⟩` to `(|00⟩ + |11⟩)/√2`, which is not `|+⟩ ⊗ |+⟩`. -/
theorem no_cloning :
    ¬ ∃ U : QubitPair ≃ₗᵢ[ℂ] QubitPair,
      ∀ ψ : Qubit, ‖ψ‖ = 1 → U (tens ψ (ket 0)) = tens ψ ψ := by
  rintro ⟨U, hU⟩
  have h0 := hU (ket 0) (norm_ket 0)
  have h1 := hU (ket 1) (norm_ket 1)
  have hp := hU plus norm_plus
  rw [plus, tens_smul_left, tens_add_left, map_smul, map_add, h0, h1, ← plus] at hp
  -- Comparing the `(0,1)` components gives `0 = 1/2`.
  have hcomp := congrArg (fun v => v (0, 1)) hp
  simp [ket, EuclideanSpace.single_apply, plus_apply] at hcomp

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

