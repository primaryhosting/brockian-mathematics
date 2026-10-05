/-
# No Deleting
Category: Frontier Qi
Target: QI.no_deleting
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

-- (Lean 4 requires `import` lines to precede any module docstring, so the header above is
-- reproduced verbatim as a module docstring immediately after the import.)
import Mathlib

/-!
# No Deleting
Category: Frontier Qi
Target: QI.no_deleting
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace QI

/-- A single qubit: the two-dimensional complex Hilbert space. -/
abbrev Qubit := EuclideanSpace ℂ (Fin 2)

/-- Two qubits: the tensor product of two copies of `Qubit`, realized concretely as
`EuclideanSpace ℂ (Fin 2 × Fin 2)`. -/
abbrev TwoQubit := EuclideanSpace ℂ (Fin 2 × Fin 2)

/-- The tensor product `a ⊗ b` of two qubit states. -/
noncomputable def tensor (a b : Qubit) : TwoQubit :=
  WithLp.toLp 2 (fun p => a p.1 * b p.2)

@[simp] lemma tensor_apply (a b : Qubit) (p : Fin 2 × Fin 2) :
    tensor a b p = a p.1 * b p.2 := by
  simp [tensor]

/-- Inner products factor through the tensor product. -/
lemma inner_tensor_tensor (a b c d : Qubit) :
    (inner ℂ (tensor a b) (tensor c d) : ℂ) = inner ℂ a c * inner ℂ b d := by
  simp [PiLp.inner_apply, Fintype.sum_prod_type]
  ring_nf

/-- The computational basis state `|0⟩`. -/
noncomputable def e0 : Qubit := WithLp.toLp 2 ![1, 0]

/-- A qubit state non-orthogonal to, and different from, `|0⟩`. -/
noncomputable def v : Qubit := WithLp.toLp 2 ![3 / 5, 4 / 5]

@[simp] lemma e0_apply (i : Fin 2) : e0 i = ![1, 0] i := by simp [e0]

@[simp] lemma v_apply (i : Fin 2) : v i = ![3 / 5, 4 / 5] i := by simp [v]

lemma norm_e0 : ‖e0‖ = 1 := by
  simp [EuclideanSpace.norm_eq, Fin.sum_univ_two]

lemma norm_v : ‖v‖ = 1 := by
  rw [EuclideanSpace.norm_eq]
  norm_num [Fin.sum_univ_two, Complex.norm_ofNat]

lemma inner_e0_v : (inner ℂ e0 v : ℂ) = 3 / 5 := by
  simp [PiLp.inner_apply, Fin.sum_univ_two]

lemma inner_e0_e0 : (inner ℂ e0 e0 : ℂ) = 1 := by
  rw [inner_self_eq_norm_sq_to_K, norm_e0]
  norm_num

/-- **No-deleting theorem, isometry form.** There is no linear isometry `U` of the two-qubit
space, and no fixed "blank" state, such that `U (ψ ⊗ ψ) = ψ ⊗ blank` for every unit vector
`ψ`. (No normalization of `blank` is assumed: it is forced by the hypothesis.) -/
theorem no_deleting_isometry :
    ¬ ∃ (U : TwoQubit →ₗᵢ[ℂ] TwoQubit) (blank : Qubit),
        ∀ ψ : Qubit, ‖ψ‖ = 1 → U (tensor ψ ψ) = tensor ψ blank := by
  rintro ⟨U, blank, hU⟩
  -- The blank state is automatically a unit vector.
  have hbb : (inner ℂ blank blank : ℂ) = 1 := by
    have h : (inner ℂ (U (tensor e0 e0)) (U (tensor e0 e0)) : ℂ)
        = inner ℂ (tensor e0 e0) (tensor e0 e0) := U.inner_map_map _ _
    rw [hU e0 norm_e0, inner_tensor_tensor, inner_tensor_tensor, inner_e0_e0] at h
    simpa using h
  -- Preservation of the inner product of `e0 ⊗ e0` and `v ⊗ v` forces `(3/5)^2 = 3/5`.
  have key : (inner ℂ (U (tensor e0 e0)) (U (tensor v v)) : ℂ)
      = inner ℂ (tensor e0 e0) (tensor v v) := U.inner_map_map _ _
  rw [hU e0 norm_e0, hU v norm_v, inner_tensor_tensor, inner_tensor_tensor, hbb,
    inner_e0_v] at key
  norm_num at key

/-- **No-deleting theorem.** There is no unitary `U` on two qubits together with a fixed
"blank" state such that `U (ψ ⊗ ψ) = ψ ⊗ blank` for every unit vector `ψ`; that is, no
unitary can delete an unknown quantum state against a copy of itself. -/
theorem no_deleting :
    ¬ ∃ (U : TwoQubit ≃ₗᵢ[ℂ] TwoQubit) (blank : Qubit),
        ∀ ψ : Qubit, ‖ψ‖ = 1 → U (tensor ψ ψ) = tensor ψ blank := by
  rintro ⟨U, blank, hU⟩
  exact no_deleting_isometry ⟨U.toLinearIsometry, blank, hU⟩

end QI

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

