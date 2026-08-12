import Mathlib

/-!
# No Deleting
Category: Frontier Qi
Target: QI.no_deleting
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

/-!
## Setting

We work with a single qubit `H = EuclideanSpace ℂ (Fin 2)` and the two-qubit space
`K = EuclideanSpace ℂ (Fin 2 × Fin 2)`, with the tensor product of two one-qubit
states given explicitly by `QI.tens x y (i, j) = x i * y j`.

A *deleting machine* would be a unitary `U` on `K` together with a fixed "blank"
state `blank` such that `U (ψ ⊗ ψ) = ψ ⊗ blank` for every state `ψ`, i.e. one of
the two copies of the unknown state `ψ` is erased and replaced by the standard
blank state.  The no-deleting theorem says that no such unitary exists.
-/

namespace QI

/-- A single qubit. -/
abbrev H := EuclideanSpace ℂ (Fin 2)

/-- Two qubits. -/
abbrev K := EuclideanSpace ℂ (Fin 2 × Fin 2)

/-- The tensor product of two one-qubit states, in coordinates. -/
noncomputable def tens (x y : H) : K :=
  WithLp.toLp 2 (fun p => x.ofLp p.1 * y.ofLp p.2)

/-- The computational basis state `|0⟩`. -/
noncomputable def ket0 : H := !₂[1, 0]

/-- The computational basis state `|1⟩`. -/
noncomputable def ket1 : H := !₂[0, 1]

lemma norm_qubit (p q : ℂ) (h : ‖p‖ ^ 2 + ‖q‖ ^ 2 = 1) : ‖(!₂[p, q] : H)‖ = 1 := by
  simp [EuclideanSpace.norm_eq, Fin.sum_univ_two, h]

/-- Expansion of `ψ ⊗ ψ` in the computational basis, for `ψ = (p, q)`. -/
lemma tens_self_expand (p q : ℂ) :
    tens !₂[p, q] !₂[p, q]
      = (p * p) • tens ket0 ket0 + (p * q) • (tens ket0 ket1 + tens ket1 ket0)
        + (q * q) • tens ket1 ket1 := by
  ext r
  obtain ⟨i, j⟩ := r
  fin_cases i <;> fin_cases j <;> simp [tens, ket0, ket1, mul_comm]

/-- Expansion of `ψ ⊗ s` in the first factor, for `ψ = (p, q)`. -/
lemma tens_left_expand (p q : ℂ) (s : H) :
    tens !₂[p, q] s = p • tens ket0 s + q • tens ket1 s := by
  ext r
  obtain ⟨i, j⟩ := r
  fin_cases i <;> simp [tens, ket0, ket1]

/-- If `ψ ⊗ blank + ψ' ⊗ blank = 0` for the two basis states, then `blank = 0`. -/
lemma blank_eq_zero_of_tens_add {blank : H}
    (h : tens ket0 blank + tens ket1 blank = 0) : blank = 0 := by
  ext j
  have hj : (tens ket0 blank + tens ket1 blank).ofLp (0, j) = (0 : K).ofLp (0, j) := by
    rw [h]
  simpa [tens, ket0, ket1] using hj

/-- **No deleting, linear version.**  Already the linearity of `U` (unitarity is not
needed) forbids a machine that maps `ψ ⊗ ψ` to `ψ ⊗ blank` for every unit vector `ψ`,
where `blank` is a fixed unit vector. -/
theorem no_deleting_linear (U : K →ₗ[ℂ] K) (blank : H) (hblank : ‖blank‖ = 1)
    (hU : ∀ ψ : H, ‖ψ‖ = 1 → U (tens ψ ψ) = tens ψ blank) : False := by
  set A := tens ket0 blank with hA
  set B := tens ket1 blank with hB
  set X := U (tens ket0 ket1) + U (tens ket1 ket0) with hX
  have h0 : U (tens ket0 ket0) = A := by
    have : ket0 = !₂[(1 : ℂ), 0] := rfl
    rw [this]
    exact hU _ (norm_qubit 1 0 (by norm_num))
  have h1 : U (tens ket1 ket1) = B := by
    have : ket1 = !₂[(0 : ℂ), 1] := rfl
    rw [this]
    exact hU _ (norm_qubit 0 1 (by norm_num))
  have key : ∀ p q : ℂ, ‖p‖ ^ 2 + ‖q‖ ^ 2 = 1 →
      (p * p) • A + (p * q) • X + (q * q) • B = p • A + q • B := by
    intro p q hpq
    have h := hU !₂[p, q] (norm_qubit p q hpq)
    rw [tens_self_expand p q, tens_left_expand p q blank] at h
    simpa [map_add, map_smul, h0, h1, hX, smul_add] using h
  have eq1 := key ((1 + Complex.I) / 2) ((1 + Complex.I) / 2) (by
    rw [Complex.sq_norm]
    simp [Complex.normSq_apply]
    norm_num)
  have eq2 := key ((1 + Complex.I) / 2) ((1 - Complex.I) / 2) (by
    rw [Complex.sq_norm, Complex.sq_norm]
    simp [Complex.normSq_apply]
    norm_num)
  have hAB : A + B = 0 := by
    linear_combination (norm := (match_scalars <;> simp [Complex.ext_iff] <;> norm_num))
      (-(1 + Complex.I)) • eq1 + (Complex.I - 1) • eq2
  have : blank = 0 := blank_eq_zero_of_tens_add (by rw [hA, hB] at hAB; exact hAB)
  rw [this] at hblank
  simp at hblank

/-- **The no-deleting theorem.**  There is no unitary `U` on two qubits and no fixed
blank state `blank` such that `U (ψ ⊗ ψ) = ψ ⊗ blank` for every one-qubit state `ψ`:
an unknown quantum state cannot be deleted. -/
theorem no_deleting :
    ¬ ∃ (U : K ≃ₗᵢ[ℂ] K) (blank : H), ‖blank‖ = 1 ∧
        ∀ ψ : H, ‖ψ‖ = 1 → U (tens ψ ψ) = tens ψ blank := by
  rintro ⟨U, blank, hblank, hU⟩
  exact no_deleting_linear U.toLinearEquiv.toLinearMap blank hblank hU

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

