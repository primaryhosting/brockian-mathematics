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
