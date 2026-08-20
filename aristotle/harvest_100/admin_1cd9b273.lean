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

import Mathlib

/-!
# Spectral Theorem Finite
Category: Quantum Physics
Target: QPhys.spectral_theorem_finite
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace QPhys

open Matrix

/-- If `U` is unitary and `A = U * D * star U`, then `star U * A * U = D`. -/
private lemma conj_of_eq {n : Type*} [Fintype n] [DecidableEq n]
    {A U D : Matrix n n ℂ} (hU : star U * U = 1)
    (h : A = U * D * star U) : star U * A * U = D := by
  subst h
  simp only [← mul_assoc, hU, one_mul]
  simp [mul_assoc, hU]

/-- **Spectral theorem (finite dimensional).**
Every Hermitian matrix `A` over `ℂ` is unitarily diagonalizable with real eigenvalues:
there exist a unitary matrix `U` (i.e. `star U * U = 1` and `U * star U = 1`) and a real
vector of eigenvalues `d` such that `A = U * diagonal d * star U`, equivalently
`star U * A * U = diagonal d`.

This repackages Mathlib's `Matrix.IsHermitian.spectral_theorem`. -/
theorem spectral_theorem_finite {n : Type*} [Fintype n] [DecidableEq n]
    (A : Matrix n n ℂ) (hA : A.IsHermitian) :
    ∃ (U : Matrix n n ℂ) (d : n → ℝ),
      star U * U = 1 ∧ U * star U = 1 ∧
      A = U * Matrix.diagonal (fun i => (d i : ℂ)) * star U ∧
      star U * A * U = Matrix.diagonal (fun i => (d i : ℂ)) := by
  classical
  set U : Matrix n n ℂ := (hA.eigenvectorUnitary : Matrix n n ℂ) with hUdef
  have hU : star U * U = 1 := Unitary.star_mul_self_of_mem hA.eigenvectorUnitary.2
  have hU' : U * star U = 1 := Unitary.mul_star_self_of_mem hA.eigenvectorUnitary.2
  have hAeq : A = U * Matrix.diagonal (fun i => ((hA.eigenvalues i : ℝ) : ℂ)) * star U := by
    have h := hA.spectral_theorem
    rw [Unitary.conjStarAlgAut_apply] at h
    simpa [hUdef, Function.comp_def] using h
  exact ⟨U, hA.eigenvalues, hU, hU', hAeq, conj_of_eq hU hAeq⟩

end QPhys

