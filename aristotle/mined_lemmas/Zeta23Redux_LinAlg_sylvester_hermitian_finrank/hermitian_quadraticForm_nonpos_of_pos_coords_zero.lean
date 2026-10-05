/-
# Sylvester Hermitian Finrank
Category: Zeta-23 §3 Linear Algebra (re-derivation)
Target: Zeta23Redux.LinAlg.sylvester_hermitian_finrank
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Sylvester Hermitian Finrank
Category: Zeta-23 §3 Linear Algebra (re-derivation)
Target: Zeta23Redux.LinAlg.sylvester_hermitian_finrank
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open scoped BigOperators
open scoped Real
open scoped Nat
open scoped Classical
open scoped Pointwise

open Matrix

set_option maxHeartbeats 8000000
set_option maxRecDepth 4000
set_option synthInstance.maxHeartbeats 20000
set_option synthInstance.maxSize 128

set_option relaxedAutoImplicit false
set_option autoImplicit false

namespace Zeta23Redux.LinAlg

/-- The positive index of inertia of a Hermitian matrix `A`: the number of indices `i` at which
the eigenvalue `hA.eigenvalues i` is strictly positive (i.e. the number of strictly positive
eigenvalues of `A`, counted with multiplicity). -/

theorem hermitian_quadraticForm_nonpos_of_pos_coords_zero {d : ℕ}
    {A : Matrix (Fin d) (Fin d) ℂ} (hA : A.IsHermitian) (x : Fin d → ℂ)
    (hx : ∀ i : Fin d, 0 < hA.eigenvalues i →
      ((star (hA.eigenvectorUnitary : Matrix (Fin d) (Fin d) ℂ)) *ᵥ x) i = 0) :
    (star x ⬝ᵥ (A *ᵥ x)).re ≤ 0 := by
  rw [hermitian_quadraticForm_eq_sum hA x]
  refine Finset.sum_nonpos fun i _ => ?_
  rcases lt_or_ge 0 (hA.eigenvalues i) with h | h
  · simp [hx i h]
  · exact mul_nonpos_of_nonpos_of_nonneg h (Complex.normSq_nonneg _)

/-- **Sylvester's law of inertia** (Hermitian case, the inequality used in the paper).
If `A` is a Hermitian complex matrix and `W` is a complex subspace of `Fin d → ℂ` on which the
Hermitian form `x ↦ Re (star x ⬝ᵥ A *ᵥ x)` is positive definite, then `finrank W ≤ posIndex A`,
i.e. pulling back the form to `W` cannot increase the positive index of inertia. -/
