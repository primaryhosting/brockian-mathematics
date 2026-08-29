import Mathlib

/-!
# Rank Trace Ineq
Category: Zeta-23 §3 Linear Algebra (re-derivation)
Target: Zeta23Redux.LinAlg.rank_trace_ineq
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

set_option relaxedAutoImplicit false
set_option autoImplicit false

set_option grind.warning false

namespace Zeta23Redux.LinAlg

open Matrix
open scoped ComplexOrder

variable {d : ℕ}

/-! ## Basic real-valued trace functionals -/

/-- The real part of the trace. -/

lemma hermitian_decomp {A : Matrix (Fin d) (Fin d) ℂ} (hA : A.IsHermitian) :
    ∃ U : Matrix (Fin d) (Fin d) ℂ, Uᴴ * U = 1 ∧ U * Uᴴ = 1 ∧
      A = U * (Matrix.diagonal (fun i => (hA.eigenvalues i : ℂ))) * Uᴴ := by
  refine ⟨(hA.eigenvectorUnitary : Matrix (Fin d) (Fin d) ℂ),
    Matrix.mem_unitaryGroup_iff'.mp hA.eigenvectorUnitary.2,
    Matrix.mem_unitaryGroup_iff.mp hA.eigenvectorUnitary.2, ?_⟩
  conv_lhs => rw [hA.spectral_theorem]
  simp [Unitary.conjStarAlgAut_apply, Function.comp_def, Matrix.star_eq_conjTranspose]

/-! ## Positive semidefinite auxiliaries -/

