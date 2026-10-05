import Mathlib

/-!
# Weyl Pos Index Above
Category: Zeta-23 §3 Linear Algebra (re-derivation)
Target: Zeta23Redux.LinAlg.weyl_posIndexAbove
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

namespace Zeta23Redux.LinAlg

open Matrix Finset

variable {d : ℕ}

/-- The Rayleigh quadratic form of a matrix `M` at a vector `x` of Euclidean space:
`Re ⟪x, M x⟫`. -/

lemma finrank_span_eigen {M : Matrix (Fin d) (Fin d) ℂ} (hM : M.IsHermitian)
    (s : Finset (Fin d)) :
    Module.finrank ℂ
        (Submodule.span ℂ (Set.range fun j : (s : Set (Fin d)) => hM.eigenvectorBasis j))
      = s.card := by
  have hli : LinearIndependent ℂ fun j : (s : Set (Fin d)) => hM.eigenvectorBasis (j : Fin d) :=
    (hM.eigenvectorBasis.toBasis.linearIndependent).comp _ Subtype.val_injective
  rw [finrank_span_eq_card hli]
  simp

/-- **Weyl monotonicity**: if every eigenvalue of the Hermitian perturbation `E` has absolute
value at most `θ`, then the number of eigenvalues of `A + E` strictly above `θ` is at most the
number of strictly positive eigenvalues of `A`. -/
