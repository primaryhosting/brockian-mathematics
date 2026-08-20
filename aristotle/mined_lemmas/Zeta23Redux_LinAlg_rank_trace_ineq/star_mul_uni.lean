import Mathlib

/-!
# Rank Trace Ineq
Category: Zeta-23 §3 Linear Algebra (re-derivation)
Target: Zeta23Redux.LinAlg.rank_trace_ineq
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open scoped BigOperators ComplexOrder

namespace Zeta23Redux.LinAlg

open Matrix

variable {d : ℕ}

/-- The real part of the trace of a matrix. -/

lemma star_mul_uni (hA : A.IsHermitian) :
    (hA.eigenvectorUnitary : Matrix (Fin d) (Fin d) ℂ)ᴴ *
      (hA.eigenvectorUnitary : Matrix (Fin d) (Fin d) ℂ) = 1 := by
  have := Unitary.coe_star_mul_self hA.eigenvectorUnitary
  rwa [Matrix.star_eq_conjTranspose] at this

