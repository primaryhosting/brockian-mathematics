/-
# Von Neumann Trace Ineq
Category: Zeta-23 §3 Linear Algebra (re-derivation)
Target: Zeta23Redux.LinAlg.vonNeumann_trace_ineq
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/
import Mathlib

open scoped BigOperators
open Matrix Finset

namespace Zeta23Redux.LinAlg

variable {d : ℕ}

/-- The entrywise squared modulus of a unitary matrix is doubly stochastic. -/

lemma exists_antitone_rearrangement (f : Fin d → ℝ) :
    ∃ mu : Fin d → ℝ, Antitone mu ∧ ∃ σ : Equiv.Perm (Fin d), mu = f ∘ σ := by
  refine ⟨f ∘ Tuple.sort f ∘ Fin.rev, ?_, (Fin.revPerm).trans (Tuple.sort f), rfl⟩
  intro i j hij
  exact Tuple.monotone_sort f (Fin.rev_le_rev.mpr hij)

/-- Von Neumann's trace inequality, stated with the explicit decreasing rearrangements of the
eigenvalues of `A` and `B`. -/
