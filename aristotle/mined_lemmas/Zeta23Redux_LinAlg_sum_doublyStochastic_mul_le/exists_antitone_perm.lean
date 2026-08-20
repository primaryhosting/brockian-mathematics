import Mathlib

/-!
# Von Neumann Trace Ineq
Category: Zeta-23 §3 Linear Algebra (re-derivation)
Target: Zeta23Redux.LinAlg.vonNeumann_trace_ineq
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open scoped BigOperators
open Matrix

namespace Zeta23Redux.LinAlg

variable {d : ℕ}

/-- A bilinear form against a doubly stochastic matrix is bounded by the "sorted" pairing,
when both weight vectors are listed in the same (decreasing) order.

This is the Birkhoff + rearrangement step of von Neumann's trace inequality. -/

theorem exists_antitone_perm (f : Fin d → ℝ) : ∃ σ : Equiv.Perm (Fin d), Antitone (f ∘ σ) := by
  refine ⟨Tuple.sort fun i => -f i, fun i j hij => ?_⟩
  simpa using Tuple.monotone_sort (fun i => -f i) hij

/-- Von Neumann's trace inequality, stated with the decreasing rearrangements of the eigenvalues
produced explicitly. -/
