/-
/-!
# Infinite Ramsey
Category: Frontier — Set Theory
Target: Frontier.infinite_ramsey
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/
-/
import Mathlib

namespace Frontier

open Filter Set

/-- A fixed nonprincipal ultrafilter on `ℕ`: an ultrafilter refining the cofinite filter. -/

lemma ramseySet_succ (c : ℕ → ℕ → Bool) (n : ℕ) :
    ramseySet c (n + 1) = ramseyStep c (ramseySet c n) := by
  simp [ramseySet, Function.iterate_succ_apply']

