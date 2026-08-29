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

lemma ramseySet_mem (c : ℕ → ℕ → Bool) : ∀ n, ramseySet c n ∈ ramseyUF := by
  intro n
  induction n with
  | zero =>
      rw [ramseySet]
      simpa using Filter.univ_mem
  | succ n ih =>
      rw [ramseySet_succ, ramseyStep]
      exact Filter.inter_mem (Filter.inter_mem ih (Ioi_mem_ramseyUF _)) (ufColor_mem c _)

