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

lemma ramseySeq_color (c : ℕ → ℕ → Bool) {m n : ℕ} (h : m < n) :
    c (ramseySeq c m) (ramseySeq c n) = ufColor c (ramseySeq c m) := by
  have hmem : ramseySeq c n ∈ ramseySet c (m + 1) :=
    ramseySet_antitone c h (ramseySeq_mem c n)
  rw [ramseySet_succ, ramseyStep] at hmem
  exact hmem.2

