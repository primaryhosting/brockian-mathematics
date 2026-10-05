/-!
# Erdos Discrepancy
Category: Frontier — Prime Numbers
Target: Frontier.erdos_discrepancy
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

/-
This file is written in plain Lean 4 core (no imports), so that the header comment above
can legally be the very first thing in the file.
-/

namespace Frontier

/-- A `±1` sequence: `f n ∈ {1, -1}` for every index `n ≥ 1`. -/

theorem continuous_hapSum_boolSeq (d n : ℕ) :
    Continuous fun g : ℕ → Bool => hapSum (boolSeq g) d n := by
  induction n with
  | zero => simpa [hapSum] using continuous_const
  | succ n ih =>
      have hcoord : Continuous fun g : ℕ → Bool => boolSeq g ((n + 1) * d) := by
        exact (continuous_of_discreteTopology (f := fun b : Bool => if b then (1 : ℤ) else -1)).comp
          (continuous_apply ((n + 1) * d))
      simpa [hapSum] using ih.add hcoord

/-- **Compactness reduction.**  The Erdős discrepancy statement is equivalent to its
finitary form: unbounded discrepancy for all infinite `±1` sequences is the same as, for
each `C`, a uniform finite length `N` in which discrepancy `> C` must occur. -/
