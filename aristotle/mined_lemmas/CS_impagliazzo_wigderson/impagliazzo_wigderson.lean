/-
# Impagliazzo Wigderson
Category: Frontier Cs
Target: CS.impagliazzo_wigderson
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Impagliazzo Wigderson
Category: Frontier Cs
Target: CS.impagliazzo_wigderson
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open scoped BigOperators
open Finset

namespace CS

/-! ## Boolean strings, probabilities and majority votes -/

/-- Boolean strings of length `n`. -/
abbrev Bits (n : ℕ) := Fin n → Bool

/-- The probability that the test `T` accepts a uniformly random string of length `k`. -/

theorem impagliazzo_wigderson (M : Model) (hIW : HardnessToRandomness M)
    (hLB : StrongCircuitLowerBound M) : M.P = M.BPP := by
  apply Set.eq_of_subset_of_subset
  · intro L hL
    exact M.det_mem_rand L hL
  · rintro L ⟨A, hA, hdec⟩
    obtain ⟨G, hG⟩ := hIW hLB A hA
    have h := M.derandomize_poly A G hA hG
    rw [derandomize_eq A G L hdec] at h
    exact h

/-! ## Non-vacuity: the axioms of `Model` and `HardnessToRandomness` are satisfiable -/

/-- A degenerate model in which every language is "polynomial time" and the randomized
algorithms considered are those using at most logarithmically many coins.  It witnesses
that the hypotheses of `impagliazzo_wigderson` (apart from the conjectural circuit lower
bound) are consistent. -/
