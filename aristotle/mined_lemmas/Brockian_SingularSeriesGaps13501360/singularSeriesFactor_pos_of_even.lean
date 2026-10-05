/-
# Singular Series Gaps 13501360
Category: Brockian Corpus
Target: Brockian.SingularSeriesGaps13501360
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

namespace Brockian

open Finset

/-- A finite set of integers is *admissible* if, for every prime `p`, it fails to cover
all residue classes modulo `p`.  This is exactly the condition under which the
Hardy–Littlewood singular series of the tuple is nonzero. -/

theorem singularSeriesFactor_pos_of_even {d : ℤ} (hev : Even d) (hd : d ≠ 0) :
    0 < singularSeriesFactor d := by
  rw [singularSeriesFactor, if_pos ⟨hev, hd⟩]
  refine Finset.prod_pos ?_
  intro p hp
  have hp2 : p ≠ 2 := (Finset.mem_erase.mp hp).1
  have hpp : p.Prime := Nat.prime_of_mem_primeFactors (Finset.mem_erase.mp hp).2
  have h3 : 3 ≤ p := by
    rcases hpp.two_le.lt_or_eq with h | h
    · omega
    · omega
  have h1 : (0 : ℝ) < (p : ℝ) - 1 := by
    have : (3 : ℝ) ≤ (p : ℝ) := by exact_mod_cast h3
    linarith
  have h2 : (0 : ℝ) < (p : ℝ) - 2 := by
    have : (3 : ℝ) ≤ (p : ℝ) := by exact_mod_cast h3
    linarith
  positivity

/-- The singular series factor vanishes at inadmissible gaps. -/
