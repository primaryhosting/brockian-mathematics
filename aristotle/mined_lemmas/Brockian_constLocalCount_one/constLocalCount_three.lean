import Mathlib

/-!
# Constellation Local Count K 3
Category: Brockian Corpus
Target: Brockian.ConstellationLocalCountK3
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open scoped BigOperators
open scoped Real
open scoped Nat
open scoped Pointwise

set_option maxHeartbeats 8000000
set_option maxRecDepth 4000
set_option synthInstance.maxHeartbeats 20000
set_option synthInstance.maxSize 128

set_option relaxedAutoImplicit false
set_option autoImplicit false

set_option grind.warning false

namespace Brockian

/-- The *local constellation count* of the shift pattern (constellation) `h : Fin k → ℤ`
relative to a set `S` of integers, counted over the window `I`:
the number of `x ∈ I` such that all the shifted points `x + h i` lie in `S`. -/

theorem constLocalCount_three (S I : Finset ℤ) (h0 h1 h2 : ℤ) :
    constLocalCount S I ![h0, h1, h2] =
      (I.filter (fun x => x + h0 ∈ S ∧ x + h1 ∈ S ∧ x + h2 ∈ S)).card := by
  unfold constLocalCount
  congr 1
  apply Finset.filter_congr
  intro x _
  constructor
  · intro hx
    exact ⟨hx 0, hx 1, hx 2⟩
  · intro hx i
    fin_cases i
    · exact hx.1
    · exact hx.2.1
    · exact hx.2.2

/-- Bonferroni step: intersecting with one more condition loses at most the number of
elements of the window failing that condition. -/
