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

theorem constLocalCount_three_le_two (S I : Finset ℤ) (h0 h1 h2 : ℤ) :
    constLocalCount S I ![h0, h1, h2] ≤ constLocalCount S I ![h0, h1] := by
  rw [constLocalCount_three, constLocalCount_two]
  apply Finset.card_le_card
  intro x hx
  simp only [Finset.mem_filter] at hx ⊢
  exact ⟨hx.1, hx.2.1, hx.2.2.1⟩

/--
**Constellation local count, `k = 3`.**

For a set `S ⊆ ℤ`, a window `I ⊆ ℤ` and a three-point constellation `(h₀, h₁, h₂)`:

1. the local count is exactly the number of `x ∈ I` with `x + h₀, x + h₁, x + h₂ ∈ S`;
2. it is bounded above by the corresponding two-point (and hence one-point) local counts;
3. (Bonferroni / union bound) it is bounded below by the sum of the three one-point
   local counts minus twice the size of the window.
-/
