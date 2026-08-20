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

theorem card_filter_and_ge (I : Finset ℤ) (p q : ℤ → Prop)
    [DecidablePred p] [DecidablePred q] :
    (I.filter p).card + (I.filter q).card ≤
      (I.filter (fun x => p x ∧ q x)).card + I.card := by
  classical
  have hinter : I.filter p ∩ I.filter q = I.filter (fun x => p x ∧ q x) := by
    ext x; simp [and_assoc, and_left_comm, and_comm]
  have hunion : (I.filter p ∪ I.filter q) ⊆ I := by
    intro x hx
    rcases Finset.mem_union.mp hx with hx | hx <;> exact Finset.mem_filter.mp hx |>.1
  have hkey := Finset.card_inter_add_card_union (I.filter p) (I.filter q)
  have hle : (I.filter p ∪ I.filter q).card ≤ I.card := Finset.card_le_card hunion
  rw [hinter] at hkey
  omega

/-- Monotonicity: adding a point to the constellation can only decrease the local count. -/
