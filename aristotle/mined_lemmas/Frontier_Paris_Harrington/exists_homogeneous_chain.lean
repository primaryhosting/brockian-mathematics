import Mathlib

/-!
# Paris Harrington
Category: Frontier — Set Theory
Target: Frontier.Paris_Harrington
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open scoped BigOperators
open scoped Real
open scoped Nat
open scoped Classical
open scoped Pointwise

set_option maxHeartbeats 8000000
set_option maxRecDepth 4000
set_option synthInstance.maxHeartbeats 20000
set_option synthInstance.maxSize 128

set_option relaxedAutoImplicit false
set_option autoImplicit false

set_option pp.fullNames true
set_option pp.structureInstances true
set_option pp.coercions.types true
set_option pp.funBinderTypes true
set_option pp.letVarTypes true
set_option pp.piBinderTypes true

set_option grind.warning false

namespace Frontier

/-- A finite set `Y` of positive integers is *relatively large* when its least element is at
most its cardinality. -/

theorem exists_homogeneous_chain {k : ℕ} (n : ℕ) (c : Finset ℕ → Fin k) :
    ∃ (B : ℕ → Finset ℕ) (i : Fin k),
      (∀ t t' : ℕ, t ≤ t' → B t ⊆ B t') ∧ (∀ t, (B t).card = t) ∧
        (∀ t, ∀ y ∈ B t, 0 < y) ∧ (∀ t, Homogeneous n c (B t) i) := by
  refine ⟨chain n c, G c n ∅, fun t t' h => chain_mono n c h, chain_card n c,
    chain_pos n c, fun t => ?_⟩
  intro s hs hcard
  exact chain_homogeneous n c t s hs hcard

/-- **Paris–Harrington strengthened finite Ramsey theorem.**

For all `n`, `k`, `m` there is `N` such that for every colouring `c` of the finite subsets of
`{1, …, N}` with `k` colours, there is a set `Y ⊆ {1, …, N}` with at least `m` elements which is
*relatively large* (its least element is at most its cardinality) and homogeneous for `c` on
`n`-element subsets.

This is the mathematical ("true") half of the Paris–Harrington theorem; the proof below is the
ultrafilter proof of the infinite Ramsey theorem combined with an ultrafilter compactness
argument.  The metamathematical half (unprovability in first-order Peano arithmetic) is a
statement about PA-derivability and is not formalised here. -/
