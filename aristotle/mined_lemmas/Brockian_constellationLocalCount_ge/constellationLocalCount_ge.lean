/-
# Constellation Local Count K 3
Category: Brockian Corpus
Target: Brockian.ConstellationLocalCountK3
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

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

set_option grind.warning false

namespace Brockian

/-- The *local constellation set* of a finite set `A ⊆ ℤ` with respect to a `k`-tuple of
displacements `d : Fin k → ℤ`: the set of base points `x ∈ A` such that the whole
constellation `x + d 0, …, x + d (k-1)` is contained in `A`. -/

theorem constellationLocalCount_ge (k : ℕ) (A : Finset ℤ) (d : Fin k → ℤ) :
    A.card ≤ constellationLocalCount k A d + ∑ i, constellationDefect A (d i) := by
  classical
  have hsplit :
      (A.filter (fun x => ∀ i, x + d i ∈ A)).card
        + (A.filter (fun x => ¬ ∀ i, x + d i ∈ A)).card = A.card :=
    Finset.card_filter_add_card_filter_not _
  have hsub :
      A.filter (fun x => ¬ ∀ i, x + d i ∈ A)
        ⊆ (Finset.univ : Finset (Fin k)).biUnion
            (fun i => A.filter (fun x => x + d i ∉ A)) := by
    intro x hx
    simp only [Finset.mem_filter, not_forall] at hx
    obtain ⟨hxA, i, hi⟩ := hx
    exact Finset.mem_biUnion.mpr ⟨i, Finset.mem_univ i, Finset.mem_filter.mpr ⟨hxA, hi⟩⟩
  have hcard :
      (A.filter (fun x => ¬ ∀ i, x + d i ∈ A)).card
        ≤ ∑ i, (A.filter (fun x => x + d i ∉ A)).card :=
    le_trans (Finset.card_le_card hsub) (Finset.card_biUnion_le)
  unfold constellationLocalCount constellationLocalSet constellationDefect
  omega

/-- **Constellation local count, `k = 3`.**  For a finite set `A ⊆ ℤ` and a triple of
displacements `d : Fin 3 → ℤ`, the number of `x ∈ A` whose full three-point constellation
`x + d 0, x + d 1, x + d 2` lies in `A` is at least `|A|` minus the three individual
translation defects. -/
