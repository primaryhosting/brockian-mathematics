/-
# Ramsey 3 3
Category: Pure Mathematics
Target: Math.ramsey_3_3
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

set_option pp.fullNames true
set_option pp.structureInstances true
set_option pp.coercions.types true
set_option pp.funBinderTypes true
set_option pp.letVarTypes true
set_option pp.piBinderTypes true

set_option grind.warning false

namespace Math

set_option synthInstance.maxSize 1000000 in
set_option synthInstance.maxHeartbeats 4000000 in
set_option maxRecDepth 1000000 in
/-- Exhaustive check over the `2 ^ 15` two-colorings of the edges of `K₆`
(the edge between `i < j` is coloured `eij`): some triple `i < j < k` is
monochromatic. -/

theorem ramsey_3_3_graph :
    (∀ G : SimpleGraph (Fin 6), ∃ a b c : Fin 6,
        (G.Adj a b ∧ G.Adj b c ∧ G.Adj a c) ∨
          (Gᶜ.Adj a b ∧ Gᶜ.Adj b c ∧ Gᶜ.Adj a c)) ∧
    (∃ G : SimpleGraph (Fin 5), ∀ a b c : Fin 5,
        ¬((G.Adj a b ∧ G.Adj b c ∧ G.Adj a c) ∨
          (Gᶜ.Adj a b ∧ Gᶜ.Adj b c ∧ Gᶜ.Adj a c))) := by
  refine ⟨?_, ⟨cycleGraph5, by decide⟩⟩
  intro G
  obtain ⟨a, b, c, hab, hac, hbc, h1, h2⟩ :=
    ramsey_3_3.1 (fun i j => decide (G.Adj i j)) (by
      intro i j
      simp [G.adj_comm])
  have e1 : G.Adj a b ↔ G.Adj b c := decide_eq_decide.mp h1
  have e2 : G.Adj b c ↔ G.Adj a c := decide_eq_decide.mp h2
  refine ⟨a, b, c, ?_⟩
  by_cases h : G.Adj a b
  · exact Or.inl ⟨h, e1.mp h, e2.mp (e1.mp h)⟩
  · refine Or.inr ?_
    simp only [SimpleGraph.compl_adj]
    exact ⟨⟨hab, h⟩, ⟨hbc, fun hh => h (e1.mpr hh)⟩,
      ⟨hac, fun hh => h (e1.mpr (e2.mpr hh))⟩⟩

end Math

