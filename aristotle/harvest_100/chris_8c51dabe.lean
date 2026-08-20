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
private theorem mono_triangle_of_bools :
    ∀ e01 e02 e03 e04 e05 e12 e13 e14 e15 e23 e24 e25 e34 e35 e45 : Bool,
    (e01 = e12 ∧ e12 = e02) ∨
    (e01 = e13 ∧ e13 = e03) ∨
    (e01 = e14 ∧ e14 = e04) ∨
    (e01 = e15 ∧ e15 = e05) ∨
    (e02 = e23 ∧ e23 = e03) ∨
    (e02 = e24 ∧ e24 = e04) ∨
    (e02 = e25 ∧ e25 = e05) ∨
    (e03 = e34 ∧ e34 = e04) ∨
    (e03 = e35 ∧ e35 = e05) ∨
    (e04 = e45 ∧ e45 = e05) ∨
    (e12 = e23 ∧ e23 = e13) ∨
    (e12 = e24 ∧ e24 = e14) ∨
    (e12 = e25 ∧ e25 = e15) ∨
    (e13 = e34 ∧ e34 = e14) ∨
    (e13 = e35 ∧ e35 = e15) ∨
    (e14 = e45 ∧ e45 = e15) ∨
    (e23 = e34 ∧ e34 = e24) ∨
    (e23 = e35 ∧ e35 = e25) ∨
    (e24 = e45 ∧ e45 = e25) ∨
    (e34 = e45 ∧ e45 = e35) := by decide

/-- The 5-cycle colouring of the edges of `K₅`: `i` and `j` get colour `true`
exactly when they are consecutive modulo `5`. -/
private def pentagon (i j : Fin 5) : Bool := (i + 1 == j) || (j + 1 == i)

/--
**R(3,3) = 6.**

* Every 2-colouring `C` of the edges of `K₆` (a symmetric `Bool`-valued function
  on `Fin 6`) admits three distinct vertices `a, b, c` whose three connecting
  edges all have the same colour.
* There is a 2-colouring of the edges of `K₅` (the 5-cycle colouring) with no
  monochromatic triangle.
-/
theorem ramsey_3_3 :
    (∀ C : Fin 6 → Fin 6 → Bool, (∀ i j : Fin 6, C i j = C j i) →
        ∃ a b c : Fin 6, a ≠ b ∧ a ≠ c ∧ b ≠ c ∧ C a b = C b c ∧ C b c = C a c) ∧
    (∃ C : Fin 5 → Fin 5 → Bool, (∀ i j : Fin 5, C i j = C j i) ∧
        ∀ a b c : Fin 5, a ≠ b → a ≠ c → b ≠ c →
          ¬(C a b = C b c ∧ C b c = C a c)) := by
  constructor
  · intro C _hsymm
    have h := mono_triangle_of_bools (C 0 1) (C 0 2) (C 0 3) (C 0 4) (C 0 5)
      (C 1 2) (C 1 3) (C 1 4) (C 1 5) (C 2 3) (C 2 4) (C 2 5) (C 3 4) (C 3 5) (C 4 5)
    rcases h with h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h
    · exact ⟨0, 1, 2, by decide, by decide, by decide, h.1, h.2⟩
    · exact ⟨0, 1, 3, by decide, by decide, by decide, h.1, h.2⟩
    · exact ⟨0, 1, 4, by decide, by decide, by decide, h.1, h.2⟩
    · exact ⟨0, 1, 5, by decide, by decide, by decide, h.1, h.2⟩
    · exact ⟨0, 2, 3, by decide, by decide, by decide, h.1, h.2⟩
    · exact ⟨0, 2, 4, by decide, by decide, by decide, h.1, h.2⟩
    · exact ⟨0, 2, 5, by decide, by decide, by decide, h.1, h.2⟩
    · exact ⟨0, 3, 4, by decide, by decide, by decide, h.1, h.2⟩
    · exact ⟨0, 3, 5, by decide, by decide, by decide, h.1, h.2⟩
    · exact ⟨0, 4, 5, by decide, by decide, by decide, h.1, h.2⟩
    · exact ⟨1, 2, 3, by decide, by decide, by decide, h.1, h.2⟩
    · exact ⟨1, 2, 4, by decide, by decide, by decide, h.1, h.2⟩
    · exact ⟨1, 2, 5, by decide, by decide, by decide, h.1, h.2⟩
    · exact ⟨1, 3, 4, by decide, by decide, by decide, h.1, h.2⟩
    · exact ⟨1, 3, 5, by decide, by decide, by decide, h.1, h.2⟩
    · exact ⟨1, 4, 5, by decide, by decide, by decide, h.1, h.2⟩
    · exact ⟨2, 3, 4, by decide, by decide, by decide, h.1, h.2⟩
    · exact ⟨2, 3, 5, by decide, by decide, by decide, h.1, h.2⟩
    · exact ⟨2, 4, 5, by decide, by decide, by decide, h.1, h.2⟩
    · exact ⟨3, 4, 5, by decide, by decide, by decide, h.1, h.2⟩
  · exact ⟨pentagon, by decide, by decide⟩

/-- The 5-cycle as a `SimpleGraph` on `Fin 5`. -/
def cycleGraph5 : SimpleGraph (Fin 5) where
  Adj i j := pentagon i j = true
  symm := by
    intro a b h
    simpa [pentagon, Bool.or_comm] using h
  loopless := ⟨by decide⟩

instance : DecidableRel cycleGraph5.Adj := fun i j => by
  unfold cycleGraph5; infer_instance

/--
**R(3,3) = 6, graph-theoretic form.**

For every simple graph `G` on six vertices, either `G` or its complement
contains a triangle; and there is a graph on five vertices (the 5-cycle) such
that neither it nor its complement contains a triangle.
-/
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

