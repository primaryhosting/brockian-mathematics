import Mathlib

/-!
# Five Color Theorem
Category: Frontier — Fields Medal Work
Target: Frontier.five_color_theorem
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open scoped BigOperators
open scoped Real
open scoped Nat
open scoped Classical
open scoped Pointwise

set_option maxHeartbeats 1000000
set_option relaxedAutoImplicit false
set_option autoImplicit false

namespace Frontier

variable {V : Type*} [DecidableEq V]

/-- The neighbours of `v` inside the vertex set `s`. -/

def contract (G : SimpleGraph V) (u w : V) : SimpleGraph V where
  Adj a b := a ≠ b ∧ (G.Adj a b ∨ (a = u ∧ G.Adj w b) ∨ (b = u ∧ G.Adj w a))
  symm := by
    rintro a b ⟨hne, h⟩
    refine ⟨hne.symm, ?_⟩
    rcases h with h | ⟨h1, h2⟩ | ⟨h1, h2⟩
    · exact Or.inl h.symm
    · exact Or.inr (Or.inr ⟨h1, h2⟩)
    · exact Or.inr (Or.inl ⟨h1, h2⟩)
  loopless := by constructor; rintro a ⟨hne, -⟩; exact hne rfl

/-- The reduction relation: `Reduces s G t H` says that the graph `H` on the vertex set `t`
can be obtained from the graph `G` on the vertex set `s` by repeatedly deleting a vertex, or
contracting a degree-`≤ 5` vertex `v` into two of its non-adjacent neighbours `u`, `w`.
Both operations preserve planarity. -/
inductive Reduces : Finset V → SimpleGraph V → Finset V → SimpleGraph V → Prop
  | refl (s : Finset V) (G : SimpleGraph V) : Reduces s G s G
  | del {s : Finset V} {G : SimpleGraph V} {t : Finset V} {H : SimpleGraph V} (v : V) :
      Reduces (s.erase v) G t H → Reduces s G t H
  | con {s : Finset V} {G : SimpleGraph V} {t : Finset V} {H : SimpleGraph V} (v u w : V)
      (hu : u ∈ nbrs s G v) (hw : w ∈ nbrs s G v) (huw : u ≠ w) (hnadj : ¬ G.Adj u w) :
      Reduces ((s.erase v).erase w) (contract G u w) t H → Reduces s G t H

/-- The local degree condition that Euler's formula (together with the non-planarity of `K₅`)
provides for a planar graph: there is a vertex of degree at most `4`, or a vertex of degree at
most `5` two of whose neighbours are non-adjacent. -/
