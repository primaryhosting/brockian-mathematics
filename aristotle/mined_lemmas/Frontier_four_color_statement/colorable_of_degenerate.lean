import Mathlib
-- (Lean 4 requires `import` lines to precede any module docstring, so the requested
-- header comment appears immediately below the import.)

/-!
# Four Color Statement
Category: Frontier — Moonshot
Target: Frontier.four_color_statement
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

set_option grind.warning false

namespace Frontier

open SimpleGraph

/-! ## Planarity

We use the *straight-line* notion of planarity: a graph is planar when its vertices can be
placed at distinct points of the plane `ℝ × ℝ` in such a way that the closed segments
representing the edges meet only in common endpoints, and no vertex lies on a segment
representing an edge that is not incident to it.

By Fáry's theorem this is equivalent, for finite simple graphs, to the usual topological
notion of planarity (embeddability of the graph into the plane with arbitrary arcs as edges).
-/

/-- A straight-line planar drawing of `G`: an injective placement `p` of the vertices in the
plane such that (i) a vertex lying on the segment of an edge is an endpoint of that edge, and
(ii) the segments of two distinct edges meet only in common endpoints. -/

theorem colorable_of_degenerate {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V)
    [DecidableRel G.Adj] (n : ℕ)
    (h : ∀ s : Finset V, s.Nonempty → ∃ v ∈ s, (s.filter (fun w => G.Adj v w)).card < n) :
    G.Colorable n := by
  have key : ∀ s : Finset V, ∃ f : V → ℕ, (∀ v ∈ s, f v < n) ∧
      ∀ a ∈ s, ∀ b ∈ s, G.Adj a b → f a ≠ f b := by
    intro s
    induction s using Finset.strongInduction with
    | _ s ih =>
      rcases s.eq_empty_or_nonempty with rfl | hs
      · exact ⟨fun _ => 0, by simp, by simp⟩
      obtain ⟨v, hv, hvcard⟩ := h s hs
      obtain ⟨f, hfb, hfp⟩ := ih (s.erase v) (Finset.erase_ssubset hv)
      set N : Finset V := s.filter (fun w => G.Adj v w) with hN
      have hlt : (N.image f).card < n := lt_of_le_of_lt (Finset.card_image_le) hvcard
      have hex : ∃ c ∈ Finset.range n, c ∉ N.image f := by
        by_contra hcon
        push_neg at hcon
        have : (Finset.range n).card ≤ (N.image f).card :=
          Finset.card_le_card (fun x hx => hcon x hx)
        simp only [Finset.card_range] at this
        omega
      obtain ⟨c, hcn, hcnot⟩ := hex
      rw [Finset.mem_range] at hcn
      refine ⟨Function.update f v c, ?_, ?_⟩
      · intro x hx
        by_cases hxv : x = v
        · subst hxv
          rw [Function.update_self]
          exact hcn
        · rw [Function.update_of_ne hxv]
          exact hfb x (Finset.mem_erase.2 ⟨hxv, hx⟩)
      · intro a ha b hb hab
        have hne : a ≠ b := hab.ne
        by_cases hav : a = v
        · subst hav
          have hbv : b ≠ a := hne.symm
          rw [Function.update_of_ne hbv, Function.update_self]
          intro hcontra
          exact hcnot (Finset.mem_image.2 ⟨b, Finset.mem_filter.2 ⟨hb, hab⟩, hcontra.symm⟩)
        · by_cases hbv : b = v
          · subst hbv
            rw [Function.update_of_ne hav, Function.update_self]
            intro hcontra
            exact hcnot (Finset.mem_image.2 ⟨a, Finset.mem_filter.2 ⟨ha, hab.symm⟩, hcontra⟩)
          · rw [Function.update_of_ne hav, Function.update_of_ne hbv]
            exact hfp a (Finset.mem_erase.2 ⟨hav, ha⟩) b (Finset.mem_erase.2 ⟨hbv, hb⟩) hab
  obtain ⟨f, hfb, hfp⟩ := key Finset.univ
  rw [SimpleGraph.colorable_iff_exists_bdd_nat_coloring]
  exact ⟨SimpleGraph.Coloring.mk f fun {a b} hab =>
    hfp a (Finset.mem_univ a) b (Finset.mem_univ b) hab, fun v => hfb v (Finset.mem_univ v)⟩

/-- Base case: any graph on at most four vertices is 4-colourable, in particular any such
planar graph. -/
