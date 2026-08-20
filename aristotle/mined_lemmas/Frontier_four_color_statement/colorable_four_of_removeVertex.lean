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

theorem colorable_four_of_removeVertex {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (v : V) (hdeg : G.degree v ≤ 3)
    (h : (G.induce {w : V | w ≠ v}).Colorable 4) : G.Colorable 4 := by
  classical
  obtain ⟨C⟩ := h
  set T : Finset (Fin 4) :=
    (G.neighborFinset v).image (fun w => if hw : w ≠ v then C ⟨w, hw⟩ else 0) with hT
  have hTcard : T.card < 4 := by
    have h1 : T.card ≤ (G.neighborFinset v).card := Finset.card_image_le
    rw [SimpleGraph.card_neighborFinset_eq_degree] at h1
    omega
  have hex : ∃ c : Fin 4, c ∉ T := by
    by_contra hcon
    push_neg at hcon
    have : (Finset.univ : Finset (Fin 4)).card ≤ T.card :=
      Finset.card_le_card (fun x _ => hcon x)
    simp only [Finset.card_univ, Fintype.card_fin] at this
    omega
  obtain ⟨c, hc⟩ := hex
  refine ⟨SimpleGraph.Coloring.mk (fun w => if hw : w ≠ v then C ⟨w, hw⟩ else c) ?_⟩
  intro a b hab
  have hmemT : ∀ w : V, G.Adj v w → (if hw : w ≠ v then C ⟨w, hw⟩ else (0 : Fin 4)) ∈ T := by
    intro w hw
    exact Finset.mem_image.2 ⟨w, (SimpleGraph.mem_neighborFinset G v w).2 hw, rfl⟩
  by_cases hav : a = v
  · subst hav
    have hb : b ≠ a := hab.ne'
    have hmem := hmemT b hab
    simp only [dif_neg (by simp : ¬(a ≠ a)), dif_pos hb]
    intro hcontra
    rw [dif_pos hb] at hmem
    exact hc (hcontra ▸ hmem)
  · by_cases hbv : b = v
    · subst hbv
      have ha : a ≠ b := hab.ne
      have hmem := hmemT a hab.symm
      simp only [dif_neg (by simp : ¬(b ≠ b)), dif_pos ha]
      intro hcontra
      rw [dif_pos ha] at hmem
      exact hc (hcontra ▸ hmem)
    · simp only [dif_pos hav, dif_pos hbv]
      exact C.valid (show (G.induce {w : V | w ≠ v}).Adj ⟨a, hav⟩ ⟨b, hbv⟩ from hab)

/-! ## Nonvacuity of the planarity predicate -/

/-- Any edgeless graph whose vertices can be placed at distinct points of the plane is
planar. -/
