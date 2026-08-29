import Mathlib

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

namespace Frontier

open SimpleGraph

/-! ## Minors and planarity -/

/-- `IsMinor H G` says that `H` is a *minor* of `G`: there is a family of pairwise disjoint
"branch sets" `B w ⊆ V`, one for each vertex `w` of `H`, each inducing a connected subgraph
of `G`, such that adjacent vertices of `H` have branch sets joined by an edge of `G`. -/

theorem IsMinor.of_induce {W V : Type*} {H : SimpleGraph W} {G : SimpleGraph V} {s : Set V}
    (h : IsMinor H (G.induce s)) : IsMinor H G := by
  obtain ⟨B, hdisj, hconn, hadj⟩ := h
  refine ⟨fun w => Subtype.val '' (B w), ?_, ?_, ?_⟩
  · intro w₁ w₂ hw
    exact Set.disjoint_image_of_injective Subtype.val_injective (hdisj w₁ w₂ hw)
  · intro w
    have hsurj : Function.Surjective
        (fun x : ↥(B w) => (⟨x.val.val, ⟨x.val, x.prop, rfl⟩⟩ : ↥(Subtype.val '' (B w)))) := by
      rintro ⟨v, y, hy, rfl⟩
      exact ⟨⟨y, hy⟩, rfl⟩
    exact Connected.map (G := (G.induce s).induce (B w)) (H := G.induce (Subtype.val '' (B w)))
      ⟨fun x => ⟨x.val.val, ⟨x.val, x.prop, rfl⟩⟩, fun {_ _} hab => hab⟩ hsurj (hconn w)
  · intro w₁ w₂ hw
    obtain ⟨a, ha, b, hb, hab⟩ := hadj w₁ w₂ hw
    exact ⟨a.val, ⟨a, ha, rfl⟩, b.val, ⟨b, hb, rfl⟩, hab⟩

/-- Planarity is inherited by induced subgraphs. -/
