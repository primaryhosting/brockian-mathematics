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

theorem colorable_four_of_card_le_four {V : Type} [Fintype V] (G : SimpleGraph V)
    (hV : Fintype.card V ≤ 4) : G.Colorable 4 := by
  obtain ⟨f⟩ : Nonempty (V ↪ Fin 4) := Function.Embedding.nonempty_of_card_le (by simpa using hV)
  exact ⟨SimpleGraph.Coloring.mk f fun {a b} hab h => G.ne_of_adj hab (f.injective h)⟩

end Frontier

