import Mathlib

/-!
# Robertson Seymour
Category: Frontier Math
Target: Math2.robertson_seymour
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

/-
NOTE ON THE HEADER: Lean 4 requires `import` to be the first command of a file, so the
module docstring above is placed directly after `import Mathlib` (a `/-! ... -/` block
before the import is a parse error).
-/

set_option maxHeartbeats 1000000
set_option autoImplicit false

namespace Math2

universe u v w

open SimpleGraph

/-! ## The minor relation -/

/-- `IsMinor H G` says that `H` is a minor of `G`: there is a family of pairwise disjoint,
nonempty, connected *branch sets* `B w ⊆ V(G)`, indexed by the vertices `w` of `H`, such
that adjacent vertices of `H` have an edge of `G` between their branch sets. -/

theorem Embeds.congr {V : Type u} {W : Type v} {V' : Type w} {W' : Type*}
    {H : SimpleGraph W} {G : SimpleGraph V} {H' : SimpleGraph W'} {G' : SimpleGraph V'}
    (eH : H ≃g H') (eG : G' ≃g G) (h : Embeds H' G') : Embeds H G := by
  obtain ⟨f, hinj, hadj⟩ := h
  refine ⟨fun x => eG (f (eH x)), ?_, ?_⟩
  · intro a b hab
    exact eH.injective (hinj (eG.injective hab))
  · intro a b hab
    exact eG.map_adj_iff.2 (hadj _ _ (eH.map_adj_iff.2 hab))

/-! ## The minor relation is transitive -/

/-- Reachability transfers along an inclusion of induced subgraphs. -/
