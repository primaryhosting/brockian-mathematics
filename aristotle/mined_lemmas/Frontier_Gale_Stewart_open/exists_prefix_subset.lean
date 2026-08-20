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

namespace Frontier

section GaleStewart

variable {A : Type*}

/-- In a two–player game on the move set `A`, the players alternate moves, player I moving at
positions of even length and player II at positions of odd length.  Given strategies `σ` for
player I and `τ` for player II, `nextMove σ τ p` is the move played at the position `p`. -/

lemma exists_prefix_subset [TopologicalSpace A] [DiscreteTopology A] {W : Set (ℕ → A)}
    (hW : IsOpen W) {x : ℕ → A} (hx : x ∈ W) :
    ∃ n : ℕ, ∀ y : ℕ → A, (∀ i < n, y i = x i) → y ∈ W := by
  obtain ⟨v, ⟨x', n, rfl⟩, hxv, hvW⟩ :=
    (PiNat.isTopologicalBasis_cylinders (fun _ : ℕ => A)).exists_subset_of_mem_open hx hW
  refine ⟨n, fun y hy => ?_⟩
  apply hvW
  have hxx' : PiNat.cylinder x n = PiNat.cylinder x' n := PiNat.mem_cylinder_iff_eq.1 hxv
  rw [← hxx']
  exact PiNat.mem_cylinder_iff.2 hy

/-- **Gale–Stewart theorem**: every open game is determined.  Here a game is given by a move set
`A` (discrete, nonempty) and a payoff set `W ⊆ (ℕ → A)` for player I; the players alternately
choose elements of `A`, player I starting, and player I wins the resulting play `x : ℕ → A`
iff `x ∈ W`.  If `W` is open, then either player I has a winning strategy, or player II has one. -/
