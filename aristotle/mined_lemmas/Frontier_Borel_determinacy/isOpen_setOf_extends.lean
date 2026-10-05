import Mathlib

/-!
# Borel Determinacy
Category: Frontier — Set Theory
Target: Frontier.Borel_determinacy
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

/-! ## Infinite games: positions, strategies, winning strategies

We consider infinite two-player games with perfect information played on an alphabet `X`.
A *play* is a sequence `x : ℕ → X`; the move at time `n` is `x n`.  Which player moves at
time `n` is recorded by a predicate `turn : ℕ → Prop` (the *turn set* of the player under
consideration).  In the classical game `G(A)` on Baire space, player I moves at the even
times and player II at the odd times, and player I wins the play `x` iff `x ∈ A`.
-/

variable {X : Type*}

/-- The position reached after the first `n` moves of the play `x`. -/

lemma isOpen_setOf_extends [TopologicalSpace X] [DiscreteTopology X] (p : List X) :
    IsOpen {y : ℕ → X | Extends p y} := by
  have hcyl : {y : ℕ → X | Extends p y}
      = ⋂ i : Fin p.length, (fun y : ℕ → X => y (i : ℕ)) ⁻¹' {p[(i : ℕ)]'i.isLt} := by
    ext y
    simp only [Set.mem_setOf_eq, Set.mem_iInter, Set.mem_preimage, Set.mem_singleton_iff]
    rw [extends_iff]
    exact ⟨fun h i => h i i.isLt, fun h i hi => h ⟨i, hi⟩⟩
  rw [hcyl]
  exact isOpen_iInter_of_finite fun i => (continuous_apply (i : ℕ)).isOpen_preimage _
    (isOpen_discrete _)

/-- Over a discrete alphabet, combinatorial closedness agrees with topological closedness. -/
