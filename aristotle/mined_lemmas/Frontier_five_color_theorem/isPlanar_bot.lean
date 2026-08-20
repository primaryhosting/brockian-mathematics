import Mathlib

/-!
# Orbits of a permutation

Minimal theory of orbits of a permutation of a finite type, as needed for face counting in a
combinatorial embedding of a graph: a permutation all of whose orbits have at least `n` elements
has at most `#α / n` orbits.
-/

namespace Frontier

variable {α : Type*}

/-- The setoid on `α` whose equivalence classes are the orbits of the permutation `f`. -/

theorem isPlanar_bot {α : Type*} [Fintype α] : IsPlanar (⊥ : SimpleGraph α) := by
  refine ⟨botRot, ?_⟩
  have hF : (botRot (α := α)).faceCount = 0 := by
    have : IsEmpty (Quotient (orbitSetoid
        ((botRot (α := α)).rot * symmPerm (⊥ : SimpleGraph α)))) := by
      constructor
      intro q
      induction q using Quotient.inductionOn with | _ d => exact d.adj.elim
    simp [RotationSystem.faceCount, numOrbits]
  have hE : Nat.card ((⊥ : SimpleGraph α).edgeSet) = 0 := by simp
  have hI : isolatedCount (⊥ : SimpleGraph α) = Nat.card α := by
    simp only [isolatedCount]
    exact Nat.card_congr (Equiv.subtypeUnivEquiv (by simp))
  have hC : Nat.card ((⊥ : SimpleGraph α).ConnectedComponent) = Nat.card α := by
    refine (Nat.card_eq_of_bijective
      (fun a : α => SimpleGraph.connectedComponentMk (⊥ : SimpleGraph α) a) ?_).symm
    constructor
    · intro a b h
      exact SimpleGraph.reachable_bot.mp (SimpleGraph.ConnectedComponent.eq.mp h)
    · intro c
      induction c using SimpleGraph.ConnectedComponent.ind with | _ a => exact ⟨a, rfl⟩
  rw [hF, hE, hI, hC, Nat.card_eq_fintype_card]
  push_cast
  ring_nf
  omega

/-- The rotation system of the graph with a single edge. -/
