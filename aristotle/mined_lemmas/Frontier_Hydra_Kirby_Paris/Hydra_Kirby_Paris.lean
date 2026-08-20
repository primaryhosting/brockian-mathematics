import Mathlib
/-!
# Hydra Kirby Paris
Category: Frontier — Set Theory
Target: Frontier.Hydra_Kirby_Paris
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
namespace KirbyParis

/-!
## Hydras

A *hydra* is a finite rooted tree.  We encode it as an inductive type whose only
constructor takes the (ordered) list of subtrees hanging off the root; the order of the
list carries no meaning, and all statements below are invariant under permuting it.
-/

/-- A hydra: a finite rooted tree, given by the list of subtrees attached to its root. -/
inductive Hydra : Type
  | node : List Hydra → Hydra

namespace Hydra

/-- The dead hydra: a bare root with no heads. -/

theorem Hydra_Kirby_Paris :
    WellFounded (fun h' h : Hydra => Move h h') ∧
    (∀ p : ℕ → Hydra, ¬ ∀ i : ℕ, Move (p i) (p (i + 1))) ∧
    (∀ s : Hydra → Hydra, (∀ g : Hydra, g ≠ Hydra.dead → Move g (s g)) →
      ∀ h : Hydra, ∃ N : ℕ, s^[N] h = Hydra.dead) := by
  refine ⟨move_wf, ?_, ?_⟩
  · intro p hp
    have key : ∀ x : Hydra, Acc (fun h' h : Hydra => Move h h') x → ∀ i : ℕ, p i ≠ x := by
      intro x hx
      induction hx with
      | intro y _ ih =>
        rintro i rfl
        exact ih (p (i + 1)) (hp i) (i + 1) rfl
    exact key (p 0) (move_wf.apply _) 0 rfl
  · intro s hs h
    induction h using move_wf.induction with
    | _ h ih =>
      by_cases hd : h = Hydra.dead
      · exact ⟨0, by simpa using hd⟩
      · obtain ⟨N, hN⟩ := ih (s h) (hs h hd)
        exact ⟨N + 1, by rwa [Function.iterate_succ_apply]⟩

end Frontier

