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

theorem exists_move : ∀ h : Hydra, h ≠ Hydra.dead → ∃ h', Move h h' := by
  intro h
  induction h using Hydra.strong_induction with
  | _ ts ih =>
    intro hne
    match ts, ih with
    | [], _ => exact absurd rfl hne
    | (t :: rest), ih =>
      by_cases ht : t = Hydra.dead
      · subst ht
        exact ⟨.node ([] ++ rest), Or.inl (Chop.mk [] rest)⟩
      · obtain ⟨t', ht'⟩ := ih t List.mem_cons_self ht
        rcases ht' with hc | hd
        · exact ⟨.node ([] ++ List.replicate 1 t' ++ rest),
            Or.inr (Deep.dup [] rest t t' 1 hc)⟩
        · exact ⟨.node ([] ++ t' :: rest), Or.inr (Deep.nest [] rest t t' hd)⟩

/-! ### Sanity checks: the rules really are the Kirby–Paris rules -/

/-- Cutting the single head of the one-headed hydra kills it. -/
example : Move (.node [Hydra.dead]) Hydra.dead := Or.inl (Chop.mk [] [])

/-- The hydra `root — v — head` of height two: cutting its unique head makes the root grow
`k` bare heads, for an arbitrary `k`.  This is the duplication rule. -/
example (k : ℕ) :
    Move (.node [.node [Hydra.dead]]) (.node (List.replicate k Hydra.dead)) := by
  refine Or.inr ?_
  have := Deep.dup [] [] (.node [Hydra.dead]) Hydra.dead k (Chop.mk [] [])
  simpa using this

/-! ### Termination -/

/-- The "hydra shrinks" relation is well-founded. -/
