import Mathlib

/-!
# Dilworth
Category: Pure Mathematics
Target: Math.dilworth
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

namespace Math

open Finset

variable {α : Type*} [Fintype α] [PartialOrder α]

/-- The finset of all chains (as finsets) of a finite partial order. -/

lemma maxChainCard_le_of_mem_antichainCoverNumbers {n : ℕ}
    (hn : n ∈ antichainCoverNumbers α) : maxChainCard α ≤ n := by
  obtain ⟨A, hA, hcov⟩ := hn
  refine Finset.sup_le ?_
  intro c hc
  have hchain : IsChain (· ≤ ·) (c : Set α) := mem_chainFinsets.1 hc
  classical
  set f : α → Fin n := fun x => (hcov x).choose with hf
  have hmem : ∀ x, x ∈ A (f x) := fun x => (hcov x).choose_spec
  have hinj : Set.InjOn f (c : Set α) := by
    intro a ha b hb hab
    by_contra hne
    have hA' := hA (f a)
    rcases hchain ha hb hne with h | h
    · exact hA' (hmem a) (hab ▸ hmem b) hne h
    · exact hA' (hab ▸ hmem b) (hmem a) (Ne.symm hne) h
  have h := Finset.card_le_card_of_injOn (t := (Finset.univ : Finset (Fin n))) f
    (fun a _ => Finset.mem_univ (f a)) hinj
  simpa using h

/-- **Mirsky's theorem** (the dual of Dilworth's theorem): in a finite partial order, the
minimum number of antichains needed to cover the poset equals the maximum cardinality of a
chain. -/
