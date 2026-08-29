import Mathlib
/-!
# Zorn
Category: Frontier Wave 2 (deeper machinery)
Target: SetTheory.zorn
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace SetTheory

/-- **Zorn's lemma** for a preorder: if every chain (with respect to `≤`) has an upper
bound, then there is a maximal element `m`, i.e. any `a` with `m ≤ a` satisfies `a ≤ m`. -/
theorem zorn {α : Type*} [Preorder α]
    (h : ∀ c : Set α, IsChain (· ≤ ·) c → ∃ ub, ∀ a ∈ c, a ≤ ub) :
    ∃ m : α, ∀ a : α, m ≤ a → a ≤ m :=
  exists_maximal_of_chains_bounded (fun {c} hc => h c hc) fun hab hbc => le_trans hab hbc

/-- **Zorn's lemma** for a partial order: if every chain has an upper bound, then there
is a maximal element, i.e. any `a` above `m` equals `m`. -/
theorem zorn_partialOrder {α : Type*} [PartialOrder α]
    (h : ∀ c : Set α, IsChain (· ≤ ·) c → ∃ ub, ∀ a ∈ c, a ≤ ub) :
    ∃ m : α, ∀ a : α, m ≤ a → a = m :=
  let ⟨m, hm⟩ := zorn h
  ⟨m, fun a ha => le_antisymm (hm a ha) ha⟩

end SetTheory

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

