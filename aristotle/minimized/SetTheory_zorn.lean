import Mathlib

/-!
# Zorn
Category: Frontier Wave 2 (deeper machinery)
Target: SetTheory.zorn
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace SetTheory

/-- **Zorn's lemma** for a preorder: if every chain has an upper bound, then there is a
maximal element `m`, i.e. any `a` with `m ≤ a` satisfies `a ≤ m`. -/

theorem zorn {α : Type*} [Preorder α]
    (h : ∀ c : Set α, IsChain (· ≤ ·) c → ∃ ub, ∀ a ∈ c, a ≤ ub) :
    ∃ m : α, ∀ a : α, m ≤ a → a ≤ m :=
  exists_maximal_of_chains_bounded h le_trans

/-- **Zorn's lemma** for a partial order: if every chain has an upper bound, then there is a
maximal element, unique-ly characterised by `m ≤ a → a = m`. -/
