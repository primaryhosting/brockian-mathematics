import Mathlib

/-!
# Zorn
Category: Frontier Wave 2 (deeper machinery)
Target: SetTheory.zorn
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace SetTheory

open Set

/-- **Zorn's lemma** for a preorder: if every chain (with respect to `≤`) has an upper bound,
then there exists a maximal element `m`, i.e. one such that `m ≤ a → a ≤ m` for all `a`.

This is Mathlib's `exists_maximal_of_chains_bounded`, instantiated at the relation `(· ≤ ·)`
with transitivity witnessed by `le_trans`. -/

theorem zorn {α : Type*} [Preorder α]
    (h : ∀ c : Set α, IsChain (· ≤ ·) c → ∃ ub : α, ∀ a ∈ c, a ≤ ub) :
    ∃ m : α, ∀ a : α, m ≤ a → a ≤ m :=
  exists_maximal_of_chains_bounded h le_trans

/-- The same hypothesis, for a partial order, yields a maximal element in Mathlib's
`IsMax` form (`∀ a, m ≤ a → a ≤ m`). Proved via `zorn_le`. -/
