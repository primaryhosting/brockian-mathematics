import Mathlib

/-!
# Zorn (Mathlib formulation)

Companion to `RequestProject/SetTheoryZorn.lean`.  That file is self-contained (it proves Zorn's

lemma from the Lean core logic, using its own minimal set theory, because Lean forbids `import`
commands after the required header comment).  Here we state and prove the same results in terms of
Mathlib's `Set`, `IsChain`, `Preorder` and `PartialOrder`, via `exists_maximal_of_chains_bounded`
and `zorn_le`.
-/

namespace SetTheory

/-- **Zorn's lemma** for a preorder: if every chain has an upper bound, then there is a maximal
element `m`, i.e. every `a` with `m ≤ a` satisfies `a ≤ m`. -/
