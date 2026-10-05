import Mathlib

/-!
# Aronszajn Tree Exists
Category: Frontier — Set Theory
Target: Frontier.Aronszajn_tree_exists
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)

This file contains auxiliary material used in the construction of an Aronszajn tree:
basic facts about countable ordinals, a dependent-choice helper, and the key
"extension" lemma for almost-disjoint modifications of injections into `ℕ`.
-/

namespace Aronszajn

open Set Cardinal Ordinal
open scoped Ordinal

/-! ### Countability of initial segments -/

/-- An initial segment of the ordinals is countable iff it lies below `ω₁`. -/

theorem exists_seq_of_step {σ : Type*} (Inv : ℕ → σ → Prop) (Rel : ℕ → σ → σ → Prop)
    (s₀ : σ) (h₀ : Inv 0 s₀)
    (step : ∀ n s, Inv n s → ∃ s', Inv (n + 1) s' ∧ Rel n s s') :
    ∃ u : ℕ → σ, u 0 = s₀ ∧ (∀ n, Inv n (u n)) ∧ ∀ n, Rel n (u n) (u (n + 1)) := by
  classical
  let F : ∀ n : ℕ, {s : σ // Inv n s} := fun n =>
    Nat.rec (motive := fun n => {s : σ // Inv n s}) ⟨s₀, h₀⟩
      (fun n ih => ⟨(step n ih.1 ih.2).choose, (step n ih.1 ih.2).choose_spec.1⟩) n
  exact ⟨fun n => (F n).1, rfl, fun n => (F n).2,
    fun n => (step n (F n).1 (F n).2).choose_spec.2⟩

/-! ### Difference sets -/

/-- The set of `γ < α` on which `f` and `g` differ. -/
