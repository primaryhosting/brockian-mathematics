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

theorem exists_injOn_into_infinite {E : Set Ordinal.{0}} (hE : E.Finite) {S : Set ℕ}
    (hS : S.Infinite) : ∃ r : Ordinal.{0} → ℕ, Set.InjOn r E ∧ ∀ γ ∈ E, r γ ∈ S := by
  classical
  have : Fintype E := hE.fintype
  obtain ⟨j, hj⟩ : ∃ j : E → ℕ, Function.Injective j :=
    ⟨fun x => (Fintype.equivFin E x : ℕ), fun a b hab => by
      simpa using Fin.val_injective (α := fun _ => True) (by simpa using hab)⟩
  let emb : ℕ ↪ S := hS.natEmbedding S
  refine ⟨fun γ => if h : γ ∈ E then (emb (j ⟨γ, h⟩) : ℕ) else 0, ?_, ?_⟩
  · intro a ha b hb hab
    simp only [dif_pos ha, dif_pos hb] at hab
    have : emb (j ⟨a, ha⟩) = emb (j ⟨b, hb⟩) := Subtype.ext hab
    have := hj (emb.injective this)
    exact congrArg Subtype.val this
  · intro γ hγ
    simp only [dif_pos hγ]
    exact (emb (j ⟨γ, hγ⟩)).2

/-- **Extension lemma.**  Suppose `fβ` is injective on `Iio β` with co-infinite range, and
`g` is injective on `Iio α` (`α ≤ β`), differs from `fβ` on only finitely many points below
`α`, and avoids the finite set `R`.  Then `g` extends to a function on `Iio β` with the same
properties relative to `β`. -/
