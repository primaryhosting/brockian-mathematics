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

theorem CoInf.of_diffSet_finite {α : Ordinal.{0}} {f g : Ordinal.{0} → ℕ} (hf : CoInf α f)
    (hd : (diffSet α f g).Finite) : CoInf α g := by
  have hsub : ((f '' Set.Iio α)ᶜ \ (g '' (diffSet α f g))) ⊆ (g '' Set.Iio α)ᶜ := by
    intro n hn
    intro hmem
    rcases image_subset_of_diffSet α f g hmem with h | h
    · exact hn.1 h
    · exact hn.2 h
  exact (hf.diff (hd.image g)).mono hsub

/-! ### The extension lemma -/

/-- Given a finite set `E` of ordinals and an infinite set `S ⊆ ℕ`, there is a function
which is injective on `E` with all values on `E` lying in `S`. -/
