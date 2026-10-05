import Mathlib

/-!
# Gale Stewart Open
Category: Frontier — Set Theory
Target: Frontier.Gale_Stewart_open
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace Frontier

variable {A : Type*}

/-- The list of the first `n` moves of the play `f`. -/

lemma eq_of_takeF_eq {f g : ℕ → A} {n : ℕ} (h : takeF f n = takeF g n) :
    ∀ i < n, f i = g i := by
  intro i hi
  have := congrArg (fun l => l[i]?) h
  simpa [takeF, List.getElem?_map, List.getElem?_range, hi] using this

/-- A strategy assigns a move to every position (finite sequence of moves played so far). -/
abbrev Strategy (A : Type*) := List A → A

/-- The play `f` follows strategy `σ` for player I (who moves at the even-numbered turns). -/
