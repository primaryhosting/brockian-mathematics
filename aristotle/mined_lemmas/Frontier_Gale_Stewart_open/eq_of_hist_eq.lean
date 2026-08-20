/-
# Gale Stewart Open
Category: Frontier — Set Theory
Target: Frontier.Gale_Stewart_open
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

namespace GaleStewart

universe u

variable {X : Type u}

/-- The list of the first `n` moves of the play `a`. -/

lemma eq_of_hist_eq {a b : ℕ → X} {n : ℕ} (h : hist a n = hist b n) :
    ∀ i < n, a i = b i := by
  intro i hi
  have := hist_getElem? a n i hi
  have hb := hist_getElem? b n i hi
  rw [h, hb] at this
  exact (Option.some_injective _ this).symm

/-- An open set of plays is determined by finite initial segments. -/
