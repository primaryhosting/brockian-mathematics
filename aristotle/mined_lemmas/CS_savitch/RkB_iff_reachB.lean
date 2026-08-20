/-
# Savitch
Category: Frontier Cs
Target: CS.savitch
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

namespace CS

/-! ## Machine model

We work with a *non-uniform* space-bounded machine model.  A machine works on inputs of one
fixed length; a language belongs to a space class if for every input length there is a machine
of the appropriate size deciding the language on inputs of that length.

A machine is described by its set of configurations `Cfg` (which is the whole memory of the
machine: the space used is `log₂ (card Cfg)`), a designated start configuration, a function
`head` telling which position of the (read-only) input is currently scanned, and a transition
which may depend on the current configuration and on the single input bit that is being read.
Note that the machine has *no* other access to the input, which is what makes the space measure
meaningful. -/

/-- The `i`-th bit of an input word; `false` beyond the end of the word. -/

lemma RkB_iff_reachB (k : ℕ) (a b : C) :
    RkB E k a b = true ↔ reachB E (2 ^ k) a b = true := by
  induction k generalizing a b with
  | zero =>
      constructor
      · intro h
        simp only [RkB, Bool.or_eq_true_iff, decide_eq_true_eq] at h
        rcases h with h | h
        · subst h; exact reachB_self _ _
        · rw [show (2 : ℕ) ^ 0 = 0 + 1 by norm_num, reachB_succ]
          simp only [Bool.or_eq_true_iff, decide_eq_true_eq]
          exact Or.inr ⟨a, by simp [reachB_zero], h⟩
      · intro h
        rw [show (2 : ℕ) ^ 0 = 0 + 1 by norm_num, reachB_succ] at h
        simp only [reachB_zero, Bool.or_eq_true_iff, decide_eq_true_eq] at h
        simp only [RkB, Bool.or_eq_true_iff, decide_eq_true_eq]
        rcases h with h | ⟨m, hm, hmb⟩
        · exact Or.inl h
        · subst hm; exact Or.inr hmb
  | succ k ih =>
      have hpow : 2 ^ (k + 1) = 2 ^ k + 2 ^ k := by ring
      simp only [RkB, decide_eq_true_eq, hpow, reachB_add]
      constructor
      · rintro ⟨m, h1, h2⟩; exact ⟨m, (ih a m).mp h1, (ih m b).mp h2⟩
      · rintro ⟨m, h1, h2⟩; exact ⟨m, (ih a m).mpr h1, (ih m b).mpr h2⟩

