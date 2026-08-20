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

lemma reachB_add (t u : ℕ) (a b : C) :
    reachB E (t + u) a b = true ↔ ∃ m, reachB E t a m = true ∧ reachB E u m b = true := by
  induction u generalizing b with
  | zero =>
      constructor
      · intro h; exact ⟨b, h, by simp [reachB]⟩
      · rintro ⟨m, hm, hmb⟩
        simp only [reachB, decide_eq_true_eq] at hmb
        subst hmb; simpa using hm
  | succ u ih =>
      constructor
      · intro h
        rw [show t + (u + 1) = (t + u) + 1 from rfl, reachB_succ] at h
        rcases Bool.or_eq_true_iff.mp h with h | h
        · obtain ⟨m, hm, hmb⟩ := (ih b).mp h
          exact ⟨m, hm, reachB_mono_succ hmb⟩
        · simp only [decide_eq_true_eq] at h
          obtain ⟨w, hw, hwb⟩ := h
          obtain ⟨m, hm, hmw⟩ := (ih w).mp hw
          refine ⟨m, hm, ?_⟩
          rw [reachB_succ]
          simp only [Bool.or_eq_true_iff, decide_eq_true_eq]
          exact Or.inr ⟨w, hmw, hwb⟩
      · rintro ⟨m, hm, hmb⟩
        rw [reachB_succ] at hmb
        rw [show t + (u + 1) = (t + u) + 1 from rfl, reachB_succ]
        simp only [Bool.or_eq_true_iff, decide_eq_true_eq]
        rcases Bool.or_eq_true_iff.mp hmb with h | h
        · exact Or.inl ((ih b).mpr ⟨m, hm, h⟩)
        · simp only [decide_eq_true_eq] at h
          obtain ⟨w, hw, hwb⟩ := h
          exact Or.inr ⟨w, (ih w).mpr ⟨m, hm, hw⟩, hwb⟩

