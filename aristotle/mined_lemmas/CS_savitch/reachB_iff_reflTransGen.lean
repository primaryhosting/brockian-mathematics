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

lemma reachB_iff_reflTransGen (a b : C) :
    (∃ t, reachB E t a b = true) ↔ Relation.ReflTransGen (fun a b => E a b = true) a b := by
  constructor
  · rintro ⟨t, ht⟩
    induction t generalizing b with
    | zero =>
        simp only [reachB_zero, decide_eq_true_eq] at ht
        subst ht; exact Relation.ReflTransGen.refl
    | succ t ih =>
        rw [reachB_succ] at ht
        rcases Bool.or_eq_true_iff.mp ht with h | h
        · exact ih b h
        · simp only [decide_eq_true_eq] at h
          obtain ⟨m, hm, hmb⟩ := h
          exact Relation.ReflTransGen.tail (ih m hm) hmb
  · intro h
    induction h with
    | refl => exact ⟨0, by simp [reachB_zero]⟩
    | tail hab hbc ih =>
        obtain ⟨t, ht⟩ := ih
        refine ⟨t + 1, ?_⟩
        rw [reachB_succ]
        simp only [Bool.or_eq_true_iff, decide_eq_true_eq]
        exact Or.inr ⟨_, ht, hbc⟩

/-- The set of configurations reachable from `a` in at most `t` steps. -/
