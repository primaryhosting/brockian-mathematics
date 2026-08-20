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

lemma reachSet_card_ge {a : C} (t : ℕ) (h : ∀ u < t, reachSet E a u ≠ reachSet E a (u + 1)) :
    t + 1 ≤ (reachSet E a t).card := by
  induction t with
  | zero =>
      have : reachSet E a 0 = {a} := by
        ext b; simp [reachSet, reachB_zero, eq_comm]
      simp [this]
  | succ t ih =>
      have h1 : t + 1 ≤ (reachSet E a t).card := ih (fun u hu => h u (by omega))
      have h2 : reachSet E a t ⊂ reachSet E a (t + 1) :=
        ⟨reachSet_subset_succ a t, fun hsub =>
          h t (by omega) (Finset.Subset.antisymm (reachSet_subset_succ a t) hsub)⟩
      have := Finset.card_lt_card h2
      omega

