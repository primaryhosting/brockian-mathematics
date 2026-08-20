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

lemma reachB_card {a b : C} {t : ℕ} (h : reachB E t a b = true) :
    reachB E (Fintype.card C) a b = true := by
  set N := Fintype.card C with hN
  by_cases hstab : ∀ u < N, reachSet E a u ≠ reachSet E a (u + 1)
  · exfalso
    have h1 : N + 1 ≤ (reachSet E a N).card := reachSet_card_ge N hstab
    have h2 : (reachSet E a N).card ≤ N := by
      simpa [hN] using Finset.card_le_univ (reachSet E a N)
    omega
  · push_neg at hstab
    obtain ⟨u, huN, hu⟩ := hstab
    have hconst : ∀ v, reachSet E a (u + v) = reachSet E a u := reachSet_stab hu
    have hbN : reachSet E a N = reachSet E a u := by
      have := hconst (N - u)
      rwa [show u + (N - u) = N by omega] at this
    rcases Nat.lt_or_ge t N with htN | htN
    · exact reachB_mono (le_of_lt htN) h
    · have hb : b ∈ reachSet E a t := mem_reachSet.mpr h
      have : reachSet E a t = reachSet E a u := by
        have := hconst (t - u)
        rwa [show u + (t - u) = t by omega] at this
      rw [this, ← hbN] at hb
      exact mem_reachSet.mp hb

end Reach

end CS

namespace CS

/-! ## Adding a unique accepting configuration -/

section Sink

variable (M : NSM)

/-- Edges of the configuration graph of `M` extended by a single absorbing accepting
configuration `none`. -/
