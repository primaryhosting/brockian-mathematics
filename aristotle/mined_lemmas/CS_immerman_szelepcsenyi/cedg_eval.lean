import RequestProject.Machine

/-!
# The inductive counting construction

Given a nondeterministic branching program we build, by Immerman and Szelepcsényi's
inductive counting method, a nondeterministic branching program of polynomially larger
size accepting exactly the complementary language.
-/

namespace CS

namespace Compl

variable {n : ℕ} (P : Setup n)

/-! ### The invariant -/

variable (x : Fin n → Bool)

/-- The set of configurations of the original machine reachable in at most `i` steps. -/

lemma cedg_eval (x : Fin n → Bool) (s t : CSt P.N P.V) :
    (cedg P s t).eval x = true ↔ cstep P x s t := by
  classical
  unfold cedg cstep
  split_ifs with h1 h2 h3
  · simp only [Guard.eval_always, true_iff]
    exact Or.inl h1
  · constructor
    · intro hq; exact Or.inr (Or.inl ⟨h2, hq⟩)
    · rintro (hU | ⟨-, hq⟩ | ⟨hN, -⟩)
      · exact absurd hU h1
      · exact hq
      · exact absurd hN (condPos_not_condNeg P h2)
  · rw [Guard.eval_neg]
    constructor
    · intro hq
      refine Or.inr (Or.inr ⟨h3, ?_⟩)
      simpa using hq
    · rintro (hU | ⟨hp, -⟩ | ⟨-, hq⟩)
      · exact absurd hU h1
      · exact absurd hp h2
      · simp [hq]
  · refine iff_of_false (by simp) ?_
    rintro (hU | ⟨hp, -⟩ | ⟨hn, -⟩)
    · exact absurd hU h1
    · exact absurd hp h2
    · exact absurd hn h3

end Compl

end CS

import Mathlib

/-!
# Nondeterministic space-bounded computation

We formalize nondeterministic space-bounded computation by *nondeterministic branching
programs* (NBPs).  An NBP over inputs of length `n` is a finite directed graph whose
vertices are the configurations of the machine, together with a distinguished start
configuration and a set of accepting configurations.  Each potential edge carries a
`Guard`: it is either absent (`never`), always present (`always`), or present exactly
when a single designated bit of the input takes a prescribed value (`bit i b`).  This is
the standard "configuration graph" picture of a space-bounded machine: a machine using
space `s` has `2^{O(s)}` configurations, and a single step of the machine looks at one
bit of the input.

Acceptance is reachability from the start configuration to an accepting configuration.
-/

namespace CS

/-- The condition under which an edge of a nondeterministic branching program is
present: never, always, or exactly when input bit `i` has value `b`. -/
inductive Guard (n : ℕ) : Type
  | never : Guard n
  | always : Guard n
  | bit (i : Fin n) (b : Bool) : Guard n
  deriving DecidableEq

/-- Evaluate a guard on an input. -/
