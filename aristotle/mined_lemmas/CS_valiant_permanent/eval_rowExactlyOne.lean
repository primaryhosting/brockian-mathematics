/-
# Valiant Permanent
Category: Frontier Cs
Target: CS.valiant_permanent
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib
import RequestProject.PermanentGadget

/-!
# Valiant Permanent
Category: Frontier Cs
Target: CS.valiant_permanent
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)

## Scope of the formalization

The statement "the `0/1` permanent is `#P`-complete" has two halves.  What is formalized here is

* the *membership* half, in full: the `0/1` permanent is the counting function of an explicitly
  constructed family of Boolean verifier circuits of polynomial size (`InSharpP perm01Count`);
* the combinatorial identity underlying the problem: the permanent of a `0/1` matrix is the
  number of perfect matchings of the associated bipartite graph;
* the weight-elimination step of Valiant's hardness argument: restricting to `0/1` entries loses
  no generality, since every matrix of natural numbers has the same permanent as a `0/1` matrix
  of controlled size.

The remaining half of Valiant's theorem, namely the parsimonious reduction of an arbitrary `#P`
verifier to a permanent (the gadget construction), is *not* formalized here.
-/

set_option autoImplicit false

namespace CS

/-! ## Boolean circuits -/

/-- Boolean circuits (formulas) over a set `ι` of input variables. -/
inductive Circuit (ι : Type) where
  | var : ι → Circuit ι
  | const : Bool → Circuit ι
  | not : Circuit ι → Circuit ι
  | and : Circuit ι → Circuit ι → Circuit ι
  | or : Circuit ι → Circuit ι → Circuit ι

namespace Circuit

variable {ι : Type}

/-- Evaluation of a circuit at a Boolean assignment of its variables. -/

theorem eval_rowExactlyOne (n : ℕ) (i : Fin n) (x w : Fin n × Fin n → Bool) :
    (rowExactlyOne n i).eval (Sum.elim x w) = true ↔ ∃! j, w (i, j) = true := by
  simp only [rowExactlyOne, Circuit.eval_anyL, List.mem_map,
    List.mem_finRange, true_and]
  constructor
  · rintro ⟨c, ⟨j, rfl⟩, hc⟩
    simp only [Circuit.eval, wv, Sum.elim_inr, Bool.and_eq_true] at hc
    refine ⟨j, hc.1, ?_⟩
    intro j' hj'
    by_contra hne
    have := hc.2
    simp only [Circuit.eval_allL, List.mem_map, List.mem_finRange, true_and] at this
    have h2 := this _ ⟨j', rfl⟩
    rw [if_neg hne] at h2
    simp [Circuit.eval, hj'] at h2
  · rintro ⟨j, hj, huniq⟩
    refine ⟨_, ⟨j, rfl⟩, ?_⟩
    simp only [Circuit.eval, wv, Sum.elim_inr, Bool.and_eq_true]
    refine ⟨hj, ?_⟩
    simp only [Circuit.eval_allL, List.mem_map, List.mem_finRange, true_and]
    rintro c ⟨j', rfl⟩
    by_cases hj' : j' = j
    · simp [hj', Circuit.eval]
    · rw [if_neg hj']
      simp only [Circuit.eval, Sum.elim_inr, Bool.not_eq_true']
      by_contra hcon
      simp only [Bool.not_eq_false] at hcon
      exact hj' (huniq j' hcon)

