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

theorem excess_border (A : Matrix α α ℕ) (r c : α) :
    excess (border A r c) = excess (setEntry A r c (A r c - 1)) := by
  classical
  rw [excess_eq_sum_sum, excess_eq_sum_sum, Fintype.sum_option]
  have h1 : (∑ j : Option α, (border A r c none j - 1)) = 0 := by
    rw [Fintype.sum_option]
    simp only [border_none_none, border_none_some]
    refine by simp [Finset.sum_eq_zero, apply_ite (fun x : ℕ => x - 1)]
  rw [h1, zero_add]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Fintype.sum_option]
  simp only [border_some_none, border_some_some, apply_ite (fun x : ℕ => x - 1)]
  simp

