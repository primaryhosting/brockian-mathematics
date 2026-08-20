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

theorem eval_dominated (n : ℕ) (x w : Fin n × Fin n → Bool) :
    (dominated n).eval (Sum.elim x w) = true ↔ ∀ i j, w (i, j) = true → x (i, j) = true := by
  simp only [dominated, Circuit.eval_allL, List.mem_flatMap, List.mem_map, List.mem_finRange,
    true_and]
  constructor
  · rintro h i j hw
    have := h _ ⟨i, ⟨j, rfl⟩⟩
    simp only [Circuit.eval, wv, xv, Sum.elim_inr, Sum.elim_inl, hw] at this
    simpa using this
  · rintro h c ⟨i, ⟨j, rfl⟩⟩
    simp only [Circuit.eval, wv, xv, Sum.elim_inr, Sum.elim_inl]
    cases hw : w (i, j) with
    | false => simp
    | true => simp [h i j hw]

