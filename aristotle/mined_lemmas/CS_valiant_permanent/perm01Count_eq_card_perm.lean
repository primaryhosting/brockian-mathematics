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

theorem perm01Count_eq_card_perm (n : ℕ) (x : Fin n × Fin n → Bool) :
    perm01Count n x = Nat.card {σ : Equiv.Perm (Fin n) // ∀ i, x (σ i, i) = true} := by
  classical
  have h1 : perm01Count n x
      = ∑ σ : Equiv.Perm (Fin n), if (∀ i, x (σ i, i) = true) then 1 else 0 := by
    unfold perm01Count Matrix.permanent
    refine Finset.sum_congr rfl ?_
    intro σ _
    by_cases h : ∀ i, x (σ i, i) = true
    · simp [mat01, h]
    · push_neg at h
      obtain ⟨i, hi⟩ := h
      rw [if_neg (by push_neg; exact ⟨i, hi⟩)]
      exact Finset.prod_eq_zero (Finset.mem_univ i) (by simp [mat01, hi])
  rw [h1, Finset.sum_boole]
  rw [Nat.card_eq_fintype_card, Fintype.card_subtype]
  simp

/-! ## The verifier circuit for the permanent -/

/-- Variables of the verifier circuit: the `n²` input bits and the `n²` witness bits. -/
abbrev PermVar (n : ℕ) : Type := (Fin n × Fin n) ⊕ (Fin n × Fin n)

/-- The circuit variable holding the input bit `(i, j)`. -/
