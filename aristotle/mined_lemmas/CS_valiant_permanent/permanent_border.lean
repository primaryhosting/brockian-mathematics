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

theorem permanent_border (A : Matrix α α ℕ) (r c : α) (h : 1 ≤ A r c) :
    (border A r c).permanent = A.permanent := by
  classical
  have expand : (border A r c).permanent
      = ∑ p : Option α × Equiv.Perm α,
          ∏ i : Option α, border A r c ((Equiv.Perm.decomposeOption.symm p) i) i := by
    rw [Matrix.permanent]
    exact (Equiv.sum_comp (Equiv.Perm.decomposeOption.symm)
      (fun σ => ∏ i, border A r c (σ i) i)).symm
  rw [expand, Fintype.sum_prod_type, Fintype.sum_option]
  have hfirst : (∑ e : Equiv.Perm α,
      ∏ i : Option α, border A r c ((Equiv.Perm.decomposeOption.symm (none, e)) i) i)
      = (setEntry A r c (A r c - 1)).permanent := by
    rw [Matrix.permanent]
    exact Finset.sum_congr rfl fun e _ => prod_border_none A r c e
  have hsecond : (∑ i₀ : α, ∑ e : Equiv.Perm α,
      ∏ i : Option α, border A r c ((Equiv.Perm.decomposeOption.symm (some i₀, e)) i) i)
      = minorSum A r c := by
    rw [Finset.sum_eq_single r]
    · rw [minorSum, Finset.sum_filter]
      exact Finset.sum_congr rfl fun e _ => prod_border_someR A r c e
    · intro i₀ _ hi₀
      refine Finset.sum_eq_zero fun e _ => prod_border_someOther A r c i₀ hi₀ e
    · intro hcon
      exact absurd (Finset.mem_univ r) hcon
  rw [hfirst, hsecond, permanent_setEntry, permanent_eq_entry_mul A r c]
  have : A r c - 1 + 1 = A r c := by omega
  nlinarith [this]

/-! ## Eliminating all weights -/

/-- How far the entries of `A` are from being `0/1`. -/
