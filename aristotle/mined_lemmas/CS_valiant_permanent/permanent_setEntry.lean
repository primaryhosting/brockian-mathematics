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

theorem permanent_setEntry (M : Matrix α α ℕ) (r c : α) (v : ℕ) :
    (setEntry M r c v).permanent = v * minorSum M r c + restSum M r c := by
  classical
  rw [Matrix.permanent, ← Finset.sum_filter_add_sum_filter_not univ
    (fun e : Equiv.Perm α => e c = r)]
  congr 1
  · rw [minorSum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun e he => ?_
    simp only [Finset.mem_filter] at he
    rw [← Finset.mul_prod_erase univ _ (Finset.mem_univ c), he.2]
    congr 1
    · simp [setEntry]
    · refine Finset.prod_congr rfl fun j hj => ?_
      exact setEntry_of_ne M r c v (by simp [Finset.ne_of_mem_erase hj])
  · rw [restSum]
    refine Finset.sum_congr rfl fun e he => ?_
    simp only [Finset.mem_filter] at he
    refine Finset.prod_congr rfl fun j _ => ?_
    refine setEntry_of_ne M r c v ?_
    rintro ⟨h1, rfl⟩
    exact he.2 h1

