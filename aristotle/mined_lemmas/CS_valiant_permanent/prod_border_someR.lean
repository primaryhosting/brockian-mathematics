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

theorem prod_border_someR (A : Matrix α α ℕ) (r c : α) (e : Equiv.Perm α) :
    (∏ i : Option α, border A r c ((Equiv.Perm.decomposeOption.symm (some r, e)) i) i)
      = if e c = r then ∏ j ∈ univ.erase c, A (e j) j else 0 := by
  classical
  have hval : ∀ i : Option α,
      (Equiv.Perm.decomposeOption.symm (some r, e)) i = Equiv.swap none (some r) (i.map e) := by
    intro i
    simp [Equiv.Perm.decomposeOption]
  rw [Fintype.prod_option]
  have h0 : border A r c ((Equiv.Perm.decomposeOption.symm (some r, e)) none) none = 1 := by
    rw [hval]; simp
  rw [h0, one_mul]
  by_cases hec : e c = r
  · rw [if_pos hec, ← Finset.mul_prod_erase univ _ (Finset.mem_univ c)]
    have hc : border A r c ((Equiv.Perm.decomposeOption.symm (some r, e)) (some c)) (some c) = 1 := by
      rw [hval]
      simp [hec]
    rw [hc, one_mul]
    refine Finset.prod_congr rfl fun j hj => ?_
    have hjc : j ≠ c := Finset.ne_of_mem_erase hj
    have hej : e j ≠ r := by
      intro h
      exact hjc (e.injective (by rw [h, hec]))
    rw [hval]
    simp only [Option.map_some]
    rw [Equiv.swap_apply_of_ne_of_ne (by simp) (by simp [hej])]
    rw [border_some_some, setEntry_of_ne _ _ _ _ (by tauto)]
  · rw [if_neg hec]
    refine Finset.prod_eq_zero (Finset.mem_univ (e.symm r)) ?_
    rw [hval]
    have h1 : e (e.symm r) = r := by simp
    simp only [Option.map_some, h1]
    rw [Equiv.swap_apply_right]
    rw [border_none_some, if_neg]
    intro hcon
    exact hec (by rw [← hcon]; simp)

