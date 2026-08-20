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

theorem excess_setEntry_pred {A : Matrix α α ℕ} {r c : α} (h : 2 ≤ A r c) :
    excess (setEntry A r c (A r c - 1)) + 1 = excess A := by
  classical
  rw [excess, excess, ← Finset.sum_erase_add _ _ (Finset.mem_univ (r, c)),
    ← Finset.sum_erase_add _ _ (Finset.mem_univ (r, c))]
  have hbody : ∀ p ∈ (univ : Finset (α × α)).erase (r, c),
      (setEntry A r c (A r c - 1) p.1 p.2 - 1) = (A p.1 p.2 - 1) := by
    intro p hp
    have : ¬(p.1 = r ∧ p.2 = c) := by
      intro hcon
      exact (Finset.ne_of_mem_erase hp) (Prod.ext hcon.1 hcon.2)
    rw [setEntry_of_ne _ _ _ _ this]
  rw [Finset.sum_congr rfl hbody]
  simp only [setEntry_self]
  omega

