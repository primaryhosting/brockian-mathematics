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

theorem eval_permVerifier (n : ℕ) (x w : Fin n × Fin n → Bool) :
    (permVerifier n).eval (Sum.elim x w) = true ↔
      ((∀ i, ∃! j, w (i, j) = true) ∧ (∀ j, ∃! i, w (i, j) = true) ∧
        ∀ i j, w (i, j) = true → x (i, j) = true) := by
  simp only [permVerifier, Circuit.eval_allL, List.mem_cons, List.not_mem_nil, or_false]
  constructor
  · intro h
    refine ⟨fun i => ?_, fun j => ?_, ?_⟩
    · have := h _ (Or.inl rfl)
      rw [Circuit.eval_allL] at this
      exact (eval_rowExactlyOne n i x w).1
        (this _ (List.mem_map_of_mem (List.mem_finRange i)))
    · have := h _ (Or.inr (Or.inl rfl))
      rw [Circuit.eval_allL] at this
      exact (eval_colExactlyOne n j x w).1
        (this _ (List.mem_map_of_mem (List.mem_finRange j)))
    · exact (eval_dominated n x w).1 (h _ (Or.inr (Or.inr rfl)))
  · rintro ⟨hr, hc, hd⟩ c hcm
    rcases hcm with rfl | rfl | rfl
    · rw [Circuit.eval_allL]
      intro d hd
      rw [List.mem_map] at hd
      obtain ⟨i, -, rfl⟩ := hd
      exact (eval_rowExactlyOne n i x w).2 (hr i)
    · rw [Circuit.eval_allL]
      intro d hd
      rw [List.mem_map] at hd
      obtain ⟨j, -, rfl⟩ := hd
      exact (eval_colExactlyOne n j x w).2 (hc j)
    · exact (eval_dominated n x w).2 hd

/-! ## Counting the accepted witnesses -/

