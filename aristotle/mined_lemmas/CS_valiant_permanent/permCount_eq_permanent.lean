import Mathlib

/-!
# Valiant Permanent
Category: Frontier Cs
Target: CS.valiant_permanent
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

/-!
## Scope of this formalization

Valiant's theorem states that the 0/1 permanent is `#P`-complete. This file develops:

* Boolean circuits with evaluation and size, and a definition of `#P` in its nonuniform
  circuit-verifier form (`CS.InSharpP`), of parsimonious reductions computed by
  polynomial-size circuits (`CS.ParsimoniousReduction`), and of `#P`-completeness
  (`CS.IsSharpPComplete`).
* The 0/1 permanent as a counting problem (`CS.permProblem`), its identification with
  `Matrix.permanent` of the encoded 0/1 matrix, and its identification with the problem of
  counting perfect matchings of a bipartite graph (`CS.matchingProblem`).
* A proof that the 0/1 permanent problem lies in `#P` (`CS.permProblem_inSharpP`), by an
  explicit polynomial-size verifier circuit family checking that the witness is a permutation
  matrix supported on the `1`-entries of the instance.
* `CS.valiant_permanent`: `#P`-completeness of the 0/1 permanent, given the `#P`-hardness of
  counting bipartite perfect matchings. That hardness — the combinatorial core of Valiant's
  original argument, proved there by an intricate gadget construction — is taken as an explicit
  hypothesis and is *not* formalized here.
-/

namespace CS

/-! ## Boolean circuits -/

/-- Boolean circuits (formulas) over `N` input variables. -/
inductive BoolCircuit (N : ℕ) : Type
  | const : Bool → BoolCircuit N
  | var : Fin N → BoolCircuit N
  | neg : BoolCircuit N → BoolCircuit N
  | conj : BoolCircuit N → BoolCircuit N → BoolCircuit N
  | disj : BoolCircuit N → BoolCircuit N → BoolCircuit N

namespace BoolCircuit

variable {N : ℕ}

/-- Evaluation of a circuit on an input assignment. -/

theorem permCount_eq_permanent {k : ℕ} (A : Fin k → Fin k → Bool) :
    (permCount A : ℕ) =
      Matrix.permanent (Matrix.of fun i j => if A i j then (1 : ℕ) else 0) := by
  classical
  have h1 : Matrix.permanent (Matrix.of fun i j => if A i j then (1 : ℕ) else 0)
      = ∑ σ : Equiv.Perm (Fin k), if (∀ i, A (σ i) i = true) then 1 else 0 := by
    rw [Matrix.permanent]
    refine Finset.sum_congr rfl ?_
    intro σ _
    by_cases h : ∀ i, A (σ i) i = true
    · simp [h]
    · push_neg at h
      obtain ⟨i, hi⟩ := h
      rw [if_neg (by push_neg; exact ⟨i, hi⟩)]
      exact Finset.prod_eq_zero (Finset.mem_univ i) (by simpa using hi)
  rw [h1, Finset.sum_boole]
  simp only [permCount]
  rw [Nat.card_eq_fintype_card, Fintype.card_subtype]
  refine Finset.card_nbij (fun σ => σ⁻¹) ?_ ?_ ?_
  · intro σ hσ
    simp only [Finset.coe_filter, Set.mem_setOf_eq, Finset.mem_univ, true_and] at *
    intro i
    have := hσ (σ⁻¹ i)
    simpa using this
  · intro a _ b _ hab
    simpa using congrArg (fun x : Equiv.Perm (Fin k) => x⁻¹) hab
  · intro σ hσ
    simp only [Finset.coe_filter, Set.mem_setOf_eq, Finset.mem_univ, true_and, Set.mem_image] at *
    refine ⟨σ⁻¹, ?_, by simp⟩
    intro i
    have := hσ (σ⁻¹ i)
    simpa using this

/-- Counting perfect matchings of a bipartite graph is the same as evaluating the 0/1 permanent
of its adjacency matrix. -/
