import Mathlib
import RequestProject.KahnKalai.Iteration

/-!
# Kahn Kalai
Category: Frontier Math
Target: Math2.kahn_kalai
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)

Expectation and threshold are within a log factor: a formalisation of the Park–Pham proof
of the Kahn–Kalai conjecture.
-/

open Finset

namespace Math2

variable {α : Type*} [Fintype α] [DecidableEq α]

/-- The `p`-biased measure of a family of subsets. -/

lemma mu_add_muFail (p : ℝ) (H : Finset (Finset α)) :
    mu p (upClosure H) + muFail p H = 1 := by
  have hsplit : ∀ U : Finset α,
      (if U ∈ upClosure H then weight p U else 0) + weight p U * failInd H U = weight p U := by
    intro U
    by_cases hU : ∃ S ∈ H, S ⊆ U
    · have : U ∈ upClosure H := by simp only [upClosure, Finset.mem_filter, Finset.mem_univ]
                                   exact ⟨trivial, hU⟩
      rw [if_pos this, failInd, if_pos hU]
      ring
    · have : U ∉ upClosure H := by
        simp only [upClosure, Finset.mem_filter, Finset.mem_univ, true_and]
        exact hU
      rw [if_neg this, failInd, if_neg hU]
      ring
  have h1 : (∑ U : Finset α, (if U ∈ upClosure H then weight p U else 0))
      + ∑ U : Finset α, weight p U * failInd H U = 1 := by
    rw [← Finset.sum_add_distrib]
    rw [Finset.sum_congr rfl (fun U _ => hsplit U)]
    exact sum_weight p
  rw [mu, muFail]
  rw [← h1]
  congr 1
  rw [Finset.sum_ite_mem, Finset.univ_inter]

