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

lemma sum_pw (p : ℝ) (s : Finset α) : ∑ W ∈ s.powerset, pw p s W = 1 := by
  have h := Finset.prod_add (fun _ : α => p) (fun _ : α => 1 - p) s
  simp only [Finset.prod_const] at h
  simp only [pw]
  rw [← h]
  simp

section Fintype
variable [Fintype α]

/-- The product-measure weight of `W ⊆ α`. -/
