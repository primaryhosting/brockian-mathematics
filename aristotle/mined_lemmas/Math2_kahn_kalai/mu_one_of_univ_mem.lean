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

lemma mu_one_of_univ_mem {F : Finset (Finset α)} (h : (Finset.univ : Finset α) ∈ F) :
    mu 1 F = 1 := by
  rw [mu, Finset.sum_eq_single (Finset.univ : Finset α)]
  · rw [weight_def]; simp
  · intro U _ hU
    rw [weight_def]
    have : Uᶜ ≠ ∅ := by
      intro hc
      exact hU (Finset.compl_eq_empty_iff.mp hc)
    have hcard : Uᶜ.card ≠ 0 := fun hc => this (Finset.card_eq_zero.1 hc)
    simp [zero_pow hcard]
  · intro hc; exact absurd h hc

