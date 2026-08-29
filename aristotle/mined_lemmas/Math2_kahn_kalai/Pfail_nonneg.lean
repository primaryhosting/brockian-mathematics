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

lemma Pfail_nonneg {p : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (k : ℕ) (H : Finset (Finset α)) :
    0 ≤ Pfail p k H := by
  induction k generalizing H with
  | zero => rw [Pfail_zero]; exact failInd_nonneg _ _
  | succ k ih =>
      rw [Pfail_succ]
      exact Finset.sum_nonneg fun W _ => mul_nonneg (weight_nonneg hp0 hp1 W) (ih _)

