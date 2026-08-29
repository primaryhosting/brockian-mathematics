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

lemma rounds_le_logb (F : Finset (Finset α)) :
    (rounds (ell F) : ℝ) ≤ 2 * Real.logb 2 (ell F) := by
  have hL := one_le_logb_ell F
  have hnat : rounds (ell F) ≤ Nat.log 2 (ell F) + 1 := rounds_le _
  have h2 : 2 ≤ ell F := le_max_left _ _
  have hlog : (Nat.log 2 (ell F) : ℝ) ≤ Real.logb 2 (ell F) := by
    have h1 : (2:ℕ) ^ (Nat.log 2 (ell F)) ≤ ell F := Nat.pow_log_le_self 2 (by omega)
    have h2' : ((2:ℝ)) ^ (Nat.log 2 (ell F)) ≤ (ell F : ℝ) := by exact_mod_cast h1
    rw [show ((Nat.log 2 (ell F) : ℝ)) = Real.logb 2 ((2:ℝ) ^ (Nat.log 2 (ell F))) by
      rw [Real.logb_pow]; simp]
    exact Real.logb_le_logb_of_le (by norm_num) (by positivity) h2'
  have : (rounds (ell F) : ℝ) ≤ (Nat.log 2 (ell F) : ℝ) + 1 := by exact_mod_cast hnat
  linarith

/-- **The Kahn–Kalai conjecture** (Park–Pham). For every nontrivial increasing family `F` on a
finite set, the threshold is at most `128` times the expectation-threshold times
`log₂ ℓ(F)`. -/
