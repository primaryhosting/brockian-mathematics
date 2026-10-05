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

theorem not_small_prob (H : Finset (Finset α)) (l : ℕ) (hb : ∀ S ∈ H, S.card ≤ l)
    (q : ℝ) (hq : 0 < q) (hq1 : 64 * q ≤ 1) (hns : ¬ IsSmall q H)
    (p : ℝ) (hp : 64 * q * (rounds l : ℝ) ≤ p) (hp1 : p ≤ 1) :
    1 / 2 < mu p (upClosure H) := by
  have hq0 : (0:ℝ) ≤ 64 * q := by positivity
  -- every cover of `H` costs more than `1/2`
  have hLB : ∀ G : Finset (Finset α), Covers G H → (1 / 2 : ℝ) ≤ cost q G := by
    intro G hG
    by_contra hlt
    push_neg at hlt
    exact hns ⟨G, hG, hlt.le⟩
  have hmain := main_bound q hq hq1 l H hb (1 / 2) hLB
  have hPf : Pfail (64 * q) (rounds l) H ≤ 1 / 15 := by
    have h16 : (0:ℝ) ≤ (1 / 16 : ℝ) ^ l := by positivity
    nlinarith
  set k := rounds l with hk
  set p₀ : ℝ := 1 - (1 - 64 * q) ^ k with hp₀
  have hbern : (1 : ℝ) - (k : ℝ) * (64 * q) ≤ (1 - 64 * q) ^ k := by
    have := one_add_mul_le_pow (a := -(64 * q)) (by linarith) k
    simpa using this
  have hp₀le : p₀ ≤ 64 * q * (k : ℝ) := by
    rw [hp₀]; nlinarith
  have hp₀0 : 0 ≤ p₀ := by
    have : (1 - 64 * q) ^ k ≤ 1 := by
      apply pow_le_one₀ (by linarith) (by linarith)
    rw [hp₀]; linarith
  have hp₀1 : p₀ ≤ 1 := by
    have : (0:ℝ) ≤ (1 - 64 * q) ^ k := by
      apply pow_nonneg; linarith
    rw [hp₀]; linarith
  have hmf : muFail p₀ H ≤ 1 / 15 := by
    rw [← Pfail_eq_muFail]
    exact hPf
  have hmono : muFail p H ≤ muFail p₀ H :=
    muFail_anti hp₀0 (le_trans hp₀le (by linarith)) hp1 H
  have := mu_add_muFail p H
  linarith

/-! ### The Kahn–Kalai theorem -/

