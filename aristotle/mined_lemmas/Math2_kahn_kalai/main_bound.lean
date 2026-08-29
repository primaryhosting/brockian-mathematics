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

theorem main_bound (p : ℝ) (hp : 0 < p) (hq1 : 64 * p ≤ 1) (ℓ : ℕ) :
    ∀ H : Finset (Finset α), (∀ S ∈ H, S.card ≤ ℓ) →
      ∀ c : ℝ, (∀ G : Finset (Finset α), Covers G H → c ≤ cost p G) →
        c * Pfail (64 * p) (rounds ℓ) H ≤ (1 / 30) * (1 - (1 / 16 : ℝ) ^ ℓ) := by
  have hq0 : (0:ℝ) ≤ 64 * p := by positivity
  induction ℓ using Nat.strong_induction_on with
  | _ ℓ ih =>
    intro H hb c hc
    rcases Nat.eq_zero_or_pos ℓ with rfl | hpos
    · rw [rounds_zero, Pfail_zero]
      simp only [pow_zero, sub_self, mul_zero]
      unfold failInd
      split_ifs with hE
      · simp
      · have hHempty : H = ∅ := by
          by_contra hne
          obtain ⟨S, hS⟩ := Finset.nonempty_iff_ne_empty.2 hne
          have hcard : S.card ≤ 0 := hb S hS
          have hSe : S = ∅ := Finset.card_eq_zero.1 (Nat.le_zero.1 hcard)
          exact hE ⟨S, hS, by rw [hSe]⟩
        have hcov : Covers (∅ : Finset (Finset α)) H := by
          intro S hS; rw [hHempty] at hS; exact absurd hS (Finset.notMem_empty S)
        have hc0 : c ≤ 0 := by simpa [cost] using hc ∅ hcov
        simpa using hc0
    · set h := ℓ / 2 with hh
      have hhlt : h < ℓ := Nat.div_lt_self hpos (by norm_num)
      have hle : ℓ ≤ 2 * h + 1 := by omega
      have hRHSnn : (0:ℝ) ≤ (1 / 30) * (1 - (1 / 16 : ℝ) ^ ℓ) := by
        have : (1/16:ℝ) ^ ℓ ≤ 1 := pow_le_one₀ (by norm_num) (by norm_num)
        nlinarith
      rcases lt_or_ge c 0 with hcneg | hcpos
      · have h1 := Pfail_nonneg hq0 hq1 (rounds ℓ) H
        nlinarith
      rw [rounds_of_pos hpos, Pfail_succ]
      have hstep : ∀ W : Finset α,
          c * Pfail (64 * p) (rounds h) (H.image (fun S => S \ W))
            ≤ (1 / 30) * (1 - (1 / 16 : ℝ) ^ h) + cost p (Ufam H h W) := by
        intro W
        have hmono : Pfail (64 * p) (rounds h) (H.image (fun S => S \ W))
            ≤ Pfail (64 * p) (rounds h) (Hfam H h W) :=
          Pfail_mono hq0 hq1 residual_covers_Hfam _
        have hLB : ∀ G : Finset (Finset α), Covers G (Hfam H h W) →
            c - cost p (Ufam H h W) ≤ cost p G := by
          intro G hG
          have h1 := hc (Ufam H h W ∪ G) (covers_union hG)
          have h2 := cost_union_le hp.le (Ufam H h W) G
          linarith
        have hIH := ih h hhlt (Hfam H h W) Hfam_bounded (c - cost p (Ufam H h W)) hLB
        have hP1 := Pfail_le_one hq0 hq1 (rounds h) (Hfam H h W)
        have hP0 := Pfail_nonneg hq0 hq1 (rounds h) (Hfam H h W)
        have hcu := cost_nonneg hp.le (Ufam H h W)
        have hA : c * Pfail (64 * p) (rounds h) (H.image (fun S => S \ W))
            ≤ c * Pfail (64 * p) (rounds h) (Hfam H h W) :=
          mul_le_mul_of_nonneg_left hmono hcpos
        have hB : cost p (Ufam H h W) * Pfail (64 * p) (rounds h) (Hfam H h W)
            ≤ cost p (Ufam H h W) := by
          calc cost p (Ufam H h W) * Pfail (64 * p) (rounds h) (Hfam H h W)
              ≤ cost p (Ufam H h W) * 1 := mul_le_mul_of_nonneg_left hP1 hcu
            _ = cost p (Ufam H h W) := mul_one _
        have e1 : (c - cost p (Ufam H h W)) * Pfail (64 * p) (rounds h) (Hfam H h W)
            = c * Pfail (64 * p) (rounds h) (Hfam H h W)
              - cost p (Ufam H h W) * Pfail (64 * p) (rounds h) (Hfam H h W) := by ring
        rw [e1] at hIH
        linarith
      have hsplit : ∀ W : Finset α,
          weight (64 * p) W * ((1 / 30) * (1 - (1 / 16 : ℝ) ^ h) + cost p (Ufam H h W))
            = weight (64 * p) W * ((1 / 30) * (1 - (1 / 16 : ℝ) ^ h))
              + weight (64 * p) W * cost p (Ufam H h W) := fun W => by ring
      have hnum : (1 / 30) * (1 - (1 / 16 : ℝ) ^ h) + (1 / 32) * (1 / 16 : ℝ) ^ h
          ≤ (1 / 30) * (1 - (1 / 16 : ℝ) ^ ℓ) := by
        have hy : (1 / 16 : ℝ) ^ ℓ ≤ (1 / 16 : ℝ) ^ (h + 1) :=
          pow_le_pow_of_le_one (by norm_num) (by norm_num) (by omega)
        rw [pow_succ] at hy
        linarith
      calc c * ∑ W : Finset α,
            weight (64 * p) W * Pfail (64 * p) (rounds h) (H.image (fun S => S \ W))
          = ∑ W : Finset α, weight (64 * p) W
              * (c * Pfail (64 * p) (rounds h) (H.image (fun S => S \ W))) := by
            rw [Finset.mul_sum]
            exact Finset.sum_congr rfl fun W _ => by ring
        _ ≤ ∑ W : Finset α, weight (64 * p) W
              * ((1 / 30) * (1 - (1 / 16 : ℝ) ^ h) + cost p (Ufam H h W)) :=
            Finset.sum_le_sum fun W _ =>
              mul_le_mul_of_nonneg_left (hstep W) (weight_nonneg hq0 hq1 W)
        _ = (1 / 30) * (1 - (1 / 16 : ℝ) ^ h)
              + ∑ W : Finset α, weight (64 * p) W * cost p (Ufam H h W) := by
            rw [Finset.sum_congr rfl (fun W _ => hsplit W), Finset.sum_add_distrib,
              ← Finset.sum_mul, sum_weight, one_mul]
        _ ≤ (1 / 30) * (1 - (1 / 16 : ℝ) ^ h) + (1 / 32) * (1 / 16 : ℝ) ^ h := by
            have := expected_cost_bound H ℓ h hb hle p hp hq1
            linarith
        _ ≤ (1 / 30) * (1 - (1 / 16 : ℝ) ^ ℓ) := hnum

end Math2

import Mathlib

/-!
# Kahn Kalai
Category: Frontier Math
Target: Math2.kahn_kalai
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open Finset

namespace Math2

variable {α : Type*} [DecidableEq α]

/-- The weight `p ^ |W| * (1-p) ^ |s \ W|` of a subset `W` of `s`, i.e. the probability that
the random subset of `s` including each element independently with probability `p` equals `W`. -/
