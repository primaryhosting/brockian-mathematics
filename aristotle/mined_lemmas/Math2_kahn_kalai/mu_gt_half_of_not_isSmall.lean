/-
Minimum fragments (Park-Pham) and the key lemma: the cover built from the large
minimum fragments has small expected cost.
-/
import RequestProject.Basic

open scoped BigOperators
open Finset

namespace KahnKalai

variable {α : Type*} [DecidableEq α]

/-! ### Minimum fragments -/

/-- The candidate fragments of `S` relative to `W`: the sets `S' \ W` for edges `S'` of `H`
contained in `W ∪ S`. -/

theorem mu_gt_half_of_not_isSmall {H : Finset (Finset α)} {m : ℕ} (hm2 : 2 ≤ m)
    (hH : ∀ S ∈ H, S.card ≤ m) {p ρ : ℝ} (hp : 0 < p) (hns : ¬ IsSmall p H)
    (hρ1 : ρ ≤ 1) (hρ : Kconst * p * Real.log m ≤ ρ) : 1 / 2 < mu ρ (upset H) := by
  have hlog2 : (0:ℝ) < Real.log 2 := log_two_pos
  have hlogm : Real.log 2 ≤ Real.log m :=
    Real.log_le_log (by norm_num) (by exact_mod_cast hm2)
  have hlogm0 : 0 < Real.log m := lt_of_lt_of_le hlog2 hlogm
  -- first, `p` is small
  have h648 : 648 * p ≤ ρ := by
    have h1 : Kconst * p * Real.log 2 ≤ Kconst * p * Real.log m := by
      have : 0 ≤ Kconst * p := le_of_lt (mul_pos Kconst_pos hp)
      nlinarith
    have h2 : Kconst * p * Real.log 2 = 648 * p := by
      rw [mul_comm Kconst p, mul_assoc, Kconst_log_two]; ring
    linarith
  set r : ℝ := 324 * p with hrdef
  have hr1 : r ≤ 1 := by rw [hrdef]; linarith
  -- number of rounds
  set k : ℕ := Nat.log 2 m + 1 with hk
  have hmk : m < 2 ^ k := Nat.lt_pow_succ_log_self (by norm_num) m
  -- every cover of `H` is expensive
  have hcov : ∀ U : Finset (Finset α), IsCover H U → (1:ℝ) / 2 ≤ cost p U := by
    intro U hU
    by_contra hlt
    exact hns ⟨U, hU, le_of_lt (not_le.1 hlt)⟩
  have hind := main_induction (α := α) hp hrdef hr1 k m hmk H hH (1 / 2) (by norm_num) hcov
  have hmu34 : (3:ℝ) / 4 ≤ mu (dens r k) (upset H) := by
    have := ebound_le m
    linarith
  -- the density used in the induction is at most `ρ`
  have hklog : (k : ℝ) ≤ 2 * Real.log m / Real.log 2 := by
    have hm0 : m ≠ 0 := by omega
    have h1 : (2:ℝ) ^ (Nat.log 2 m) ≤ (m : ℝ) := by
      have := Nat.pow_log_le_self 2 hm0
      exact_mod_cast this
    have h2 : (Nat.log 2 m : ℝ) * Real.log 2 ≤ Real.log m := by
      have := Real.log_le_log (by positivity) h1
      rwa [Real.log_pow] at this
    have h3 : Real.log 2 ≤ Real.log m := hlogm
    rw [le_div_iff₀ hlog2, hk]
    push_cast
    linarith
  have hdensle : dens r k ≤ ρ := by
    have h1 : dens r k ≤ (k : ℝ) * r := dens_le_mul r (by linarith) hr1 k
    have h2 : (k : ℝ) * r ≤ Kconst * p * Real.log m := by
      rw [hrdef, Kconst]
      have h3 : (k : ℝ) * (324 * p) ≤ (2 * Real.log m / Real.log 2) * (324 * p) := by
        have : (0:ℝ) ≤ 324 * p := by linarith
        exact mul_le_mul_of_nonneg_right hklog this
      have h4 : (2 * Real.log m / Real.log 2) * (324 * p) = 648 / Real.log 2 * p * Real.log m := by
        field_simp
        ring
      linarith
    linarith
  have hdens0 : 0 ≤ dens r k := dens_nonneg (by linarith) hr1 k
  have hmono : mu (dens r k) (upset H) ≤ mu ρ (upset H) :=
    mu_mono hdens0 hdensle hρ1 (isUp_upset H)
  linarith

/-! ### Minimal elements, thresholds -/

/-- The minimal elements of a family. -/
