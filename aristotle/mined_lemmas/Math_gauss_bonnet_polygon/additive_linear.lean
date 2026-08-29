import Mathlib

/-!
# Additive monotone functions on an interval are linear

An elementary Cauchy-functional-equation argument: a nonnegative function on `[0, π]` which is
additive there is determined by its value at `π`.
-/

open scoped Real

namespace Math

variable {W : ℝ → ℝ}

/-- An additive nonnegative function is monotone. -/

theorem additive_linear (hnn : ∀ θ, 0 ≤ W θ) (hzero : W 0 = 0)
    (hadd : ∀ x y : ℝ, 0 < x → 0 < y → x + y ≤ π → W (x + y) = W x + W y)
    (hpi : W π = 2 * π / 3) {θ : ℝ} (h0 : 0 ≤ θ) (hp : θ ≤ π) :
    W θ = 2 * θ / 3 := by
  rcases eq_or_lt_of_le hp with rfl | hlt
  · exact hpi
  -- the value at `π / n`
  have hdiv : ∀ n : ℕ, 0 < n → W (π / n) = 2 * π / 3 / n := by
    intro n hn
    have hnpos : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
    have hx : 0 < π / n := by positivity
    have hkey := additive_nsmul hzero hadd n (π / n) hx (le_of_eq (by field_simp))
    rw [show (n : ℝ) * (π / n) = π by field_simp] at hkey
    rw [hpi] at hkey
    exact (eq_div_iff (ne_of_gt hnpos)).2 (by rw [mul_comm]; linarith)
  -- the squeeze
  have hbound : ∀ n : ℕ, 0 < n → |W θ - 2 * θ / 3| ≤ 2 * π / 3 / n := by
    intro n hn
    have hnpos : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
    set m : ℕ := ⌊θ * n / π⌋₊ with hm
    have hzpos : 0 ≤ θ * n / π := by positivity
    have hmle : (m : ℝ) ≤ θ * n / π := Nat.floor_le hzpos
    have hmlt : θ * n / π < m + 1 := Nat.lt_floor_add_one _
    have hmn : (m : ℝ) < n := by
      have : θ * n / π < n := by
        rw [div_lt_iff₀ Real.pi_pos]
        nlinarith [Real.pi_pos]
      linarith
    have hm1n : (m : ℝ) + 1 ≤ n := by
      have : m < n := by exact_mod_cast hmn
      have : (m : ℝ) + 1 ≤ (n : ℝ) := by exact_mod_cast this
      exact this
    -- the two comparison points
    have hlow : (m : ℝ) * (π / n) ≤ θ := by
      have := mul_le_mul_of_nonneg_right hmle (le_of_lt (by positivity : (0:ℝ) < π / n))
      calc (m : ℝ) * (π / n) ≤ (θ * n / π) * (π / n) := this
        _ = θ := by field_simp
    have hhigh : θ ≤ ((m : ℝ) + 1) * (π / n) := by
      have := mul_le_mul_of_nonneg_right hmlt.le (le_of_lt (by positivity : (0:ℝ) < π / n))
      calc θ = (θ * n / π) * (π / n) := by field_simp
        _ ≤ ((m : ℝ) + 1) * (π / n) := this
    have hWlow : W ((m : ℝ) * (π / n)) = (m : ℝ) * (2 * π / 3 / n) := by
      rcases Nat.eq_zero_or_pos m with hm0 | hm0
      · simp [hm0, hzero]
      · have := additive_nsmul hzero hadd m (π / n) (by positivity) (by
          rw [show (m : ℝ) * (π / n) = (m : ℝ) / n * π by ring]
          nlinarith [Real.pi_pos, (div_le_one hnpos).2 hmn.le])
        rw [this, hdiv n hn]
    have hWhigh : W (((m : ℝ) + 1) * (π / n)) = ((m : ℝ) + 1) * (2 * π / 3 / n) := by
      have hcast : ((m : ℝ) + 1) = ((m + 1 : ℕ) : ℝ) := by push_cast; ring
      rw [hcast]
      have := additive_nsmul hzero hadd (m + 1) (π / n) (by positivity) (by
        rw [show ((m + 1 : ℕ) : ℝ) * (π / n) = ((m + 1 : ℕ) : ℝ) / n * π by ring]
        have : ((m + 1 : ℕ) : ℝ) / n ≤ 1 := by
          rw [div_le_one hnpos]
          push_cast
          exact hm1n
        nlinarith [Real.pi_pos])
      rw [this, hdiv n hn]
    have h1 : W ((m : ℝ) * (π / n)) ≤ W θ :=
      additive_mono hnn hzero hadd (by positivity) hlow hp
    have h2 : W θ ≤ W (((m : ℝ) + 1) * (π / n)) := by
      refine additive_mono hnn hzero hadd h0 hhigh ?_
      rw [show ((m : ℝ) + 1) * (π / n) = (((m : ℝ) + 1) / n) * π by ring]
      have : ((m : ℝ) + 1) / n ≤ 1 := (div_le_one hnpos).2 hm1n
      nlinarith [Real.pi_pos]
    rw [hWlow] at h1
    rw [hWhigh] at h2
    have hθlow : (m : ℝ) * (2 * π / 3 / n) ≤ 2 * θ / 3 := by
      have he : (m : ℝ) * (2 * π / 3 / n) = 2 / 3 * ((m : ℝ) * (π / n)) := by ring
      rw [he]
      linarith
    have hθhigh : 2 * θ / 3 ≤ ((m : ℝ) + 1) * (2 * π / 3 / n) := by
      have he : ((m : ℝ) + 1) * (2 * π / 3 / n) = 2 / 3 * (((m : ℝ) + 1) * (π / n)) := by ring
      rw [he]
      linarith
    have hexp : ((m : ℝ) + 1) * (2 * π / 3 / n) = (m : ℝ) * (2 * π / 3 / n) + 2 * π / 3 / n := by
      ring
    rw [abs_le]
    rw [hexp] at h2 hθhigh
    constructor <;> linarith
  by_contra hne
  have hd : 0 < |W θ - 2 * θ / 3| := abs_pos.2 (sub_ne_zero.2 hne)
  obtain ⟨n, hn⟩ := exists_nat_gt ((2 * π / 3) / |W θ - 2 * θ / 3|)
  have hnpos : (0 : ℝ) < (n : ℝ) := lt_of_le_of_lt (by positivity) hn
  have hn' : 0 < n := by exact_mod_cast hnpos
  have := hbound n hn'
  rw [div_lt_iff₀ hd] at hn
  rw [le_div_iff₀ hnpos] at this
  linarith

end Math

import Mathlib

/-!
# Basic measure-theoretic tools for solid angles in Euclidean 3-space
-/

open MeasureTheory Metric InnerProductGeometry
open scoped RealInnerProductSpace

noncomputable section

namespace Math

/-- Euclidean three-space. -/
abbrev E3 : Type := EuclideanSpace ℝ (Fin 3)

