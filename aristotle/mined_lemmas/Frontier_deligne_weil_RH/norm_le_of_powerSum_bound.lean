/-
# Deligne Weil RH
Category: Frontier — Fields Medal Work
Target: Frontier.deligne_weil_RH
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Deligne Weil RH
Category: Frontier — Fields Medal Work
Target: Frontier.deligne_weil_RH
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open scoped BigOperators
open scoped Real
open scoped Nat
open scoped Classical
open scoped Pointwise

set_option maxHeartbeats 8000000
set_option maxRecDepth 4000
set_option synthInstance.maxHeartbeats 20000
set_option synthInstance.maxSize 128

set_option relaxedAutoImplicit false
set_option autoImplicit false

set_option pp.fullNames true
set_option pp.structureInstances true
set_option pp.coercions.types true
set_option pp.funBinderTypes true
set_option pp.letVarTypes true
set_option pp.piBinderTypes true

set_option grind.warning false

namespace Frontier

open Filter Metric

/-!
## The zeta datum of a variety over a finite field

Mathlib has no étale cohomology, so we formalize the *shape* of the Weil conjectures at
the level of the numerical data they concern: for a `d`-dimensional variety `X` over `𝔽_q`
one has Betti numbers `b i`, inverse roots `α i j` of the characteristic polynomials
`P i` of Frobenius on the `i`-th cohomology group, and point counts
`N n = #X(𝔽_{q^n})` linked by the Grothendieck–Lefschetz trace formula.

The Riemann hypothesis part of the Weil conjectures (Deligne, 1974) is the assertion that
every inverse root occurring in degree `i` has archimedean absolute value `q ^ (i / 2)`.
-/

/-- Numerical zeta-function data attached to a `dim`-dimensional variety over `𝔽_q`:
Betti numbers, the inverse roots of Frobenius in each cohomological degree, the point
counts over the extensions `𝔽_{q ^ n}`, and the Lefschetz trace formula relating them. -/
structure WeilDatum where
  /-- the cardinality of the base field -/
  q : ℕ
  /-- the base field is a genuine finite field -/
  hq : 1 < q
  /-- the dimension of the variety -/
  dim : ℕ
  /-- the Betti numbers -/
  betti : ℕ → ℕ
  /-- the inverse roots of Frobenius acting on the `i`-th cohomology group -/
  root : (i : ℕ) → Fin (betti i) → ℂ
  /-- `pointCount n` is the number of `𝔽_{q ^ n}`-points -/
  pointCount : ℕ → ℕ
  /-- cohomology vanishes above degree `2 * dim` -/
  betti_vanishing : ∀ i, 2 * dim < i → betti i = 0
  /-- the Grothendieck–Lefschetz trace formula -/
  lefschetz : ∀ n : ℕ, 1 ≤ n →
    (pointCount n : ℂ) =
      ∑ i ∈ Finset.range (2 * dim + 1), (-1 : ℂ) ^ i * ∑ j, (root i j) ^ n

/-- The Riemann hypothesis for a zeta datum: every inverse root of Frobenius in
cohomological degree `i` has absolute value `q ^ (i / 2)` (Deligne's theorem, for the
data coming from a smooth projective variety). -/

theorem norm_le_of_powerSum_bound {m : ℕ} (α : Fin m → ℂ) {r C : ℝ} (hr : 0 < r)
    (h : ∀ n : ℕ, 1 ≤ n → ‖∑ j, (α j) ^ n‖ ≤ C * r ^ n) (j₀ : Fin m) : ‖α j₀‖ ≤ r := by
  classical
  by_contra hcon
  push_neg at hcon
  have hne : (Finset.univ : Finset (Fin m)).Nonempty := ⟨j₀, Finset.mem_univ j₀⟩
  set M := Finset.univ.sup' hne (fun j => ‖α j‖) with hMdef
  have hMge : ∀ j, ‖α j‖ ≤ M := by
    intro j; rw [hMdef]; exact Finset.le_sup' (fun j => ‖α j‖) (Finset.mem_univ j)
  have hrM : r < M := lt_of_lt_of_le hcon (hMge j₀)
  have hM0 : 0 < M := lt_trans hr hrM
  set A := Finset.univ.filter (fun j => ‖α j‖ = M) with hAdef
  have hAne : A.Nonempty := by
    obtain ⟨i, -, hi⟩ := Finset.exists_mem_eq_sup' hne (fun j => ‖α j‖)
    exact ⟨i, by simp [hAdef, ← hMdef, ← hi]⟩
  set k : ℝ := (A.card : ℝ) with hkdef
  have hk1 : (1 : ℝ) ≤ k := by
    have := Finset.card_pos.2 hAne
    rw [hkdef]; exact_mod_cast this
  set ρ := Finset.univ.sup' hne (fun j => if ‖α j‖ = M then 0 else ‖α j‖) with hρdef
  have hρM : ρ < M := by
    rw [hρdef, Finset.sup'_lt_iff]
    intro i _
    by_cases hi : ‖α i‖ = M
    · simpa [hi] using hM0
    · simp only [hi, if_false]
      exact lt_of_le_of_ne (hMge i) hi
  have hρ0 : 0 ≤ ρ := by
    rw [hρdef]
    refine le_trans ?_
      (Finset.le_sup' (fun j => if ‖α j‖ = M then 0 else ‖α j‖) (Finset.mem_univ j₀))
    positivity
  have hnotA : ∀ j, j ∉ A → ‖α j‖ ≤ ρ := by
    intro j hj
    have hjne : ‖α j‖ ≠ M := by simpa [hAdef] using hj
    have := Finset.le_sup' (fun j => if ‖α j‖ = M then 0 else ‖α j‖) (Finset.mem_univ j)
    simpa [hjne, ← hρdef] using this
  set β : Fin m → ℂ := fun j => if ‖α j‖ = M then α j / (M : ℂ) else 1 with hβdef
  have hβ1 : ∀ j, ‖β j‖ = 1 := by
    intro j
    by_cases hj : ‖α j‖ = M
    · simp only [hβdef, if_pos hj, norm_div, Complex.norm_real, Real.norm_eq_abs,
        abs_of_pos hM0, hj]
      field_simp
    · simp [hβdef, hj]
  have hαβ : ∀ j ∈ A, α j = (M : ℂ) * β j := by
    intro j hj
    have hjm : ‖α j‖ = M := by simpa [hAdef] using hj
    have hM' : (M : ℂ) ≠ 0 := by exact_mod_cast hM0.ne'
    simp only [hβdef, if_pos hjm]
    field_simp
  have hlim1 : Tendsto (fun n : ℕ => (m : ℝ) * (ρ / M) ^ n) atTop (nhds 0) := by
    have := tendsto_pow_atTop_nhds_zero_of_lt_one (r := ρ / M) (by positivity)
      ((div_lt_one hM0).2 hρM)
    simpa using this.const_mul (m : ℝ)
  have hlim2 : Tendsto (fun n : ℕ => (|C| + 1) * (r / M) ^ n) atTop (nhds 0) := by
    have := tendsto_pow_atTop_nhds_zero_of_lt_one (r := r / M) (by positivity)
      ((div_lt_one hM0).2 hrM)
    simpa using this.const_mul (|C| + 1)
  have hk4 : (0 : ℝ) < k / 4 := by linarith
  obtain ⟨N₁, hN₁⟩ := (hlim1.eventually (gt_mem_nhds hk4)).exists_forall_of_atTop
  obtain ⟨N₂, hN₂⟩ := (hlim2.eventually (gt_mem_nhds hk4)).exists_forall_of_atTop
  obtain ⟨n, hnN, hn1, hnclose⟩ :=
    exists_pow_near_one β hβ1 (ε := 1 / 2) (by norm_num) (max N₁ N₂)
  have hMn : (0 : ℝ) < M ^ n := by positivity
  have hA : k / 2 * M ^ n ≤ ‖∑ j ∈ A, α j ^ n‖ := by
    have h1 : ∑ j ∈ A, α j ^ n = (M : ℂ) ^ n * ∑ j ∈ A, β j ^ n := by
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl (fun j hj => by rw [hαβ j hj, mul_pow])
    have h2 : ∑ j ∈ A, β j ^ n = (A.card : ℂ) + ∑ j ∈ A, (β j ^ n - 1) := by
      rw [Finset.sum_sub_distrib]; simp
    have h3 : ‖∑ j ∈ A, (β j ^ n - 1)‖ ≤ k * (1 / 2) := by
      calc ‖∑ j ∈ A, (β j ^ n - 1)‖ ≤ ∑ j ∈ A, ‖β j ^ n - 1‖ := norm_sum_le _ _
      _ ≤ ∑ j ∈ A, (1 / 2 : ℝ) := Finset.sum_le_sum (fun j _ => (hnclose j).le)
      _ = k * (1 / 2) := by simp [hkdef]
    have h4 : k / 2 ≤ ‖∑ j ∈ A, β j ^ n‖ := by
      have hge := norm_sub_norm_le_norm_add (A.card : ℂ) (∑ j ∈ A, (β j ^ n - 1))
      rw [h2]
      simp only [Complex.norm_natCast] at hge
      rw [hkdef]; linarith
    calc k / 2 * M ^ n ≤ ‖∑ j ∈ A, β j ^ n‖ * M ^ n :=
          mul_le_mul_of_nonneg_right h4 (by positivity)
    _ = ‖∑ j ∈ A, α j ^ n‖ := by
        rw [h1, norm_mul, norm_pow, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hM0,
          mul_comm]
  have hB : ‖∑ j ∈ Finset.univ.filter (fun j => ¬ ‖α j‖ = M), α j ^ n‖ ≤ (m : ℝ) * ρ ^ n := by
    calc ‖∑ j ∈ Finset.univ.filter (fun j => ¬ ‖α j‖ = M), α j ^ n‖
        ≤ ∑ j ∈ Finset.univ.filter (fun j => ¬ ‖α j‖ = M), ‖α j ^ n‖ := norm_sum_le _ _
      _ ≤ ∑ j ∈ Finset.univ.filter (fun j => ¬ ‖α j‖ = M), ρ ^ n := by
          refine Finset.sum_le_sum (fun j hj => ?_)
          rw [norm_pow]
          have hjA : j ∉ A := by
            simp only [hAdef, Finset.mem_filter, Finset.mem_univ, true_and]
            exact (Finset.mem_filter.1 hj).2
          exact pow_le_pow_left₀ (norm_nonneg _) (hnotA j hjA) n
      _ ≤ (m : ℝ) * ρ ^ n := by
          rw [Finset.sum_const, nsmul_eq_mul]
          apply mul_le_mul_of_nonneg_right _ (by positivity)
          exact_mod_cast le_trans (Finset.card_filter_le _ _) (by simp)
  have hsplit :=
    Finset.sum_filter_add_sum_filter_not Finset.univ (fun j => ‖α j‖ = M) (fun j => α j ^ n)
  have hlow : k / 2 * M ^ n - (m : ℝ) * ρ ^ n ≤ ‖∑ j, α j ^ n‖ := by
    have hge : ‖∑ j ∈ A, α j ^ n‖
        - ‖∑ j ∈ Finset.univ.filter (fun j => ¬ ‖α j‖ = M), α j ^ n‖ ≤ ‖∑ j, α j ^ n‖ := by
      rw [← hsplit, hAdef]
      exact norm_sub_norm_le_norm_add _ _
    linarith
  have e1 : (m : ℝ) * ρ ^ n < k / 4 * M ^ n := by
    have hb := hN₁ n (le_trans (le_max_left _ _) hnN)
    have hpow : ρ ^ n = (ρ / M) ^ n * M ^ n := by rw [div_pow]; field_simp
    rw [hpow, ← mul_assoc]
    exact mul_lt_mul_of_pos_right hb hMn
  have e2 : C * r ^ n < k / 4 * M ^ n := by
    have hb := hN₂ n (le_trans (le_max_right _ _) hnN)
    have hpow : r ^ n = (r / M) ^ n * M ^ n := by rw [div_pow]; field_simp
    have hCle : C * r ^ n ≤ (|C| + 1) * r ^ n := by
      apply mul_le_mul_of_nonneg_right _ (by positivity)
      have := le_abs_self C; linarith
    calc C * r ^ n ≤ (|C| + 1) * r ^ n := hCle
    _ = ((|C| + 1) * (r / M) ^ n) * M ^ n := by rw [hpow]; ring
    _ < (k / 4) * M ^ n := mul_lt_mul_of_pos_right hb hMn
  have := h n hn1
  linarith

/-!
## Base case: projective space

For `X = ℙ^d` over `𝔽_q` one has `#ℙ^d(𝔽_{q^n}) = ∑ i ≤ d, q ^ (n i)`, the cohomology is
one-dimensional in each even degree `2i ≤ 2d` with Frobenius acting by `q ^ i`, and the
Riemann hypothesis holds: `‖q ^ i‖ = q ^ (2 i / 2)`.
-/

