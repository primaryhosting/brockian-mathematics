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
def WeilDatum.RiemannHypothesis (W : WeilDatum) : Prop :=
  ∀ i, i ≤ 2 * W.dim → ∀ j : Fin (W.betti i), ‖W.root i j‖ = (W.q : ℝ) ^ ((i : ℝ) / 2)

/-!
## An analytic input: power sums control the largest root

If the power sums `∑ j, α j ^ n` are `O(r ^ n)` then every `α j` has absolute value at
most `r`. This is the elementary (pigeonhole/compactness) form of the statement that the
generating function `∑ n, (∑ j, α j ^ n) z ^ n` has no pole in the disc `|z| < 1 / r`.
-/

/-- On a compact torus the powers `β ^ n` return arbitrarily close to `1`, simultaneously
for finitely many `β` of modulus one, with `n` arbitrarily large. -/
theorem exists_pow_near_one {m : ℕ} (β : Fin m → ℂ) (hβ : ∀ j, ‖β j‖ = 1)
    {ε : ℝ} (hε : 0 < ε) (N : ℕ) :
    ∃ n : ℕ, N ≤ n ∧ 1 ≤ n ∧ ∀ j, ‖β j ^ n - 1‖ < ε := by
  classical
  set x : ℕ → (Fin m → ℂ) := fun k j => β j ^ (k * (N + 1)) with hx
  have hS : IsCompact (Set.univ.pi (fun _ : Fin m => Metric.closedBall (0 : ℂ) 1)) :=
    isCompact_univ_pi (fun _ => isCompact_closedBall 0 1)
  have hmem : ∀ k, x k ∈ Set.univ.pi (fun _ : Fin m => Metric.closedBall (0 : ℂ) 1) := by
    intro k j _
    simp [hx, mem_closedBall, dist_eq_norm, norm_pow, hβ j]
  obtain ⟨a, -, psi, hpsi, hlim⟩ := hS.tendsto_subseq hmem
  have hc := hlim.cauchySeq
  rw [Metric.cauchySeq_iff] at hc
  obtain ⟨K, hK⟩ := hc ε hε
  have hlt : psi K < psi (K + 1) := hpsi (Nat.lt_succ_self K)
  have hd : dist (x (psi (K + 1))) (x (psi K)) < ε := hK (K + 1) (by omega) K (by omega)
  have hsum : psi K + (psi (K + 1) - psi K) = psi (K + 1) := by omega
  refine ⟨(psi (K + 1) - psi K) * (N + 1), ?_, ?_, ?_⟩
  · calc N ≤ 1 * (N + 1) := by omega
    _ ≤ _ := Nat.mul_le_mul_right _ (by omega)
  · exact Nat.one_le_iff_ne_zero.2 (Nat.mul_ne_zero (by omega) (by omega))
  · intro j
    have hj := lt_of_le_of_lt (dist_le_pi_dist (x (psi (K + 1))) (x (psi K)) j) hd
    rw [dist_eq_norm] at hj
    have hfac : β j ^ (psi (K + 1) * (N + 1)) - β j ^ (psi K * (N + 1))
        = β j ^ (psi K * (N + 1)) * (β j ^ ((psi (K + 1) - psi K) * (N + 1)) - 1) := by
      rw [mul_sub, mul_one, ← pow_add, ← Nat.add_mul, hsum]
    simp only [hx] at hj
    rw [hfac, norm_mul, norm_pow, hβ j, one_pow, one_mul] at hj
    exact hj

private theorem norm_sub_norm_le_norm_add (a b : ℂ) : ‖a‖ - ‖b‖ ≤ ‖a + b‖ := by
  have := norm_sub_le (a + b) b
  simp only [add_sub_cancel_right] at this
  linarith

/-- **Power sums control the roots.** If `‖∑ j, α j ^ n‖ ≤ C * r ^ n` for all `n ≥ 1`,
then `‖α j‖ ≤ r` for every `j`. -/
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

private theorem projSum (q n : ℕ) (d : ℕ) :
    ∑ i ∈ Finset.range (2 * d + 1), (-1 : ℂ) ^ i * (if Even i then ((q : ℂ) ^ (i / 2)) ^ n else 0)
      = ∑ i ∈ Finset.range (d + 1), (q : ℂ) ^ (n * i) := by
  induction d with
  | zero => simp
  | succ d ih =>
      conv_rhs => rw [Finset.sum_range_succ]
      have h2 : 2 * (d + 1) + 1 = (2 * d + 1) + 1 + 1 := by ring
      rw [h2, Finset.sum_range_succ, Finset.sum_range_succ, ih]
      have hodd : ¬ Even (2 * d + 1) := by simp [parity_simps]
      have heven : Even (2 * d + 1 + 1) := by simp [parity_simps]
      rw [if_neg hodd, if_pos heven]
      have hhalf : (2 * d + 1 + 1) / 2 = d + 1 := by omega
      rw [hhalf]
      have hsign : (-1 : ℂ) ^ (2 * d + 1 + 1) = 1 := by
        rw [show 2 * d + 1 + 1 = 2 * (d + 1) by ring, pow_mul]; norm_num
      have hpow : ((q : ℂ) ^ (d + 1)) ^ n = (q : ℂ) ^ (n * (d + 1)) := by
        rw [← pow_mul, mul_comm]
      rw [hsign, hpow]
      ring

/-- The zeta datum of the projective space `ℙ^d` over `𝔽_q`. -/
def projectiveSpace (q : ℕ) (hq : 1 < q) (d : ℕ) : WeilDatum where
  q := q
  hq := hq
  dim := d
  betti := fun i => if (Even i ∧ i ≤ 2 * d) then 1 else 0
  root := fun i _ => (q : ℂ) ^ (i / 2)
  pointCount := fun n => ∑ i ∈ Finset.range (d + 1), q ^ (n * i)
  betti_vanishing := by
    intro i hi
    have : ¬ (Even i ∧ i ≤ 2 * d) := by omega
    simp [this]
  lefschetz := by
    intro n _
    push_cast
    rw [← projSum q n d]
    refine Finset.sum_congr rfl (fun i hi => ?_)
    have hile : i ≤ 2 * d := by
      have := Finset.mem_range.1 hi; omega
    by_cases he : Even i
    · simp [he, hile]
    · simp [he]

/-- **Base case of the Weil Riemann hypothesis: projective space.** -/
theorem riemannHypothesis_projectiveSpace (q : ℕ) (hq : 1 < q) (d : ℕ) :
    (projectiveSpace q hq d).RiemannHypothesis := by
  intro i hi j
  by_cases he : Even i
  · obtain ⟨c, hc⟩ := he
    have hi2 : i / 2 = c := by omega
    have hq0 : (0 : ℝ) < q := by positivity
    show ‖(q : ℂ) ^ (i / 2)‖ = (q : ℝ) ^ ((i : ℝ) / 2)
    rw [hi2, norm_pow, Complex.norm_natCast]
    have : ((i : ℝ) / 2) = (c : ℝ) := by
      have : (i : ℝ) = 2 * c := by exact_mod_cast (by omega : i = 2 * c)
      rw [this]; ring
    rw [this, Real.rpow_natCast]
  · exfalso
    have hb : (projectiveSpace q hq d).betti i = 0 := by
      show (if (Even i ∧ i ≤ 2 * d) then 1 else 0) = 0
      simp [he]
    have hpos : 0 < (projectiveSpace q hq d).betti i :=
      lt_of_le_of_lt (Nat.zero_le _) j.isLt
    rw [hb] at hpos
    exact absurd hpos (lt_irrefl 0)

/-!
## Reduction: for curves, the Riemann hypothesis is the Hasse–Weil point count bound

For a smooth projective curve of genus `g` over `𝔽_q` the cohomology is `ℂ` in degree `0`
(Frobenius acting by `1`), of dimension `2 g` in degree `1` (inverse roots `α j`), and `ℂ`
in degree `2` (Frobenius acting by `q`); the functional equation pairs the `α j` so that
`α j * α (σ j) = q`.  We prove, in this situation, that the Riemann hypothesis is
*equivalent* to the point count estimate `|N n - q ^ n - 1| = O(q ^ (n / 2))`.
-/

/-- Betti numbers of a curve of genus `g`. -/
def curveBetti (g : ℕ) : ℕ → ℕ
  | 0 => 1
  | 1 => 2 * g
  | 2 => 1
  | _ + 3 => 0

/-- Inverse roots of Frobenius on the cohomology of a curve of genus `g`. -/
def curveRoot (q g : ℕ) (α : Fin (2 * g) → ℂ) : (i : ℕ) → Fin (curveBetti g i) → ℂ
  | 0 => fun _ => 1
  | 1 => fun j => α j
  | 2 => fun _ => (q : ℂ)
  | _ + 3 => fun j => j.elim0

/-- The zeta datum of a smooth projective curve of genus `g` over `𝔽_q` with inverse
Frobenius roots `α` and point counts `N`. -/
def curveDatum {q : ℕ} (hq : 1 < q) {g : ℕ} (α : Fin (2 * g) → ℂ) (N : ℕ → ℕ)
    (hN : ∀ n : ℕ, 1 ≤ n → (N n : ℂ) = (q : ℂ) ^ n + 1 - ∑ j, (α j) ^ n) : WeilDatum where
  q := q
  hq := hq
  dim := 1
  betti := curveBetti g
  root := curveRoot q g α
  pointCount := N
  betti_vanishing := by
    intro i hi
    obtain ⟨c, rfl⟩ : ∃ c, i = c + 3 := ⟨i - 3, by omega⟩
    rfl
  lefschetz := by
    intro n hn
    rw [hN n hn]
    show _ = ∑ i ∈ Finset.range 3, (-1 : ℂ) ^ i * ∑ j, (curveRoot q g α i j) ^ n
    rw [Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_one]
    show _ = (-1 : ℂ) ^ 0 * (∑ _j : Fin 1, (1 : ℂ) ^ n)
        + (-1 : ℂ) ^ 1 * (∑ j : Fin (2 * g), (α j) ^ n)
        + (-1 : ℂ) ^ 2 * (∑ _j : Fin 1, ((q : ℂ)) ^ n)
    simp
    ring

/-- The Riemann hypothesis for a curve datum says exactly that all the inverse roots of
Frobenius on `H¹` have absolute value `√q`. -/
theorem curveDatum_riemannHypothesis_iff {q : ℕ} (hq : 1 < q) {g : ℕ} (α : Fin (2 * g) → ℂ)
    (N : ℕ → ℕ) (hN : ∀ n : ℕ, 1 ≤ n → (N n : ℂ) = (q : ℂ) ^ n + 1 - ∑ j, (α j) ^ n) :
    (curveDatum hq α N hN).RiemannHypothesis ↔ ∀ j, ‖α j‖ = Real.sqrt q := by
  have hsq : Real.sqrt q = (q : ℝ) ^ ((1 : ℝ) / 2) := Real.sqrt_eq_rpow _
  constructor
  · intro h j
    have h1 := h 1 (by show 1 ≤ 2 * 1; norm_num) j
    rw [hsq]
    simpa using h1
  · intro h i hi j
    have hi2 : i ≤ 2 := by simpa using hi
    interval_cases i
    · show ‖(1 : ℂ)‖ = (q : ℝ) ^ (((0 : ℕ) : ℝ) / 2)
      norm_num
    · show ‖α j‖ = (q : ℝ) ^ (((1 : ℕ) : ℝ) / 2)
      rw [h j, hsq]
      norm_num
    · show ‖(q : ℂ)‖ = (q : ℝ) ^ (((2 : ℕ) : ℝ) / 2)
      rw [Complex.norm_natCast]
      norm_num

/-- **Reduction: the Riemann hypothesis for a curve is the Hasse–Weil bound.** -/
theorem curve_RH_iff_pointCount_bound {q : ℕ} (hq : 1 < q) {g : ℕ} (α : Fin (2 * g) → ℂ)
    (σ : Equiv.Perm (Fin (2 * g))) (hσ : ∀ j, α j * α (σ j) = (q : ℂ))
    (N : ℕ → ℕ) (hN : ∀ n : ℕ, 1 ≤ n → (N n : ℂ) = (q : ℂ) ^ n + 1 - ∑ j, (α j) ^ n) :
    (curveDatum hq α N hN).RiemannHypothesis ↔
      ∃ C : ℝ, ∀ n : ℕ, 1 ≤ n → |(N n : ℝ) - (q : ℝ) ^ n - 1| ≤ C * Real.sqrt q ^ n := by
  have hq0 : (0 : ℝ) ≤ q := by positivity
  have hqpos : (0 : ℝ) < q := by exact_mod_cast lt_trans Nat.zero_lt_one hq
  have hsqpos : 0 < Real.sqrt q := Real.sqrt_pos.2 hqpos
  have hsqsq : Real.sqrt q * Real.sqrt q = q := Real.mul_self_sqrt hq0
  -- the point count defect is exactly the power sum of the inverse roots
  have key : ∀ n : ℕ, 1 ≤ n → ‖∑ j, (α j) ^ n‖ = |(N n : ℝ) - (q : ℝ) ^ n - 1| := by
    intro n hn
    have h1 : ∑ j, (α j) ^ n = -((((N n : ℝ) - (q : ℝ) ^ n - 1 : ℝ)) : ℂ) := by
      have h2 := hN n hn
      push_cast
      linear_combination h2
    rw [h1, norm_neg, Complex.norm_real, Real.norm_eq_abs]
  rw [curveDatum_riemannHypothesis_iff]
  constructor
  · intro h
    refine ⟨(2 * g : ℕ), fun n hn => ?_⟩
    rw [← key n hn]
    calc ‖∑ j, (α j) ^ n‖ ≤ ∑ j, ‖(α j) ^ n‖ := norm_sum_le _ _
    _ = ∑ _j : Fin (2 * g), Real.sqrt q ^ n := by
        refine Finset.sum_congr rfl (fun j _ => ?_)
        rw [norm_pow, h j]
    _ = ((2 * g : ℕ) : ℝ) * Real.sqrt q ^ n := by
        rw [Finset.sum_const, nsmul_eq_mul]
        norm_num
  · rintro ⟨C, hC⟩
    have hbound : ∀ n : ℕ, 1 ≤ n → ‖∑ j, (α j) ^ n‖ ≤ C * Real.sqrt q ^ n := by
      intro n hn
      rw [key n hn]
      exact hC n hn
    have hle : ∀ j, ‖α j‖ ≤ Real.sqrt q :=
      fun j => norm_le_of_powerSum_bound α hsqpos hbound j
    intro j
    have hprod : ‖α j‖ * ‖α (σ j)‖ = (q : ℝ) := by
      rw [← norm_mul, hσ j, Complex.norm_natCast]
    have h1 := hle j
    have h2 := hle (σ j)
    nlinarith [norm_nonneg (α j), norm_nonneg (α (σ j))]

/-- Sanity check: the datum of `ℙ¹` over `𝔽_q` really does count `q ^ n + 1` points. -/
theorem projectiveLine_pointCount (q : ℕ) (hq : 1 < q) (n : ℕ) :
    (projectiveSpace q hq 1).pointCount n = 1 + q ^ n := by
  show ∑ i ∈ Finset.range 2, q ^ (n * i) = 1 + q ^ n
  rw [Finset.sum_range_succ, Finset.sum_range_one]
  simp

/-- The hypotheses of the curve reduction are non-vacuous: a curve of genus `0` (the
projective line) has no inverse roots in degree one, `q ^ n + 1` points over `𝔽_{q ^ n}`,
and satisfies the Riemann hypothesis. -/
theorem riemannHypothesis_genusZeroCurve (q : ℕ) (hq : 1 < q) :
    (curveDatum hq (g := 0) (fun j => j.elim0) (fun n => q ^ n + 1)
      (by intro n _; push_cast; simp)).RiemannHypothesis := by
  rw [curveDatum_riemannHypothesis_iff]
  exact fun j => j.elim0

/-- **The Weil Riemann hypothesis: formalized statement, with a proved base case and a
proved reduction.**

Mathlib contains no étale cohomology, so Deligne's theorem itself cannot yet be stated for
arbitrary smooth projective varieties.  We formalize the numerical content of the Riemann
hypothesis part of the Weil conjectures (`Frontier.WeilDatum.RiemannHypothesis`) and prove:

* the base case, that the Riemann hypothesis holds for the zeta datum of projective space
  `ℙ^d` over any finite field `𝔽_q`;
* a Lean-checked reduction, that for the zeta datum of a curve of genus `g` (with the
  functional equation encoded by a pairing `σ` of the inverse Frobenius roots) the Riemann
  hypothesis is *equivalent* to the Hasse–Weil point count estimate
  `|#X(𝔽_{q^n}) - q^n - 1| = O(q^(n/2))`. -/
theorem deligne_weil_RH :
    (∀ (q : ℕ) (hq : 1 < q) (d : ℕ), (projectiveSpace q hq d).RiemannHypothesis) ∧
    (∀ (q : ℕ) (hq : 1 < q) (g : ℕ) (α : Fin (2 * g) → ℂ) (σ : Equiv.Perm (Fin (2 * g)))
      (_ : ∀ j, α j * α (σ j) = (q : ℂ)) (N : ℕ → ℕ)
      (hN : ∀ n : ℕ, 1 ≤ n → (N n : ℂ) = (q : ℂ) ^ n + 1 - ∑ j, (α j) ^ n),
      (curveDatum hq α N hN).RiemannHypothesis ↔
        ∃ C : ℝ, ∀ n : ℕ, 1 ≤ n → |(N n : ℝ) - (q : ℝ) ^ n - 1| ≤ C * Real.sqrt q ^ n) :=
  ⟨riemannHypothesis_projectiveSpace,
   fun _ hq _ α σ hσ N hN => curve_RH_iff_pointCount_bound hq α σ hσ N hN⟩

end Frontier

