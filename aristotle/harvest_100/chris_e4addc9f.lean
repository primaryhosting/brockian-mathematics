/-
# Sato Tate
Category: Frontier Math
Target: Math2.sato_tate
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/
import Mathlib

/-!
# Sato Tate
Category: Frontier Math
Target: Math2.sato_tate
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open Filter Topology Set MeasureTheory intervalIntegral
open scoped Real

namespace Math2

/-- The Sato–Tate density on `[0, π]`: `θ ↦ (2/π) sin²θ`. -/
noncomputable def satoTateDensity (x : ℝ) : ℝ := 2 / Real.pi * Real.sin x ^ 2

/-- The finset of primes `< X`. -/
def primesBelow (X : ℕ) : Finset ℕ := (Finset.range X).filter Nat.Prime

/-- The Frobenius angle `θ_p ∈ [0, π]` attached to a trace of Frobenius `a_p` at a prime `p`:
the unique angle with `a_p = 2 √p cos θ_p` (well defined by the Hasse bound `|a_p| ≤ 2√p`). -/
noncomputable def frobeniusAngle (p : ℕ) (a : ℤ) : ℝ :=
  Real.arccos ((a : ℝ) / (2 * Real.sqrt p))

lemma frobeniusAngle_mem_Icc (p : ℕ) (a : ℤ) : frobeniusAngle p a ∈ Icc 0 Real.pi :=
  ⟨Real.arccos_nonneg _, Real.arccos_le_pi _⟩

/-- The defining property of the Frobenius angle: under the Hasse bound `|a_p| ≤ 2√p`
we indeed have `a_p = 2 √p cos θ_p`. -/
lemma cos_frobeniusAngle {p : ℕ} {a : ℤ} (hp : 0 < p) (hasse : |(a : ℝ)| ≤ 2 * Real.sqrt p) :
    2 * Real.sqrt p * Real.cos (frobeniusAngle p a) = (a : ℝ) := by
  have hs : 0 < Real.sqrt p := Real.sqrt_pos.2 (by exact_mod_cast hp)
  have h2 : (0 : ℝ) < 2 * Real.sqrt p := by linarith
  have habs : |(a : ℝ) / (2 * Real.sqrt p)| ≤ 1 := by
    rw [abs_div, abs_of_pos h2, div_le_one h2]
    exact hasse
  rw [abs_le] at habs
  rw [frobeniusAngle, Real.cos_arccos habs.1 habs.2]
  field_simp

/-- The Sato–Tate equidistribution property for a sequence of angles `θ` indexed by primes:
for every continuous test function `f`, the average of `f (θ p)` over the primes `p < X`
converges, as `X → ∞`, to `∫₀^π f(x) (2/π) sin²x dx`. -/
def SatoTateEquidistributed (θ : ℕ → ℝ) : Prop :=
  ∀ f : ℝ → ℝ, Continuous f →
    Tendsto (fun X : ℕ => (∑ p ∈ primesBelow X, f (θ p)) / (primesBelow X).card)
      atTop (𝓝 (∫ x in (0 : ℝ)..Real.pi, satoTateDensity x * f x))

/-! ### Basic properties of the Sato–Tate density -/

lemma satoTateDensity_nonneg (x : ℝ) : 0 ≤ satoTateDensity x := by
  have := Real.pi_pos
  unfold satoTateDensity
  positivity

lemma satoTateDensity_le (x : ℝ) : satoTateDensity x ≤ 2 / Real.pi := by
  have hp := Real.pi_pos
  have h1 : Real.sin x ^ 2 ≤ 1 := by nlinarith [Real.neg_one_le_sin x, Real.sin_le_one x]
  have h2 : 0 < 2 / Real.pi := by positivity
  unfold satoTateDensity
  nlinarith

lemma continuous_satoTateDensity : Continuous satoTateDensity := by
  unfold satoTateDensity; fun_prop

/-- The Sato–Tate density is a probability density on `[0, π]`. -/
theorem integral_satoTateDensity : ∫ x in (0 : ℝ)..Real.pi, satoTateDensity x = 1 := by
  have hp := Real.pi_pos
  unfold satoTateDensity
  rw [intervalIntegral.integral_const_mul, integral_sin_sq]
  simp

lemma integral_density_mul_nonneg {u v : ℝ} (huv : u ≤ v) {φ : ℝ → ℝ}
    (hφ0 : ∀ x, 0 ≤ φ x) : 0 ≤ ∫ x in u..v, satoTateDensity x * φ x :=
  intervalIntegral.integral_nonneg huv fun x _ =>
    mul_nonneg (satoTateDensity_nonneg x) (hφ0 x)

lemma integral_density_mul_le {u v : ℝ} (huv : u ≤ v) {φ : ℝ → ℝ} (hφ : Continuous φ)
    (hφ1 : ∀ x, φ x ≤ 1) :
    (∫ x in u..v, satoTateDensity x * φ x) ≤ 2 / Real.pi * (v - u) := by
  have h : (∫ x in u..v, satoTateDensity x * φ x) ≤ ∫ _x in u..v, (2 / Real.pi : ℝ) := by
    apply intervalIntegral.integral_mono_on huv
      ((continuous_satoTateDensity.mul hφ).intervalIntegrable _ _)
      (intervalIntegral.intervalIntegrable_const)
    intro x _
    simp only [Pi.mul_apply]
    have h1 := satoTateDensity_le x
    have h2 := satoTateDensity_nonneg x
    nlinarith [hφ1 x]
  rw [intervalIntegral.integral_const, smul_eq_mul] at h
  linarith [h, (by ring : (v - u) * (2 / Real.pi : ℝ) = 2 / Real.pi * (v - u))]

lemma integral_density_le {u v : ℝ} (huv : u ≤ v) :
    (∫ x in u..v, satoTateDensity x) ≤ 2 / Real.pi * (v - u) := by
  have := integral_density_mul_le huv (φ := fun _ => (1 : ℝ)) continuous_const (fun _ => le_rfl)
  simpa using this

/-! ### Trapezoidal approximations of indicator functions -/

/-- A continuous trapezoidal function which is `1` on `[u+ε, v-ε]` and `0` outside `(u, v)`. -/
noncomputable def trap (u v ε : ℝ) (x : ℝ) : ℝ := max 0 (min 1 (min ((x - u) / ε) ((v - x) / ε)))

lemma continuous_trap (u v ε : ℝ) : Continuous (trap u v ε) := by
  unfold trap; fun_prop

lemma trap_nonneg (u v ε x : ℝ) : 0 ≤ trap u v ε x := le_max_left _ _

lemma trap_le_one (u v ε x : ℝ) : trap u v ε x ≤ 1 :=
  max_le zero_le_one (min_le_left _ _)

lemma trap_eq_zero_left {u v ε x : ℝ} (hε : 0 < ε) (hx : x ≤ u) : trap u v ε x = 0 := by
  have h : (x - u) / ε ≤ 0 := div_nonpos_of_nonpos_of_nonneg (by linarith) hε.le
  unfold trap
  exact max_eq_left (le_trans (min_le_right _ _) (le_trans (min_le_left _ _) h))

lemma trap_eq_zero_right {u v ε x : ℝ} (hε : 0 < ε) (hx : v ≤ x) : trap u v ε x = 0 := by
  have h : (v - x) / ε ≤ 0 := div_nonpos_of_nonpos_of_nonneg (by linarith) hε.le
  unfold trap
  exact max_eq_left (le_trans (min_le_right _ _) (le_trans (min_le_right _ _) h))

lemma trap_eq_one {u v ε x : ℝ} (hε : 0 < ε) (h1 : u + ε ≤ x) (h2 : x ≤ v - ε) :
    trap u v ε x = 1 := by
  have ha : (1 : ℝ) ≤ (x - u) / ε := by rw [le_div_iff₀ hε]; linarith
  have hb : (1 : ℝ) ≤ (v - x) / ε := by rw [le_div_iff₀ hε]; linarith
  unfold trap
  rw [min_eq_left (le_min ha hb), max_eq_right zero_le_one]

/-! ### Comparison of the smoothed integrals with the mass of an interval -/

lemma dens_trap_intervalIntegrable (u v ε a b : ℝ) :
    IntervalIntegrable (fun x => satoTateDensity x * trap u v ε x) MeasureTheory.volume a b :=
  (continuous_satoTateDensity.mul (continuous_trap u v ε)).intervalIntegrable _ _

lemma integral_trap_upper {α β ε : ℝ} (hε : 0 < ε) (hαβ : α ≤ β) :
    (∫ x in (0 : ℝ)..Real.pi, satoTateDensity x * trap (α - ε) (β + ε) ε x)
      ≤ (∫ x in α..β, satoTateDensity x) + 4 / Real.pi * ε := by
  set F := fun x => satoTateDensity x * trap (α - ε) (β + ε) ε x with hF
  show (∫ x in (0 : ℝ)..Real.pi, F x) ≤ (∫ x in α..β, satoTateDensity x) + 4 / Real.pi * ε
  set A := min 0 (α - ε) with hA
  set B := max Real.pi (β + ε) with hB
  have hA0 : A ≤ 0 := min_le_left _ _
  have hAae : A ≤ α - ε := min_le_right _ _
  have hBpi : Real.pi ≤ B := le_max_left _ _
  have hBbe : β + ε ≤ B := le_max_right _ _
  have step1 : (∫ x in (0 : ℝ)..Real.pi, F x) ≤ ∫ x in A..B, F x := by
    have h1 : (∫ x in A..(0 : ℝ), F x) + (∫ x in (0 : ℝ)..Real.pi, F x) = ∫ x in A..Real.pi, F x :=
      intervalIntegral.integral_add_adjacent_intervals
        (dens_trap_intervalIntegrable _ _ _ _ _) (dens_trap_intervalIntegrable _ _ _ _ _)
    have h2 : (∫ x in A..Real.pi, F x) + (∫ x in Real.pi..B, F x) = ∫ x in A..B, F x :=
      intervalIntegral.integral_add_adjacent_intervals
        (dens_trap_intervalIntegrable _ _ _ _ _) (dens_trap_intervalIntegrable _ _ _ _ _)
    have p1 : 0 ≤ ∫ x in A..(0 : ℝ), F x :=
      integral_density_mul_nonneg hA0 fun x => trap_nonneg _ _ _ x
    have p2 : 0 ≤ ∫ x in Real.pi..B, F x :=
      integral_density_mul_nonneg hBpi fun x => trap_nonneg _ _ _ x
    linarith
  have s1 : (∫ x in A..(α - ε), F x) = 0 := by
    have h : (∫ x in A..(α - ε), F x) = ∫ _x in A..(α - ε), (0 : ℝ) := by
      apply intervalIntegral.integral_congr
      intro x hx
      rw [uIcc_of_le hAae] at hx
      show satoTateDensity x * trap (α - ε) (β + ε) ε x = 0
      rw [trap_eq_zero_left hε hx.2, mul_zero]
    simp [h]
  have s2 : (∫ x in (β + ε)..B, F x) = 0 := by
    have h : (∫ x in (β + ε)..B, F x) = ∫ _x in (β + ε)..B, (0 : ℝ) := by
      apply intervalIntegral.integral_congr
      intro x hx
      rw [uIcc_of_le hBbe] at hx
      show satoTateDensity x * trap (α - ε) (β + ε) ε x = 0
      rw [trap_eq_zero_right hε hx.1, mul_zero]
    simp [h]
  have add1 : (∫ x in A..(α - ε), F x) + (∫ x in (α - ε)..α, F x) = ∫ x in A..α, F x :=
    intervalIntegral.integral_add_adjacent_intervals
      (dens_trap_intervalIntegrable _ _ _ _ _) (dens_trap_intervalIntegrable _ _ _ _ _)
  have add2 : (∫ x in A..α, F x) + (∫ x in α..β, F x) = ∫ x in A..β, F x :=
    intervalIntegral.integral_add_adjacent_intervals
      (dens_trap_intervalIntegrable _ _ _ _ _) (dens_trap_intervalIntegrable _ _ _ _ _)
  have add3 : (∫ x in A..β, F x) + (∫ x in β..(β + ε), F x) = ∫ x in A..(β + ε), F x :=
    intervalIntegral.integral_add_adjacent_intervals
      (dens_trap_intervalIntegrable _ _ _ _ _) (dens_trap_intervalIntegrable _ _ _ _ _)
  have add4 : (∫ x in A..(β + ε), F x) + (∫ x in (β + ε)..B, F x) = ∫ x in A..B, F x :=
    intervalIntegral.integral_add_adjacent_intervals
      (dens_trap_intervalIntegrable _ _ _ _ _) (dens_trap_intervalIntegrable _ _ _ _ _)
  have b1 : (∫ x in (α - ε)..α, F x) ≤ 2 / Real.pi * ε := by
    have := integral_density_mul_le (u := α - ε) (v := α) (by linarith)
      (continuous_trap (α - ε) (β + ε) ε) fun x => trap_le_one _ _ _ x
    simpa using this.trans_eq (by ring)
  have b2 : (∫ x in β..(β + ε), F x) ≤ 2 / Real.pi * ε := by
    have := integral_density_mul_le (u := β) (v := β + ε) (by linarith)
      (continuous_trap (α - ε) (β + ε) ε) fun x => trap_le_one _ _ _ x
    simpa using this.trans_eq (by ring)
  have b3 : (∫ x in α..β, F x) ≤ ∫ x in α..β, satoTateDensity x := by
    apply intervalIntegral.integral_mono_on hαβ (dens_trap_intervalIntegrable _ _ _ _ _)
      (continuous_satoTateDensity.intervalIntegrable _ _)
    intro x _
    have := satoTateDensity_nonneg x
    nlinarith [trap_le_one (α - ε) (β + ε) ε x]
  have hfour : 4 / Real.pi * ε = 2 / Real.pi * ε + 2 / Real.pi * ε := by ring
  linarith

lemma integral_trap_lower {α β ε : ℝ} (hε : 0 < ε) (hα : 0 ≤ α) (hαβ : α ≤ β)
    (hβ : β ≤ Real.pi) :
    (∫ x in α..β, satoTateDensity x) - 4 / Real.pi * ε
      ≤ ∫ x in (0 : ℝ)..Real.pi, satoTateDensity x * trap α β ε x := by
  have hpi : (0 : ℝ) < 2 / Real.pi := by positivity
  set F := fun x => satoTateDensity x * trap α β ε x with hF
  show (∫ x in α..β, satoTateDensity x) - 4 / Real.pi * ε ≤ ∫ x in (0 : ℝ)..Real.pi, F x
  have key : (∫ x in α..β, satoTateDensity x) - 4 / Real.pi * ε ≤ ∫ x in α..β, F x := by
    rcases le_or_gt (β - α) (2 * ε) with hcase | hcase
    · have h0 : 0 ≤ ∫ x in α..β, F x :=
        integral_density_mul_nonneg hαβ fun x => trap_nonneg _ _ _ x
      have h1 : (∫ x in α..β, satoTateDensity x) ≤ 2 / Real.pi * (β - α) :=
        integral_density_le hαβ
      have h2 : 2 / Real.pi * (β - α) ≤ 2 / Real.pi * (2 * ε) :=
        mul_le_mul_of_nonneg_left hcase hpi.le
      have h3 : 2 / Real.pi * (2 * ε) = 4 / Real.pi * ε := by ring
      linarith
    · have hab : α + ε ≤ β - ε := by linarith
      have mid : (∫ x in (α + ε)..(β - ε), F x) = ∫ x in (α + ε)..(β - ε), satoTateDensity x := by
        apply intervalIntegral.integral_congr
        intro x hx
        rw [uIcc_of_le hab] at hx
        show satoTateDensity x * trap α β ε x = satoTateDensity x
        rw [trap_eq_one hε hx.1 hx.2, mul_one]
      have a1 : (∫ x in α..(α + ε), F x) + (∫ x in (α + ε)..β, F x) = ∫ x in α..β, F x :=
        intervalIntegral.integral_add_adjacent_intervals
          (dens_trap_intervalIntegrable _ _ _ _ _) (dens_trap_intervalIntegrable _ _ _ _ _)
      have a2 : (∫ x in (α + ε)..(β - ε), F x) + (∫ x in (β - ε)..β, F x)
          = ∫ x in (α + ε)..β, F x :=
        intervalIntegral.integral_add_adjacent_intervals
          (dens_trap_intervalIntegrable _ _ _ _ _) (dens_trap_intervalIntegrable _ _ _ _ _)
      have d1 : (∫ x in α..(α + ε), satoTateDensity x) + (∫ x in (α + ε)..β, satoTateDensity x)
          = ∫ x in α..β, satoTateDensity x :=
        intervalIntegral.integral_add_adjacent_intervals
          (continuous_satoTateDensity.intervalIntegrable _ _)
          (continuous_satoTateDensity.intervalIntegrable _ _)
      have d2 : (∫ x in (α + ε)..(β - ε), satoTateDensity x)
            + (∫ x in (β - ε)..β, satoTateDensity x) = ∫ x in (α + ε)..β, satoTateDensity x :=
        intervalIntegral.integral_add_adjacent_intervals
          (continuous_satoTateDensity.intervalIntegrable _ _)
          (continuous_satoTateDensity.intervalIntegrable _ _)
      have e1 : (∫ x in α..(α + ε), satoTateDensity x) ≤ 2 / Real.pi * ε := by
        have := integral_density_le (u := α) (v := α + ε) (by linarith)
        simpa using this.trans_eq (by ring)
      have e2 : (∫ x in (β - ε)..β, satoTateDensity x) ≤ 2 / Real.pi * ε := by
        have := integral_density_le (u := β - ε) (v := β) (by linarith)
        simpa using this.trans_eq (by ring)
      have p1 : 0 ≤ ∫ x in α..(α + ε), F x :=
        integral_density_mul_nonneg (by linarith) fun x => trap_nonneg _ _ _ x
      have p2 : 0 ≤ ∫ x in (β - ε)..β, F x :=
        integral_density_mul_nonneg (by linarith) fun x => trap_nonneg _ _ _ x
      have h4 : 4 / Real.pi * ε = 2 / Real.pi * ε + 2 / Real.pi * ε := by ring
      linarith
  have outer1 : 0 ≤ ∫ x in (0 : ℝ)..α, F x :=
    integral_density_mul_nonneg hα fun x => trap_nonneg _ _ _ x
  have outer2 : 0 ≤ ∫ x in β..Real.pi, F x :=
    integral_density_mul_nonneg hβ fun x => trap_nonneg _ _ _ x
  have t1 : (∫ x in (0 : ℝ)..α, F x) + (∫ x in α..β, F x) = ∫ x in (0 : ℝ)..β, F x :=
    intervalIntegral.integral_add_adjacent_intervals
      (dens_trap_intervalIntegrable _ _ _ _ _) (dens_trap_intervalIntegrable _ _ _ _ _)
  have t2 : (∫ x in (0 : ℝ)..β, F x) + (∫ x in β..Real.pi, F x) = ∫ x in (0 : ℝ)..Real.pi, F x :=
    intervalIntegral.integral_add_adjacent_intervals
      (dens_trap_intervalIntegrable _ _ _ _ _) (dens_trap_intervalIntegrable _ _ _ _ _)
  linarith

/-! ### Counting estimates -/

lemma card_le_sum_trap_upper (θ : ℕ → ℝ) (X : ℕ) {α β ε : ℝ} (hε : 0 < ε) :
    ((((primesBelow X).filter fun p => θ p ∈ Icc α β).card : ℝ))
      ≤ ∑ p ∈ primesBelow X, trap (α - ε) (β + ε) ε (θ p) := by
  rw [Finset.card_filter]
  push_cast
  refine Finset.sum_le_sum fun p _ => ?_
  by_cases h : θ p ∈ Icc α β
  · have h1 := trap_eq_one (u := α - ε) (v := β + ε) hε (by simp; exact h.1) (by simp; exact h.2)
    simp [h, h1]
  · simp [h, trap_nonneg]

lemma sum_trap_lower_le_card (θ : ℕ → ℝ) (X : ℕ) {α β ε : ℝ} (hε : 0 < ε) :
    (∑ p ∈ primesBelow X, trap α β ε (θ p))
      ≤ ((((primesBelow X).filter fun p => θ p ∈ Icc α β).card : ℝ)) := by
  rw [Finset.card_filter]
  push_cast
  refine Finset.sum_le_sum fun p _ => ?_
  by_cases h : θ p ∈ Icc α β
  · simp [h, trap_le_one]
  · simp only [Set.mem_Icc, not_and_or, not_le] at h
    rcases h with h | h
    · rw [trap_eq_zero_left hε h.le]; positivity
    · rw [trap_eq_zero_right hε h.le]; positivity

lemma primesBelow_card_pos {X : ℕ} (hX : 3 ≤ X) : 0 < (primesBelow X).card :=
  Finset.card_pos.2 ⟨2, by simp [primesBelow, Nat.prime_two]; omega⟩

/-! ### The main equidistribution statement -/

/-- From equidistribution against continuous test functions we obtain equidistribution
against intervals: the proportion of primes `p < X` whose Frobenius angle lies in `[α, β]`
converges to the Sato–Tate mass of `[α, β]`. -/
theorem satoTate_interval {θ : ℕ → ℝ} (hST : SatoTateEquidistributed θ)
    {α β : ℝ} (hα : 0 ≤ α) (hαβ : α ≤ β) (hβ : β ≤ Real.pi) :
    Tendsto
      (fun X : ℕ => ((((primesBelow X).filter fun p => θ p ∈ Icc α β).card : ℝ))
        / (primesBelow X).card)
      atTop (𝓝 (∫ x in α..β, satoTateDensity x)) := by
  have hpi := Real.pi_pos
  rw [Metric.tendsto_atTop]
  intro δ hδ
  set L := ∫ x in α..β, satoTateDensity x with hL
  set ε : ℝ := δ * Real.pi / 32 with hεdef
  have hε : 0 < ε := by positivity
  have hεsmall : 4 / Real.pi * ε = δ / 8 := by
    rw [hεdef]; field_simp; ring
  -- the two continuous test functions
  have hg := hST (trap (α - ε) (β + ε) ε) (continuous_trap _ _ _)
  have hf := hST (trap α β ε) (continuous_trap _ _ _)
  rw [Metric.tendsto_atTop] at hg hf
  obtain ⟨N₁, hN₁⟩ := hg (δ / 4) (by linarith)
  obtain ⟨N₂, hN₂⟩ := hf (δ / 4) (by linarith)
  refine ⟨max (max N₁ N₂) 3, fun X hX => ?_⟩
  have hX₁ : N₁ ≤ X := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hX
  have hX₂ : N₂ ≤ X := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hX
  have hX₃ : 3 ≤ X := le_trans (le_max_right _ _) hX
  have hP : (0 : ℝ) < (primesBelow X).card := by
    exact_mod_cast primesBelow_card_pos hX₃
  have hgX := hN₁ X hX₁
  have hfX := hN₂ X hX₂
  rw [Real.dist_eq, abs_lt] at hgX hfX
  -- counting sandwich
  have hup : ((((primesBelow X).filter fun p => θ p ∈ Icc α β).card : ℝ)) / (primesBelow X).card
      ≤ (∑ p ∈ primesBelow X, trap (α - ε) (β + ε) ε (θ p)) / (primesBelow X).card := by
    gcongr
    exact card_le_sum_trap_upper θ X hε
  have hlow : (∑ p ∈ primesBelow X, trap α β ε (θ p)) / (primesBelow X).card
      ≤ ((((primesBelow X).filter fun p => θ p ∈ Icc α β).card : ℝ)) / (primesBelow X).card := by
    gcongr
    exact sum_trap_lower_le_card θ X hε
  have hIup := integral_trap_upper hε hαβ
  have hIlow := integral_trap_lower hε hα hαβ hβ
  rw [Real.dist_eq, abs_lt]
  constructor <;> linarith

/-- **Sato–Tate.**  Let `E` be an elliptic curve over `ℚ` without complex multiplication and,
for each prime `p` of good reduction, let `a p` be the trace of Frobenius, so that the
Frobenius angle is `θ_p = arccos (a_p / (2 √p)) ∈ [0, π]`.  The Sato–Tate theorem
(Clozel–Harris–Shepherd-Barron–Taylor) asserts that these angles are equidistributed with
respect to the measure `(2/π) sin²θ dθ`; this is the hypothesis `hST`.

The conclusion is the distributional form of the statement: for every subinterval
`[α, β] ⊆ [0, π]`, the density of primes whose Frobenius angle lies in `[α, β]` equals
`(2/π) ∫_α^β sin²x dx`.

The hypothesis is no stronger than the conclusion: by `Math2.satoTate_iff_intervals` the
test-function form `SatoTateEquidistributed` and the interval form `SatoTateIntervals`
are equivalent for angles in `[0, π]`. -/
theorem sato_tate (a : ℕ → ℤ)
    (hST : SatoTateEquidistributed fun p => frobeniusAngle p (a p))
    {α β : ℝ} (hα : 0 ≤ α) (hαβ : α ≤ β) (hβ : β ≤ Real.pi) :
    Tendsto
      (fun X : ℕ =>
        ((((primesBelow X).filter fun p => frobeniusAngle p (a p) ∈ Icc α β).card : ℝ))
          / (primesBelow X).card)
      atTop (𝓝 (2 / Real.pi * ∫ x in α..β, Real.sin x ^ 2)) := by
  have h := satoTate_interval hST hα hαβ hβ
  simpa [satoTateDensity, intervalIntegral.integral_const_mul] using h


/-! ### The interval form implies equidistribution against continuous test functions

We show that the two formulations of Sato–Tate equidistribution are equivalent, so that the
hypothesis used in `Math2.sato_tate` is exactly as strong as its conclusion. -/

/-- The interval (distribution-function) form of Sato–Tate equidistribution. -/
def SatoTateIntervals (θ : ℕ → ℝ) : Prop :=
  ∀ α β : ℝ, 0 ≤ α → α ≤ β → β ≤ Real.pi →
    Tendsto
      (fun X : ℕ => ((((primesBelow X).filter fun p => θ p ∈ Icc α β).card : ℝ))
        / (primesBelow X).card)
      atTop (𝓝 (∫ x in α..β, satoTateDensity x))

lemma abel_sum_aux (g M : ℕ → ℝ) (n : ℕ) (hM0 : M 0 = 0) :
    (∑ j ∈ Finset.range n, (g j - g (j + 1)) * M j) + g n * M n
      = ∑ j ∈ Finset.range n, g (j + 1) * (M (j + 1) - M j) := by
  induction n with
  | zero => simp [hM0]
  | succ n ih =>
      rw [Finset.sum_range_succ, Finset.sum_range_succ]
      linarith [ih]

lemma integral_split_grid (t : ℕ → ℝ) (F : ℝ → ℝ) (hF : Continuous F) (n : ℕ) :
    (∑ j ∈ Finset.range n, ∫ x in (t j)..(t (j + 1)), F x) = ∫ x in (t 0)..(t n), F x := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [Finset.sum_range_succ, ih]
      exact intervalIntegral.integral_add_adjacent_intervals
        (hF.intervalIntegrable _ _) (hF.intervalIntegrable _ _)

lemma cell_bound {u v : ℝ} (huv : u ≤ v) {f : ℝ → ℝ} (hf : Continuous f) {y c : ℝ}
    (h : ∀ x ∈ Icc u v, |f y - f x| ≤ c) :
    |f y * (∫ x in u..v, satoTateDensity x) - ∫ x in u..v, satoTateDensity x * f x|
      ≤ c * ∫ x in u..v, satoTateDensity x := by
  have hint1 : IntervalIntegrable (fun x => satoTateDensity x * f y) MeasureTheory.volume u v :=
    (continuous_satoTateDensity.mul continuous_const).intervalIntegrable _ _
  have hint2 : IntervalIntegrable (fun x => satoTateDensity x * f x) MeasureTheory.volume u v :=
    (continuous_satoTateDensity.mul hf).intervalIntegrable _ _
  have e1 : f y * (∫ x in u..v, satoTateDensity x) = ∫ x in u..v, satoTateDensity x * f y := by
    rw [intervalIntegral.integral_mul_const]; ring
  have e2 : (∫ x in u..v, satoTateDensity x * f y) - (∫ x in u..v, satoTateDensity x * f x)
      = ∫ x in u..v, (satoTateDensity x * f y - satoTateDensity x * f x) :=
    (intervalIntegral.integral_sub hint1 hint2).symm
  rw [e1, e2]
  have habs : |∫ x in u..v, (satoTateDensity x * f y - satoTateDensity x * f x)|
      ≤ ∫ x in u..v, |satoTateDensity x * f y - satoTateDensity x * f x| :=
    intervalIntegral.abs_integral_le_integral_abs huv
  have hmono : (∫ x in u..v, |satoTateDensity x * f y - satoTateDensity x * f x|)
      ≤ ∫ x in u..v, satoTateDensity x * c := by
    apply intervalIntegral.integral_mono_on huv (hint1.sub hint2).abs
      ((continuous_satoTateDensity.mul continuous_const).intervalIntegrable _ _)
    intro x hx
    have hd := satoTateDensity_nonneg x
    have habs' : |satoTateDensity x * f y - satoTateDensity x * f x|
        = satoTateDensity x * |f y - f x| := by
      rw [← mul_sub, abs_mul, abs_of_nonneg hd]
    rw [habs']
    exact mul_le_mul_of_nonneg_left (h x hx) hd
  rw [intervalIntegral.integral_mul_const] at hmono
  calc |∫ x in u..v, (satoTateDensity x * f y - satoTateDensity x * f x)| ≤ _ := habs
    _ ≤ (∫ x in u..v, satoTateDensity x) * c := hmono
    _ = c * ∫ x in u..v, satoTateDensity x := by ring

/-- The uniform grid `0 = t₀ < t₁ < ⋯ < tₙ = π` on `[0, π]`. -/
noncomputable def grid (n j : ℕ) : ℝ := j * Real.pi / n

lemma grid_zero (n : ℕ) : grid n 0 = 0 := by simp [grid]

lemma grid_self {n : ℕ} (hn : 0 < n) : grid n n = Real.pi := by
  have h : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.2 hn.ne'
  unfold grid
  rw [mul_comm, mul_div_assoc, div_self h, mul_one]

lemma grid_mono {n : ℕ} {i j : ℕ} (h : i ≤ j) : grid n i ≤ grid n j := by
  unfold grid
  have hij : (i : ℝ) ≤ j := Nat.cast_le.2 h
  have hn : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
  have hpi := Real.pi_pos.le
  gcongr

lemma grid_nonneg (n j : ℕ) : 0 ≤ grid n j := by
  unfold grid
  have hpi := Real.pi_pos.le
  positivity

lemma grid_mem {n j : ℕ} (hn : 0 < n) (hj : j ≤ n) : grid n j ∈ Icc 0 Real.pi := by
  refine ⟨grid_nonneg n j, ?_⟩
  rw [← grid_self hn]
  exact grid_mono hj

lemma grid_succ_sub {n : ℕ} (hn : 0 < n) (j : ℕ) : grid n (j + 1) - grid n j = Real.pi / n := by
  have h : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.2 hn.ne'
  unfold grid
  push_cast
  field_simp
  ring

/-- The step function approximating `f`, written as a combination of the indicators of the
initial segments `[0, tⱼ]`. -/
noncomputable def stepFun (f : ℝ → ℝ) (n : ℕ) (x : ℝ) : ℝ :=
  f Real.pi + ∑ j ∈ Finset.range n,
    (f (grid n j) - f (grid n (j + 1))) * (if x ≤ grid n j then 1 else 0)

lemma stepFun_eq (f : ℝ → ℝ) {n : ℕ} (hn : 0 < n) {x : ℝ} (hx : x ∈ Icc 0 Real.pi) :
    ∃ k ≤ n, |x - grid n k| ≤ Real.pi / n ∧ stepFun f n x = f (grid n k) := by
  have hpi := Real.pi_pos
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  set k := ⌈x * n / Real.pi⌉₊ with hk
  have hy0 : 0 ≤ x * n / Real.pi := by have := hx.1; positivity
  have hkn : k ≤ n := by
    rw [hk, Nat.ceil_le, div_le_iff₀ hpi]
    have := hx.2
    nlinarith
  have hxk : x ≤ grid n k := by
    have h1 : x * n / Real.pi ≤ (k : ℝ) := Nat.le_ceil _
    unfold grid
    rw [le_div_iff₀ hnR]
    rw [div_le_iff₀ hpi] at h1
    nlinarith
  have hkx : grid n k - x ≤ Real.pi / n := by
    have h2 : (k : ℝ) < x * n / Real.pi + 1 := Nat.ceil_lt_add_one hy0
    unfold grid
    rw [sub_le_iff_le_add, div_le_iff₀ hnR]
    have hcancel : Real.pi / n * n = Real.pi := div_mul_cancel₀ _ hnR.ne'
    have hxn : x * n / Real.pi * Real.pi = x * n := div_mul_cancel₀ _ hpi.ne'
    nlinarith [mul_lt_mul_of_pos_right h2 hpi]
  have hlt : ∀ j : ℕ, j < k → grid n j < x := by
    intro j hj
    have h3 : (j : ℝ) < x * n / Real.pi := Nat.lt_ceil.1 hj
    unfold grid
    rw [div_lt_iff₀ hnR]
    rw [lt_div_iff₀ hpi] at h3
    nlinarith
  refine ⟨k, hkn, by rw [abs_le]; constructor <;> linarith, ?_⟩
  unfold stepFun
  have hfilter : (Finset.range n).filter (fun j => x ≤ grid n j) = Finset.Ico k n := by
    ext j
    simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_Ico]
    constructor
    · rintro ⟨hjn, hxj⟩
      refine ⟨?_, hjn⟩
      by_contra hc
      push_neg at hc
      exact absurd hxj (not_le.2 (hlt j hc))
    · rintro ⟨hkj, hjn⟩
      exact ⟨hjn, hxk.trans (grid_mono hkj)⟩
  have hsum : (∑ j ∈ Finset.range n,
        (f (grid n j) - f (grid n (j + 1))) * (if x ≤ grid n j then 1 else 0))
      = ∑ j ∈ Finset.Ico k n, (f (grid n j) - f (grid n (j + 1))) := by
    rw [← hfilter, Finset.sum_filter]
    exact Finset.sum_congr rfl fun j _ => by split <;> simp
  rw [hsum]
  have htel : (∑ j ∈ Finset.Ico k n, (f (grid n j) - f (grid n (j + 1))))
      = f (grid n k) - f (grid n n) := by
    rw [Finset.sum_Ico_eq_sub _ hkn, Finset.sum_range_sub' (fun i => f (grid n i)),
      Finset.sum_range_sub' (fun i => f (grid n i))]
    ring
  rw [htel, grid_self hn]
  ring

lemma sum_stepFun (f : ℝ → ℝ) (n : ℕ) {θ : ℕ → ℝ} (hrange : ∀ p, θ p ∈ Icc 0 Real.pi) (X : ℕ) :
    (∑ p ∈ primesBelow X, stepFun f n (θ p))
      = ((primesBelow X).card : ℝ) * f Real.pi
        + ∑ j ∈ Finset.range n, (f (grid n j) - f (grid n (j + 1))) *
            ((((primesBelow X).filter fun p => θ p ∈ Icc 0 (grid n j)).card : ℝ)) := by
  unfold stepFun
  rw [Finset.sum_add_distrib, Finset.sum_const, nsmul_eq_mul, Finset.sum_comm]
  congr 1
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [← Finset.mul_sum, Finset.card_filter]
  push_cast
  congr 1
  refine Finset.sum_congr rfl fun p _ => ?_
  have hp := hrange p
  by_cases h : θ p ≤ grid n j
  · simp [h, mem_Icc, hp.1]
  · simp [h, mem_Icc]


lemma stepIntegral_bound {f : ℝ → ℝ} (hf : Continuous f) {n : ℕ} (hn : 0 < n) {c : ℝ}
    (hunif : ∀ x ∈ Icc 0 Real.pi, ∀ y ∈ Icc 0 Real.pi, |x - y| ≤ Real.pi / n → |f x - f y| ≤ c) :
    |(f Real.pi + ∑ j ∈ Finset.range n, (f (grid n j) - f (grid n (j + 1)))
          * (∫ x in (0 : ℝ)..grid n j, satoTateDensity x))
        - ∫ x in (0 : ℝ)..Real.pi, satoTateDensity x * f x| ≤ c := by
  have hpn : 0 ≤ Real.pi / n := by have := Real.pi_pos.le; positivity
  set M : ℕ → ℝ := fun j => ∫ x in (0 : ℝ)..grid n j, satoTateDensity x with hM
  set g : ℕ → ℝ := fun j => f (grid n j) with hg
  have hM0 : M 0 = 0 := by simp [hM, grid_zero]
  have hMn : M n = 1 := by
    rw [hM]; simp only; rw [grid_self hn]; exact integral_satoTateDensity
  have hgn : g n = f Real.pi := by rw [hg]; simp only [grid_self hn]
  have habel := abel_sum_aux g M n hM0
  have hcell : ∀ j, M (j + 1) - M j = ∫ x in (grid n j)..(grid n (j + 1)), satoTateDensity x := by
    intro j
    have h := intervalIntegral.integral_add_adjacent_intervals (μ := MeasureTheory.volume)
      (a := (0 : ℝ)) (b := grid n j) (c := grid n (j + 1))
      (continuous_satoTateDensity.intervalIntegrable _ _)
      (continuous_satoTateDensity.intervalIntegrable _ _)
    simp only [hM]
    linarith [h]
  have hB : (f Real.pi + ∑ j ∈ Finset.range n, (g j - g (j + 1)) * M j)
      = ∑ j ∈ Finset.range n, g (j + 1) * (M (j + 1) - M j) := by
    rw [← habel, hgn, hMn]; ring
  rw [show (∑ j ∈ Finset.range n, (f (grid n j) - f (grid n (j + 1))) * M j)
      = ∑ j ∈ Finset.range n, (g j - g (j + 1)) * M j from rfl, hB]
  have hsplit : (∫ x in (0 : ℝ)..Real.pi, satoTateDensity x * f x)
      = ∑ j ∈ Finset.range n, ∫ x in (grid n j)..(grid n (j + 1)), satoTateDensity x * f x := by
    rw [integral_split_grid (grid n) (fun x => satoTateDensity x * f x)
      (continuous_satoTateDensity.mul hf) n, grid_zero, grid_self hn]
  rw [hsplit, ← Finset.sum_sub_distrib]
  calc |∑ j ∈ Finset.range n, (g (j + 1) * (M (j + 1) - M j)
          - ∫ x in (grid n j)..(grid n (j + 1)), satoTateDensity x * f x)|
      ≤ ∑ j ∈ Finset.range n, |g (j + 1) * (M (j + 1) - M j)
          - ∫ x in (grid n j)..(grid n (j + 1)), satoTateDensity x * f x| :=
        Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ j ∈ Finset.range n, c * ∫ x in (grid n j)..(grid n (j + 1)), satoTateDensity x := by
        refine Finset.sum_le_sum fun j hj => ?_
        rw [Finset.mem_range] at hj
        rw [hcell j]
        refine cell_bound (grid_mono (Nat.le_succ j)) hf ?_
        intro x hx
        have hx1 : x ∈ Icc 0 Real.pi :=
          ⟨le_trans (grid_nonneg n j) hx.1, le_trans hx.2 (grid_mem hn hj).2⟩
        refine hunif _ (grid_mem hn hj) _ hx1 ?_
        rw [abs_le]
        have h1 := hx.1
        have h2 := hx.2
        have h3 := grid_succ_sub hn j
        constructor <;> linarith
    _ = c * ∑ j ∈ Finset.range n, ∫ x in (grid n j)..(grid n (j + 1)), satoTateDensity x := by
        rw [Finset.mul_sum]
    _ = c := by
        rw [integral_split_grid (grid n) satoTateDensity continuous_satoTateDensity n,
          grid_zero, grid_self hn, integral_satoTateDensity, mul_one]


lemma abs_sum_sub_sum_stepFun {f : ℝ → ℝ} {n : ℕ} (hn : 0 < n) {θ : ℕ → ℝ}
    (hrange : ∀ p, θ p ∈ Icc 0 Real.pi) {c : ℝ}
    (hunif : ∀ x ∈ Icc 0 Real.pi, ∀ y ∈ Icc 0 Real.pi, |x - y| ≤ Real.pi / n → |f x - f y| ≤ c)
    (X : ℕ) :
    |(∑ p ∈ primesBelow X, f (θ p)) - ∑ p ∈ primesBelow X, stepFun f n (θ p)|
      ≤ ((primesBelow X).card : ℝ) * c := by
  rw [← Finset.sum_sub_distrib]
  refine le_trans (Finset.abs_sum_le_sum_abs _ _) ?_
  have hterm : ∀ p ∈ primesBelow X, |f (θ p) - stepFun f n (θ p)| ≤ c := by
    intro p _
    obtain ⟨k, hk, habs, heq⟩ := stepFun_eq f hn (hrange p)
    rw [heq]
    exact hunif _ (hrange p) _ (grid_mem hn hk) habs
  refine le_trans (Finset.sum_le_sum hterm) ?_
  rw [Finset.sum_const, nsmul_eq_mul]

/-- The interval form of Sato–Tate equidistribution implies the test-function form. -/
theorem satoTate_of_intervals {θ : ℕ → ℝ} (hrange : ∀ p, θ p ∈ Icc 0 Real.pi)
    (hI : SatoTateIntervals θ) : SatoTateEquidistributed θ := by
  intro f hf
  have hpi := Real.pi_pos
  rw [Metric.tendsto_atTop]
  intro δ hδ
  -- uniform continuity of `f` on `[0, π]`
  have hcont : UniformContinuousOn f (Icc 0 Real.pi) :=
    isCompact_Icc.uniformContinuousOn_of_continuous hf.continuousOn
  rw [Metric.uniformContinuousOn_iff] at hcont
  obtain ⟨η, hη, hηc⟩ := hcont (δ / 4) (by linarith)
  -- a grid fine enough
  set n : ℕ := ⌈Real.pi / η⌉₊ + 1 with hndef
  have hn : 0 < n := Nat.succ_pos _
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hpin : Real.pi / n < η := by
    have h1 : Real.pi / η ≤ (⌈Real.pi / η⌉₊ : ℝ) := Nat.le_ceil _
    have h2 : Real.pi / η < (n : ℝ) := by rw [hndef]; push_cast; linarith
    rw [div_lt_iff₀ hnR]
    rw [div_lt_iff₀ hη] at h2
    linarith [h2]
  have hunif : ∀ x ∈ Icc 0 Real.pi, ∀ y ∈ Icc 0 Real.pi,
      |x - y| ≤ Real.pi / n → |f x - f y| ≤ δ / 4 := by
    intro x hx y hy hxy
    have : dist x y < η := by rw [Real.dist_eq]; linarith
    have := hηc x hx y hy this
    rw [Real.dist_eq] at this
    linarith
  -- the averages of the step function converge
  have hconv : Tendsto
      (fun X : ℕ => f Real.pi + ∑ j ∈ Finset.range n, (f (grid n j) - f (grid n (j + 1))) *
        (((((primesBelow X).filter fun p => θ p ∈ Icc 0 (grid n j)).card : ℝ))
          / (primesBelow X).card))
      atTop (𝓝 (f Real.pi + ∑ j ∈ Finset.range n, (f (grid n j) - f (grid n (j + 1))) *
        (∫ x in (0 : ℝ)..grid n j, satoTateDensity x))) := by
    refine Tendsto.const_add _ (tendsto_finset_sum _ fun j hj => ?_)
    rw [Finset.mem_range] at hj
    exact ((hI 0 (grid n j) le_rfl (grid_nonneg n j) (grid_mem hn hj.le).2)).const_mul _
  rw [Metric.tendsto_atTop] at hconv
  obtain ⟨N, hN⟩ := hconv (δ / 4) (by linarith)
  refine ⟨max N 3, fun X hX => ?_⟩
  have hXN : N ≤ X := le_trans (le_max_left _ _) hX
  have hX3 : 3 ≤ X := le_trans (le_max_right _ _) hX
  have hPpos : (0 : ℝ) < (primesBelow X).card := by exact_mod_cast primesBelow_card_pos hX3
  set P : ℝ := ((primesBelow X).card : ℝ) with hP
  -- the step average, in two forms
  have hstep : (∑ p ∈ primesBelow X, stepFun f n (θ p)) / P
      = f Real.pi + ∑ j ∈ Finset.range n, (f (grid n j) - f (grid n (j + 1))) *
        (((((primesBelow X).filter fun p => θ p ∈ Icc 0 (grid n j)).card : ℝ)) / P) := by
    rw [sum_stepFun f n hrange X, add_div, Finset.sum_div]
    have hne : ((primesBelow X).card : ℝ) ≠ 0 := by rw [hP] at hPpos; exact ne_of_gt hPpos
    congr 1
    · rw [hP, mul_comm, mul_div_assoc, div_self hne, mul_one]
    · exact Finset.sum_congr rfl fun j _ => by rw [mul_div_assoc]
  -- three error terms
  have h1 : |(∑ p ∈ primesBelow X, f (θ p)) / P
      - (∑ p ∈ primesBelow X, stepFun f n (θ p)) / P| ≤ δ / 4 := by
    rw [div_sub_div_same, abs_div, abs_of_pos hPpos, div_le_iff₀ hPpos]
    have := abs_sum_sub_sum_stepFun hn hrange hunif X
    calc |(∑ p ∈ primesBelow X, f (θ p)) - ∑ p ∈ primesBelow X, stepFun f n (θ p)|
        ≤ P * (δ / 4) := this
      _ = δ / 4 * P := by ring
  have h2 := hN X hXN
  rw [Real.dist_eq] at h2
  have h3 := stepIntegral_bound hf hn hunif
  rw [Real.dist_eq]
  rw [hstep] at h1
  calc |(∑ p ∈ primesBelow X, f (θ p)) / P - ∫ x in (0 : ℝ)..Real.pi, satoTateDensity x * f x|
      ≤ δ / 4 + δ / 4 + δ / 4 := by
        rw [abs_le] at h1 h3 ⊢
        rw [abs_lt] at h2
        constructor <;> linarith [h1.1, h1.2, h2.1, h2.2, h3.1, h3.2]
    _ < δ := by linarith

/-- The two formulations of Sato–Tate equidistribution agree, for angles in `[0, π]`. -/
theorem satoTate_iff_intervals {θ : ℕ → ℝ} (hrange : ∀ p, θ p ∈ Icc 0 Real.pi) :
    SatoTateEquidistributed θ ↔ SatoTateIntervals θ :=
  ⟨fun h _ _ hα hαβ hβ => satoTate_interval h hα hαβ hβ, satoTate_of_intervals hrange⟩


/-! ### A concrete consequence -/

lemma integral_satoTateDensity_half : ∫ x in (0 : ℝ)..(Real.pi / 2), satoTateDensity x = 1 / 2 := by
  have hp := Real.pi_pos
  unfold satoTateDensity
  rw [intervalIntegral.integral_const_mul, integral_sin_sq]
  simp
  field_simp

lemma frobeniusAngle_mem_Icc_half {p : ℕ} (hp : 0 < p) (a : ℤ) :
    frobeniusAngle p a ∈ Icc 0 (Real.pi / 2) ↔ 0 ≤ a := by
  have hs : 0 < Real.sqrt p := Real.sqrt_pos.2 (by exact_mod_cast hp)
  rw [frobeniusAngle, mem_Icc]
  constructor
  · rintro ⟨-, h2⟩
    have h3 := Real.arccos_le_pi_div_two.1 h2
    have h4 : (0 : ℝ) ≤ (a : ℝ) := by
      rcases le_or_gt 0 ((a : ℝ)) with h | h
      · exact h
      · exact absurd (div_neg_of_neg_of_pos h (by linarith)) (not_lt.2 h3)
    exact_mod_cast h4
  · intro h
    refine ⟨Real.arccos_nonneg _, Real.arccos_le_pi_div_two.2 ?_⟩
    have h4 : (0 : ℝ) ≤ (a : ℝ) := by exact_mod_cast h
    positivity

/-- A concrete consequence of Sato–Tate: the traces of Frobenius are nonnegative for
exactly half of the primes, in the sense of natural density among the primes. -/
theorem sato_tate_half_nonneg_trace (a : ℕ → ℤ)
    (hST : SatoTateEquidistributed fun p => frobeniusAngle p (a p)) :
    Tendsto (fun X : ℕ => ((((primesBelow X).filter fun p => 0 ≤ a p).card : ℝ))
        / (primesBelow X).card)
      atTop (𝓝 (1 / 2)) := by
  have hpi := Real.pi_pos
  have h := satoTate_interval hST (α := 0) (β := Real.pi / 2) le_rfl (by linarith) (by linarith)
  rw [integral_satoTateDensity_half] at h
  refine h.congr fun X => ?_
  have hfil : ((primesBelow X).filter fun p => frobeniusAngle p (a p) ∈ Icc 0 (Real.pi / 2))
      = ((primesBelow X).filter fun p => 0 ≤ a p) := by
    refine Finset.filter_congr fun p hp => ?_
    have hp' : 0 < p := (Finset.mem_filter.1 hp).2.pos
    exact frobeniusAngle_mem_Icc_half hp' (a p)
  rw [hfil]

#print axioms Math2.sato_tate
#print axioms Math2.satoTate_iff_intervals
#print axioms Math2.sato_tate_half_nonneg_trace

end Math2

import Mathlib

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

