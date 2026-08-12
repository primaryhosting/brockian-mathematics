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

/-!
# An effective convergence rate for the twin-prime singular series

The Hardy–Littlewood singular series for prime pairs `(n, n + 2)` is

  `𝔖 = 2 * ∏_{p odd prime} (1 - 1/(p-1)^2)`,

the product being over all odd primes.  In this file we define the partial products
`Brockian.twinPartial N` (product over the odd primes `p ≤ N`), show they converge, and
prove an *effective* rate of convergence:

  `|Brockian.singularSeriesPartial N - Brockian.singularSeries| ≤ 2 / (N - 1)`  for `N ≥ 3`.
-/

namespace Brockian

open Filter Finset
open scoped Topology

/-- The set of odd primes `p ≤ N`, as a `Finset`. -/
def oddPrimesLE (N : ℕ) : Finset ℕ :=
  (Finset.range (N + 1)).filter (fun p => Nat.Prime p ∧ 3 ≤ p)

/-- The local factor `1 - 1/(p-1)^2` of the twin-prime singular series at an odd prime `p`. -/
noncomputable def twinFactor (p : ℕ) : ℝ := 1 - 1 / ((p : ℝ) - 1) ^ 2

/-- The partial product of the twin-prime singular series, over the odd primes `p ≤ N`. -/
noncomputable def twinPartial (N : ℕ) : ℝ := ∏ p ∈ oddPrimesLE N, twinFactor p

/-- The twin-prime (Hardy–Littlewood) constant `C₂ = ∏_{p odd prime} (1 - 1/(p-1)^2)`,
defined as the infimum of the (antitone) sequence of partial products. -/
noncomputable def twinPrimeConstant : ℝ := ⨅ N, twinPartial N

/-- The truncation at `N` of the singular series `𝔖 = 2 C₂` for prime pairs. -/
noncomputable def singularSeriesPartial (N : ℕ) : ℝ := 2 * twinPartial N

/-- The singular series `𝔖 = 2 C₂` for prime pairs `(n, n+2)`. -/
noncomputable def singularSeries : ℝ := 2 * twinPrimeConstant

/-- Weierstrass' product inequality: `1 - ∑ f ≤ ∏ (1 - f)` for `f` valued in `[0,1]`. -/
theorem one_sub_sum_le_prod_one_sub (s : Finset ℕ) (f : ℕ → ℝ)
    (h0 : ∀ i ∈ s, 0 ≤ f i) (h1 : ∀ i ∈ s, f i ≤ 1) :
    1 - ∑ i ∈ s, f i ≤ ∏ i ∈ s, (1 - f i) := by
  induction s using Finset.cons_induction with
  | empty => simp
  | cons a s ha ih =>
      have hs0 : ∀ i ∈ s, 0 ≤ f i := fun i hi => h0 i (Finset.mem_cons_of_mem hi)
      have hs1 : ∀ i ∈ s, f i ≤ 1 := fun i hi => h1 i (Finset.mem_cons_of_mem hi)
      have hprodnn : (0:ℝ) ≤ ∏ i ∈ s, (1 - f i) :=
        Finset.prod_nonneg (fun i hi => by linarith [hs1 i hi])
      have hfa0 : 0 ≤ f a := h0 a (Finset.mem_cons_self _ _)
      have hfa1 : f a ≤ 1 := h1 a (Finset.mem_cons_self _ _)
      have hind := ih hs0 hs1
      have hsum : (0:ℝ) ≤ ∑ i ∈ s, f i := Finset.sum_nonneg hs0
      rw [Finset.prod_cons, Finset.sum_cons]
      nlinarith [hind]

theorem mem_oddPrimesLE {N p : ℕ} : p ∈ oddPrimesLE N ↔ p ≤ N ∧ Nat.Prime p ∧ 3 ≤ p := by
  simp [oddPrimesLE]

theorem oddPrimesLE_subset {M N : ℕ} (h : N ≤ M) : oddPrimesLE N ⊆ oddPrimesLE M := by
  intro p hp
  rw [mem_oddPrimesLE] at hp ⊢
  exact ⟨hp.1.trans h, hp.2⟩

theorem twinFactor_nonneg {p : ℕ} (hp : 3 ≤ p) : 0 ≤ twinFactor p := by
  have h3 : (3:ℝ) ≤ (p : ℝ) := by exact_mod_cast hp
  have h2 : (2:ℝ) ≤ (p : ℝ) - 1 := by linarith
  have : (1:ℝ) ≤ ((p : ℝ) - 1) ^ 2 := by nlinarith
  have hpos : (0:ℝ) < ((p : ℝ) - 1) ^ 2 := by nlinarith
  rw [twinFactor, sub_nonneg, div_le_one hpos]
  exact this

theorem twinFactor_le_one (p : ℕ) : twinFactor p ≤ 1 := by
  have : (0:ℝ) ≤ 1 / ((p : ℝ) - 1) ^ 2 := by positivity
  simpa [twinFactor] using this

theorem twinPartial_nonneg (N : ℕ) : 0 ≤ twinPartial N :=
  Finset.prod_nonneg fun _ hp => twinFactor_nonneg (mem_oddPrimesLE.mp hp).2.2

theorem twinPartial_le_one (N : ℕ) : twinPartial N ≤ 1 :=
  Finset.prod_le_one (fun _ hp => twinFactor_nonneg (mem_oddPrimesLE.mp hp).2.2)
    (fun p _ => twinFactor_le_one p)

theorem twinPartial_antitone : Antitone twinPartial := by
  classical
  intro N M h
  have hsplit : (∏ p ∈ oddPrimesLE M \ oddPrimesLE N, twinFactor p) * twinPartial N
      = twinPartial M := Finset.prod_sdiff (oddPrimesLE_subset h)
  set Q := ∏ p ∈ oddPrimesLE M \ oddPrimesLE N, twinFactor p with hQ
  have hQnn : 0 ≤ Q := Finset.prod_nonneg fun _ hp =>
    twinFactor_nonneg (mem_oddPrimesLE.mp (Finset.mem_sdiff.mp hp).1).2.2
  have hQle : Q ≤ 1 :=
    Finset.prod_le_one
      (fun _ hp => twinFactor_nonneg (mem_oddPrimesLE.mp (Finset.mem_sdiff.mp hp).1).2.2)
      (fun p _ => twinFactor_le_one p)
  nlinarith [twinPartial_nonneg N]

theorem twinPartial_bddBelow : BddBelow (Set.range twinPartial) := by
  refine ⟨0, ?_⟩
  rintro x ⟨N, rfl⟩
  exact twinPartial_nonneg N

/-- The partial products converge to the twin-prime constant. -/
theorem twinPartial_tendsto :
    Tendsto twinPartial atTop (𝓝 twinPrimeConstant) :=
  tendsto_atTop_ciInf twinPartial_antitone twinPartial_bddBelow

/-- The elementary telescoping step `1/x^2 ≤ 1/(x-1) - 1/x` for `x ≥ 2`. -/
theorem one_div_sq_le_telescope (x : ℝ) (hx : 2 ≤ x) : 1 / x ^ 2 ≤ 1 / (x - 1) - 1 / x := by
  have h1 : (0:ℝ) < x - 1 := by linarith
  have h2 : (0:ℝ) < x := by linarith
  have key : 1 / (x - 1) - 1 / x - 1 / x ^ 2 = 1 / ((x - 1) * x ^ 2) := by field_simp; ring
  have h3 : (0:ℝ) ≤ 1 / ((x - 1) * x ^ 2) := by positivity
  linarith

/-- Telescoping bound: `∑_{N < n ≤ M} 1/(n-1)^2 ≤ 1/(N-1) - 1/(M-1)`. -/
theorem sum_inv_sq_Ioc_le {N : ℕ} (hN : 2 ≤ N) :
    ∀ M : ℕ, N ≤ M →
      ∑ n ∈ Finset.Ioc N M, 1 / ((n : ℝ) - 1) ^ 2 ≤ 1 / ((N : ℝ) - 1) - 1 / ((M : ℝ) - 1) := by
  intro M hM
  induction M, hM using Nat.le_induction with
  | base => simp
  | succ M hM ih =>
      have hM2 : (2:ℝ) ≤ (M : ℝ) := by
        have : (2:ℕ) ≤ M := le_trans hN hM
        exact_mod_cast this
      rw [Finset.sum_Ioc_succ_top (by omega)]
      push_cast
      have haux := one_div_sq_le_telescope (M : ℝ) hM2
      have hs : ((M:ℝ) + 1 - 1) = (M:ℝ) := by ring
      rw [hs]
      linarith

/-- Effective Cauchy estimate for the partial products. -/
theorem twinPartial_sub_le {N M : ℕ} (hN : 3 ≤ N) (hM : N ≤ M) :
    twinPartial N - twinPartial M ≤ 1 / ((N : ℝ) - 1) := by
  classical
  set D := oddPrimesLE M \ oddPrimesLE N with hD
  have hsub : oddPrimesLE N ⊆ oddPrimesLE M := oddPrimesLE_subset hM
  have hsplit : (∏ p ∈ D, twinFactor p) * twinPartial N = twinPartial M :=
    Finset.prod_sdiff hsub
  set Q := ∏ p ∈ D, twinFactor p with hQ
  have hQnn : 0 ≤ Q := Finset.prod_nonneg fun _ hp =>
    twinFactor_nonneg (mem_oddPrimesLE.mp (Finset.mem_sdiff.mp hp).1).2.2
  have hQle : Q ≤ 1 :=
    Finset.prod_le_one (fun _ hp => twinFactor_nonneg (mem_oddPrimesLE.mp (Finset.mem_sdiff.mp hp).1).2.2)
      (fun p _ => twinFactor_le_one p)
  -- Weierstrass bound on `1 - Q`
  have hW : 1 - ∑ p ∈ D, 1 / ((p : ℝ) - 1) ^ 2 ≤ Q := by
    have := one_sub_sum_le_prod_one_sub D (fun p => 1 / ((p : ℝ) - 1) ^ 2)
      (fun p _ => by positivity)
      (fun p hp => by
        have hp3 : 3 ≤ p := (mem_oddPrimesLE.mp (Finset.mem_sdiff.mp hp).1).2.2
        have h3 : (3:ℝ) ≤ (p : ℝ) := by exact_mod_cast hp3
        rw [div_le_one (by nlinarith)]
        nlinarith)
    simpa [hQ, twinFactor] using this
  -- the sum over `D` is at most the telescoping sum
  have hDsub : D ⊆ Finset.Ioc N M := by
    intro p hp
    rw [Finset.mem_sdiff] at hp
    obtain ⟨hpM, hpN⟩ := hp
    rw [mem_oddPrimesLE] at hpM
    rw [Finset.mem_Ioc]
    refine ⟨?_, hpM.1⟩
    by_contra hcon
    exact hpN (mem_oddPrimesLE.mpr ⟨by omega, hpM.2⟩)
  have hsum : ∑ p ∈ D, 1 / ((p : ℝ) - 1) ^ 2 ≤ ∑ n ∈ Finset.Ioc N M, 1 / ((n : ℝ) - 1) ^ 2 :=
    Finset.sum_le_sum_of_subset_of_nonneg hDsub (fun i _ _ => by positivity)
  have hM1 : (1:ℝ) ≤ (M : ℝ) - 1 := by
    have : (3:ℕ) ≤ M := le_trans hN hM
    have : (3:ℝ) ≤ (M:ℝ) := by exact_mod_cast this
    linarith
  have htel := sum_inv_sq_Ioc_le (N := N) (by omega) M hM
  have hinv : 0 < 1 / ((M : ℝ) - 1) := by positivity
  have hbound : ∑ p ∈ D, 1 / ((p : ℝ) - 1) ^ 2 ≤ 1 / ((N : ℝ) - 1) := by
    linarith
  have hPN := twinPartial_le_one N
  have hPNnn := twinPartial_nonneg N
  have : twinPartial N - twinPartial M = twinPartial N * (1 - Q) := by
    rw [← hsplit]; ring
  rw [this]
  have h1Q : 1 - Q ≤ ∑ p ∈ D, 1 / ((p : ℝ) - 1) ^ 2 := by linarith
  nlinarith [hbound, h1Q]

theorem twinPrimeConstant_le (N : ℕ) : twinPrimeConstant ≤ twinPartial N :=
  ciInf_le twinPartial_bddBelow N

/-- **Effective convergence rate for the twin-prime constant.** -/
theorem twinPartial_sub_twinPrimeConstant_le {N : ℕ} (hN : 3 ≤ N) :
    |twinPartial N - twinPrimeConstant| ≤ 1 / ((N : ℝ) - 1) := by
  have hle : twinPrimeConstant ≤ twinPartial N := twinPrimeConstant_le N
  have hupper : twinPartial N - twinPrimeConstant ≤ 1 / ((N : ℝ) - 1) := by
    have hlim : Tendsto (fun M => twinPartial N - twinPartial M) atTop
        (𝓝 (twinPartial N - twinPrimeConstant)) := by
      exact (tendsto_const_nhds).sub twinPartial_tendsto
    refine le_of_tendsto hlim ?_
    filter_upwards [eventually_ge_atTop N] with M hM
    exact twinPartial_sub_le hN hM
  rw [abs_of_nonneg (by linarith)]
  exact hupper

/-- **Effective convergence-rate bound for the singular series.**
For every `N ≥ 3`, the truncation `singularSeriesPartial N = 2 ∏_{3 ≤ p ≤ N} (1 - 1/(p-1)^2)`
of the Hardy–Littlewood singular series for prime pairs approximates `𝔖` with error at most
`2/(N-1)`. -/
theorem SingularSeriesConvergenceRate {N : ℕ} (hN : 3 ≤ N) :
    |singularSeriesPartial N - singularSeries| ≤ 2 / ((N : ℝ) - 1) := by
  have h := twinPartial_sub_twinPrimeConstant_le hN
  have : singularSeriesPartial N - singularSeries = 2 * (twinPartial N - twinPrimeConstant) := by
    simp [singularSeriesPartial, singularSeries]; ring
  rw [this, abs_mul, abs_of_nonneg (by norm_num : (0:ℝ) ≤ 2)]
  calc 2 * |twinPartial N - twinPrimeConstant| ≤ 2 * (1 / ((N:ℝ) - 1)) := by linarith
    _ = 2 / ((N:ℝ) - 1) := by ring

/-- The truncated singular series converges to `𝔖`. -/
theorem singularSeriesPartial_tendsto :
    Tendsto singularSeriesPartial atTop (𝓝 singularSeries) :=
  tendsto_const_nhds.mul twinPartial_tendsto

end Brockian

