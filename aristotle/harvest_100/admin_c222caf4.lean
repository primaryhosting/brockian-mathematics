import Mathlib

/-!
# Sato Tate
Category: Frontier Math
Target: Math2.sato_tate
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

set_option grind.warning false

namespace Math2

open Filter Topology Set Polynomial

/-- The Sato–Tate density `(2/π) sin²θ` on the interval `[0, π]`. -/
noncomputable def stDensity (t : ℝ) : ℝ := (2 / π) * Real.sin t ^ 2

/-- The integral of `f` against the Sato–Tate measure `(2/π) sin²θ dθ` on `[0, π]`. -/
noncomputable def stIntegral (f : ℝ → ℝ) : ℝ := ∫ t in (0:ℝ)..π, f t * stDensity t

/-- The finite set of primes `p ≤ N`. -/
def primesUpTo (N : ℕ) : Finset ℕ := (Finset.range (N + 1)).filter Nat.Prime

/-- The average of `f (θ p)` over the primes `p ≤ N`. -/
noncomputable def primeAvg (θ : ℕ → ℝ) (f : ℝ → ℝ) (N : ℕ) : ℝ :=
  (∑ p ∈ primesUpTo N, f (θ p)) / ((primesUpTo N).card : ℝ)

/-- The angles `θ p` are *Sato–Tate distributed*: the empirical measures of the angles
attached to the primes `p ≤ N` converge weakly, as `N → ∞`, to the Sato–Tate measure
`(2/π) sin²θ dθ` on `[0, π]`. -/
def SatoTateDistributed (θ : ℕ → ℝ) : Prop :=
  ∀ f : ℝ → ℝ, Continuous f → Tendsto (fun N => primeAvg θ f N) atTop (𝓝 (stIntegral f))

/-- The `m`-th Weyl test function `θ ↦ U_m (cos θ)`, where `U_m` is the Chebyshev polynomial
of the second kind; equivalently `θ ↦ sin ((m+1)θ) / sin θ`.  This is the character of the
`m`-th symmetric power of the standard representation of `SU(2)`. -/
noncomputable def weyl (m : ℕ) : ℝ → ℝ := fun t => (Chebyshev.U ℝ m).eval (Real.cos t)

/-- The Frobenius angle at `p` attached to the trace of Frobenius `a p`:
`θ_p = arccos (a_p / (2 √p))`, so that `a_p = 2 √p cos θ_p`. -/
noncomputable def frobeniusAngle (a : ℕ → ℤ) (p : ℕ) : ℝ :=
  Real.arccos ((a p : ℝ) / (2 * Real.sqrt p))

/-! ### Basic properties of the Sato–Tate integral -/

lemma continuous_stDensity : Continuous stDensity := by
  unfold stDensity; fun_prop

lemma stDensity_nonneg (t : ℝ) : 0 ≤ stDensity t := by
  unfold stDensity; positivity

lemma stIntegral_one : stIntegral (fun _ => 1) = 1 := by
  unfold stIntegral stDensity
  simp only [one_mul]
  rw [intervalIntegral.integral_const_mul, integral_sin_sq]
  simp [Real.pi_ne_zero]

lemma weyl_zero : weyl 0 = fun _ => 1 := by
  funext t; simp [weyl, Chebyshev.U_zero]

lemma continuous_weyl (m : ℕ) : Continuous (weyl m) :=
  (Chebyshev.U ℝ m).continuous_aeval.comp Real.continuous_cos

lemma integral_cos_nat_mul {k : ℕ} (hk : 1 ≤ k) : ∫ t in (0:ℝ)..π, Real.cos (k * t) = 0 := by
  have hk0 : (k:ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
  rw [intervalIntegral.integral_comp_mul_left (fun x => Real.cos x) hk0]
  simp [Real.sin_nat_mul_pi]

lemma stIntegral_weyl_eq_zero {m : ℕ} (hm : 1 ≤ m) : stIntegral (weyl m) = 0 := by
  have key : ∀ t : ℝ, weyl m t * stDensity t
      = (1 / π) * (Real.cos (m * t) - Real.cos ((m + 2) * t)) := by
    intro t
    have h := Chebyshev.U_real_cos t (m : ℤ)
    have hU : weyl m t * Real.sin t = Real.sin (((m : ℝ) + 1) * t) := by
      unfold weyl
      rw [show (Chebyshev.U ℝ (m : ℕ)) = Chebyshev.U ℝ (m : ℤ) by norm_cast]
      exact_mod_cast h
    have e1 : Real.cos ((m : ℝ) * t) = Real.cos (((m : ℝ) + 1) * t) * Real.cos t
        + Real.sin (((m : ℝ) + 1) * t) * Real.sin t := by
      rw [show (m : ℝ) * t = ((m : ℝ) + 1) * t - t by ring, Real.cos_sub]
    have e2 : Real.cos (((m : ℝ) + 2) * t) = Real.cos (((m : ℝ) + 1) * t) * Real.cos t
        - Real.sin (((m : ℝ) + 1) * t) * Real.sin t := by
      rw [show ((m : ℝ) + 2) * t = ((m : ℝ) + 1) * t + t by ring, Real.cos_add]
    unfold stDensity
    rw [e1, e2]
    rw [show weyl m t * (2 / π * Real.sin t ^ 2)
        = 2 / π * ((weyl m t * Real.sin t) * Real.sin t) by ring, hU]
    field_simp
    ring
  unfold stIntegral
  simp only [key]
  rw [intervalIntegral.integral_const_mul, intervalIntegral.integral_sub]
  · rw [integral_cos_nat_mul hm, show ((m : ℝ) + 2) = ((m + 2 : ℕ) : ℝ) by push_cast; ring]
    rw [integral_cos_nat_mul (by omega : 1 ≤ m + 2)]
    simp
  · exact (Real.continuous_cos.comp (continuous_const.mul continuous_id)).intervalIntegrable _ _
  · exact (Real.continuous_cos.comp (continuous_const.mul continuous_id)).intervalIntegrable _ _

lemma stIntegral_sum {ι : Type} (s : Finset ι) (f : ι → ℝ → ℝ)
    (hf : ∀ i ∈ s, Continuous (f i)) :
    stIntegral (fun t => ∑ i ∈ s, f i t) = ∑ i ∈ s, stIntegral (f i) := by
  unfold stIntegral
  simp only [Finset.sum_mul]
  exact intervalIntegral.integral_finset_sum
    (fun i hi => ((hf i hi).mul continuous_stDensity).intervalIntegrable _ _)

lemma stIntegral_const_mul (c : ℝ) (f : ℝ → ℝ) :
    stIntegral (fun t => c * f t) = c * stIntegral f := by
  unfold stIntegral
  rw [← intervalIntegral.integral_const_mul]
  congr 1; funext t; ring

lemma stIntegral_sub {f g : ℝ → ℝ} (hf : Continuous f) (hg : Continuous g) :
    stIntegral (fun t => f t - g t) = stIntegral f - stIntegral g := by
  unfold stIntegral
  simp only [sub_mul]
  exact intervalIntegral.integral_sub ((hf.mul continuous_stDensity).intervalIntegrable _ _)
    ((hg.mul continuous_stDensity).intervalIntegrable _ _)

lemma abs_stIntegral_le {f : ℝ → ℝ} {C : ℝ} (hf : Continuous f)
    (h : ∀ t ∈ Icc (0:ℝ) π, |f t| ≤ C) : |stIntegral f| ≤ C := by
  have hpi : (0:ℝ) ≤ π := Real.pi_pos.le
  have h1 : |stIntegral f| ≤ ∫ t in (0:ℝ)..π, |f t * stDensity t| :=
    intervalIntegral.abs_integral_le_integral_abs hpi
  have h2 : (∫ t in (0:ℝ)..π, |f t * stDensity t|) ≤ ∫ t in (0:ℝ)..π, C * stDensity t := by
    apply intervalIntegral.integral_mono_on hpi
    · exact ((hf.mul continuous_stDensity).abs).intervalIntegrable _ _
    · exact (continuous_const.mul continuous_stDensity).intervalIntegrable _ _
    · intro t ht
      rw [abs_mul, abs_of_nonneg (stDensity_nonneg t)]
      exact mul_le_mul_of_nonneg_right (h t ht) (stDensity_nonneg t)
  have h3 : (∫ t in (0:ℝ)..π, C * stDensity t) = C := by
    have hc := stIntegral_const_mul C (fun _ => 1)
    simp only [mul_one, stIntegral_one] at hc
    exact hc
  linarith

/-! ### Basic properties of prime averages -/

lemma card_primesUpTo_pos {N : ℕ} (hN : 2 ≤ N) : 0 < (primesUpTo N).card := by
  refine Finset.card_pos.mpr ⟨2, ?_⟩
  simp only [primesUpTo, Finset.mem_filter, Finset.mem_range]
  exact ⟨by omega, Nat.prime_two⟩

lemma primeAvg_const (θ : ℕ → ℝ) {N : ℕ} (hN : 2 ≤ N) (c : ℝ) :
    primeAvg θ (fun _ => c) N = c := by
  have h := card_primesUpTo_pos hN
  unfold primeAvg
  rw [Finset.sum_const, nsmul_eq_mul]
  field_simp

lemma primeAvg_sum {ι : Type} (θ : ℕ → ℝ) (s : Finset ι) (f : ι → ℝ → ℝ) (N : ℕ) :
    primeAvg θ (fun t => ∑ i ∈ s, f i t) N = ∑ i ∈ s, primeAvg θ (f i) N := by
  unfold primeAvg
  rw [Finset.sum_comm, Finset.sum_div]

lemma primeAvg_const_mul (θ : ℕ → ℝ) (c : ℝ) (f : ℝ → ℝ) (N : ℕ) :
    primeAvg θ (fun t => c * f t) N = c * primeAvg θ f N := by
  unfold primeAvg
  rw [← Finset.mul_sum, mul_div_assoc]

lemma primeAvg_sub (θ : ℕ → ℝ) (f g : ℝ → ℝ) (N : ℕ) :
    primeAvg θ (fun t => f t - g t) N = primeAvg θ f N - primeAvg θ g N := by
  unfold primeAvg
  rw [Finset.sum_sub_distrib, sub_div]

lemma abs_primeAvg_le {θ : ℕ → ℝ} {f : ℝ → ℝ} {C : ℝ} {N : ℕ} (hN : 2 ≤ N)
    (hθ : ∀ p, θ p ∈ Icc (0:ℝ) π) (h : ∀ t ∈ Icc (0:ℝ) π, |f t| ≤ C) :
    |primeAvg θ f N| ≤ C := by
  have hcard : 0 < ((primesUpTo N).card : ℝ) := by
    exact_mod_cast card_primesUpTo_pos hN
  have hC : 0 ≤ C := le_trans (abs_nonneg _) (h 0 ⟨le_refl 0, Real.pi_pos.le⟩)
  unfold primeAvg
  rw [abs_div, abs_of_nonneg hcard.le, div_le_iff₀ hcard]
  calc |∑ p ∈ primesUpTo N, f (θ p)| ≤ ∑ p ∈ primesUpTo N, |f (θ p)| :=
        Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _p ∈ primesUpTo N, C := Finset.sum_le_sum fun p _ => h _ (hθ p)
    _ = C * (primesUpTo N).card := by rw [Finset.sum_const, nsmul_eq_mul]; ring

/-! ### Density of the span of the Weyl test functions -/

lemma cheb_coeff_top (n : ℕ) : (Chebyshev.U ℝ (n : ℤ)).coeff n = 2 ^ n := by
  have h1 : (Chebyshev.U ℝ (n : ℤ)).natDegree = n := Chebyshev.natDegree_U_natCast ℝ n
  have h := Chebyshev.leadingCoeff_U_natCast ℝ n
  rw [Polynomial.leadingCoeff, h1] at h
  exact h

lemma cheb_span_aux : ∀ (n : ℕ) (q : ℝ[X]), q.natDegree ≤ n →
    ∃ c : ℕ → ℝ, ∀ x : ℝ,
      q.eval x = ∑ m ∈ Finset.range (n + 1), c m * (Chebyshev.U ℝ m).eval x := by
  intro n
  induction n with
  | zero =>
    intro q hq
    refine ⟨fun _ => q.coeff 0, fun x => ?_⟩
    rw [Polynomial.eq_C_of_natDegree_le_zero hq]
    simp [Chebyshev.U_zero]
  | succ n ih =>
    intro q hq
    set b : ℝ := q.coeff (n + 1) / 2 ^ (n + 1) with hb
    set r : ℝ[X] := q - C b * Chebyshev.U ℝ ((n + 1 : ℕ) : ℤ) with hr
    have hrdeg : r.natDegree ≤ n := by
      rw [Polynomial.natDegree_le_iff_coeff_eq_zero]
      intro N hN
      rw [hr, Polynomial.coeff_sub, Polynomial.coeff_C_mul]
      rcases eq_or_lt_of_le (Nat.succ_le_of_lt hN) with heq | hlt
      · rw [← heq, cheb_coeff_top (n + 1), hb]
        field_simp
        ring
      · have h1 : q.coeff N = 0 := Polynomial.coeff_eq_zero_of_natDegree_lt (lt_of_le_of_lt hq hlt)
        have h2 : (Chebyshev.U ℝ ((n + 1 : ℕ) : ℤ)).coeff N = 0 := by
          apply Polynomial.coeff_eq_zero_of_natDegree_lt
          rw [Chebyshev.natDegree_U_natCast ℝ (n + 1)]
          exact hlt
        rw [h1, h2]; ring
    obtain ⟨c, hc⟩ := ih r hrdeg
    refine ⟨Function.update c (n + 1) b, fun x => ?_⟩
    rw [Finset.sum_range_succ]
    have hsum : ∑ m ∈ Finset.range (n + 1), Function.update c (n + 1) b m * (Chebyshev.U ℝ m).eval x
        = ∑ m ∈ Finset.range (n + 1), c m * (Chebyshev.U ℝ m).eval x := by
      refine Finset.sum_congr rfl fun m hm => ?_
      have hne : m ≠ n + 1 := by simp only [Finset.mem_range] at hm; omega
      rw [Function.update_of_ne hne]
    rw [hsum, ← hc x]
    have hev : r.eval x = q.eval x - b * (Chebyshev.U ℝ ((n + 1 : ℕ) : ℤ)).eval x := by
      rw [hr]; simp
    rw [hev, Function.update_self]
    push_cast
    ring

/-- Every real polynomial is a linear combination of Chebyshev polynomials of the second kind. -/
lemma exists_chebyshev_repr (q : ℝ[X]) :
    ∃ (n : ℕ) (c : ℕ → ℝ), ∀ x : ℝ,
      q.eval x = ∑ m ∈ Finset.range n, c m * (Chebyshev.U ℝ m).eval x := by
  obtain ⟨c, hc⟩ := cheb_span_aux q.natDegree q le_rfl
  exact ⟨q.natDegree + 1, c, hc⟩

/-- Weierstrass approximation: continuous functions on `[0, π]` are uniformly approximated by
finite linear combinations of the Weyl test functions. -/
lemma exists_weyl_approx {f : ℝ → ℝ} (hf : Continuous f) {ε : ℝ} (hε : 0 < ε) :
    ∃ (n : ℕ) (c : ℕ → ℝ), ∀ t ∈ Icc (0:ℝ) π,
      |f t - ∑ m ∈ Finset.range n, c m * weyl m t| ≤ ε := by
  have hF : Continuous (fun x : ℝ => f (Real.arccos x)) := hf.comp Real.continuous_arccos
  obtain ⟨q, hq⟩ := exists_polynomial_near_of_continuousOn (-1) 1 (fun x => f (Real.arccos x))
    hF.continuousOn ε hε
  obtain ⟨n, c, hc⟩ := exists_chebyshev_repr q
  refine ⟨n, c, fun t ht => ?_⟩
  have hcos : Real.cos t ∈ Icc (-1:ℝ) 1 := ⟨Real.neg_one_le_cos t, Real.cos_le_one t⟩
  have h1 := hq (Real.cos t) hcos
  rw [Real.arccos_cos ht.1 ht.2] at h1
  have h2 : ∑ m ∈ Finset.range n, c m * weyl m t = q.eval (Real.cos t) := (hc (Real.cos t)).symm
  rw [h2, abs_sub_comm]
  exact h1.le

/-! ### The Weyl criterion for the Sato–Tate measure -/

/-- **Weyl criterion for the Sato–Tate measure.**  A sequence of angles in `[0, π]` is
Sato–Tate distributed if and only if all the Weyl sums attached to the nontrivial
symmetric powers tend to `0`. -/
theorem satoTate_iff_weyl_tendsto_zero (θ : ℕ → ℝ) (hθ : ∀ p, θ p ∈ Icc (0:ℝ) π) :
    SatoTateDistributed θ ↔
      ∀ m : ℕ, 1 ≤ m → Tendsto (fun N => primeAvg θ (weyl m) N) atTop (𝓝 0) := by
  constructor
  · intro h m hm
    have h' := h (weyl m) (continuous_weyl m)
    rwa [stIntegral_weyl_eq_zero hm] at h'
  · intro hW
    have key : ∀ m : ℕ,
        Tendsto (fun N => primeAvg θ (weyl m) N) atTop (𝓝 (stIntegral (weyl m))) := by
      intro m
      rcases Nat.eq_zero_or_pos m with rfl | hm
      · rw [weyl_zero, stIntegral_one]
        refine Tendsto.congr' ?_ tendsto_const_nhds
        filter_upwards [eventually_ge_atTop 2] with N hN
        exact (primeAvg_const θ hN 1).symm
      · rw [stIntegral_weyl_eq_zero hm]
        exact hW m hm
    intro f hf
    rw [Metric.tendsto_atTop]
    intro ε hε
    obtain ⟨n, c, hc⟩ := exists_weyl_approx hf (show (0:ℝ) < ε / 4 by linarith)
    let g : ℝ → ℝ := fun t => ∑ m ∈ Finset.range n, c m * weyl m t
    have hgcont : Continuous g :=
      continuous_finset_sum _ fun m _ => continuous_const.mul (continuous_weyl m)
    have hgint : stIntegral g = ∑ m ∈ Finset.range n, c m * stIntegral (weyl m) := by
      have h := stIntegral_sum (Finset.range n) (fun m t => c m * weyl m t)
        (fun m _ => continuous_const.mul (continuous_weyl m))
      simpa [g, stIntegral_const_mul] using h
    have hgavg : Tendsto (fun N => primeAvg θ g N) atTop (𝓝 (stIntegral g)) := by
      rw [hgint]
      have hrw : ∀ N, primeAvg θ g N = ∑ m ∈ Finset.range n, c m * primeAvg θ (weyl m) N := by
        intro N
        have h := primeAvg_sum θ (Finset.range n) (fun m t => c m * weyl m t) N
        simpa [g, primeAvg_const_mul] using h
      simp only [hrw]
      exact tendsto_finset_sum _ fun m _ => (key m).const_mul (c m)
    rw [Metric.tendsto_atTop] at hgavg
    obtain ⟨N₀, hN₀⟩ := hgavg (ε / 2) (by linarith)
    refine ⟨max N₀ 2, fun N hN => ?_⟩
    have hN2 : 2 ≤ N := le_trans (le_max_right _ _) hN
    have hNN₀ : N₀ ≤ N := le_trans (le_max_left _ _) hN
    have h1 : |primeAvg θ f N - primeAvg θ g N| ≤ ε / 4 := by
      rw [← primeAvg_sub]
      exact abs_primeAvg_le hN2 hθ fun t ht => hc t ht
    have h2 : |stIntegral f - stIntegral g| ≤ ε / 4 := by
      rw [← stIntegral_sub hf hgcont]
      exact abs_stIntegral_le (hf.sub hgcont) fun t ht => hc t ht
    have h3 : |primeAvg θ g N - stIntegral g| < ε / 2 := by
      have := hN₀ N hNN₀
      rwa [Real.dist_eq] at this
    have h2' : |stIntegral g - stIntegral f| ≤ ε / 4 := by rwa [abs_sub_comm] at h2
    have t1 := abs_sub_le (primeAvg θ f N) (stIntegral g) (stIntegral f)
    have t2 := abs_sub_le (primeAvg θ f N) (primeAvg θ g N) (stIntegral g)
    rw [Real.dist_eq]
    linarith

/-- Under the Hasse bound, the Frobenius angle really does satisfy `a_p = 2 √p cos θ_p`. -/
lemma frobeniusAngle_spec (a : ℕ → ℤ)
    (hasse : ∀ p : ℕ, p.Prime → |(a p : ℝ)| ≤ 2 * Real.sqrt p) (p : ℕ) (hp : p.Prime) :
    (a p : ℝ) = 2 * Real.sqrt p * Real.cos (frobeniusAngle a p) := by
  have hp0 : (0:ℝ) < p := by exact_mod_cast hp.pos
  have hsqrt : 0 < Real.sqrt p := Real.sqrt_pos.mpr hp0
  have hden : (0:ℝ) < 2 * Real.sqrt p := by linarith
  have habs : |(a p : ℝ) / (2 * Real.sqrt p)| ≤ 1 := by
    rw [abs_div, abs_of_pos hden, div_le_one hden]
    exact hasse p hp
  rw [abs_le] at habs
  unfold frobeniusAngle
  rw [Real.cos_arccos habs.1 habs.2]
  field_simp

/-- **Sato–Tate.**  Let `a : ℕ → ℤ` be the trace-of-Frobenius function of a non-CM elliptic
curve over `ℚ` (so that `|a p| ≤ 2 √p` by the Hasse bound), and let
`θ_p = arccos (a_p / (2 √p))` be the associated Frobenius angles.  Then the Frobenius angles
are equidistributed with respect to the Sato–Tate measure `(2/π) sin²θ dθ` on `[0, π]`
if and only if, for every `m ≥ 1`, the `m`-th symmetric power Weyl sums
`(1/π(N)) ∑_{p ≤ N} U_m(cos θ_p)` tend to `0`; the latter is exactly the analytic input
(nonvanishing/analyticity of the symmetric power `L`-functions) supplied by the potential
automorphy theorems.

The first conjunct records, using the Hasse bound, that `θ_p` is indeed an angle in `[0, π]`
with `a_p = 2 √p cos θ_p`; the equivalence itself holds for any angles in `[0, π]`. -/
theorem sato_tate (a : ℕ → ℤ) (hasse : ∀ p : ℕ, p.Prime → |(a p : ℝ)| ≤ 2 * Real.sqrt p) :
    (∀ p : ℕ, p.Prime → (a p : ℝ) = 2 * Real.sqrt p * Real.cos (frobeniusAngle a p)) ∧
      (SatoTateDistributed (frobeniusAngle a) ↔
        ∀ m : ℕ, 1 ≤ m →
          Tendsto (fun N => primeAvg (frobeniusAngle a) (weyl m) N) atTop (𝓝 0)) :=
  ⟨frobeniusAngle_spec a hasse,
    satoTate_iff_weyl_tendsto_zero _ fun _ => ⟨Real.arccos_nonneg _, Real.arccos_le_pi _⟩⟩

/-! ### The Sato–Tate distribution in counting form

Sato–Tate equidistribution implies the concrete counting statement: the proportion of primes
`p ≤ N` whose Frobenius angle lies in `[α, β]` converges to the Sato–Tate measure of `[α, β]`.
-/

lemma stDensity_le (t : ℝ) : stDensity t ≤ 2 / π := by
  unfold stDensity
  have h1 : Real.sin t ^ 2 ≤ 1 := by
    rw [sq]; nlinarith [Real.neg_one_le_sin t, Real.sin_le_one t]
  have h2 : (0:ℝ) < 2 / π := by positivity
  nlinarith

lemma stDensity_integral_le {x y : ℝ} (hxy : x ≤ y) :
    (∫ t in x..y, stDensity t) ≤ (2 / π) * (y - x) := by
  have h : (∫ t in x..y, stDensity t) ≤ ∫ _t in x..y, (2 / π : ℝ) := by
    apply intervalIntegral.integral_mono_on hxy
      (continuous_stDensity.intervalIntegrable _ _) (continuous_const.intervalIntegrable _ _)
    exact fun t _ => stDensity_le t
  rw [intervalIntegral.integral_const, smul_eq_mul] at h
  linarith [h]

/-- A continuous trapezoidal function which is `1` on `[α, β]`, `0` outside `[α-δ, β+δ]`. -/
noncomputable def bumpUpper (α β δ : ℝ) : ℝ → ℝ :=
  fun t => max 0 (min 1 (min ((t - (α - δ)) / δ) (((β + δ) - t) / δ)))

/-- A continuous trapezoidal function which is `1` on `[α+δ, β-δ]`, `0` outside `[α, β]`. -/
noncomputable def bumpLower (α β δ : ℝ) : ℝ → ℝ :=
  fun t => max 0 (min 1 (min ((t - α) / δ) ((β - t) / δ)))

/-- The indicator function of the interval `[α, β]`. -/
noncomputable def indIcc (α β : ℝ) : ℝ → ℝ := fun t => if α ≤ t ∧ t ≤ β then 1 else 0

lemma continuous_bumpUpper (α β δ : ℝ) : Continuous (bumpUpper α β δ) := by
  unfold bumpUpper; fun_prop

lemma continuous_bumpLower (α β δ : ℝ) : Continuous (bumpLower α β δ) := by
  unfold bumpLower; fun_prop

lemma bumpUpper_nonneg (α β δ t : ℝ) : 0 ≤ bumpUpper α β δ t := le_max_left _ _

lemma bumpLower_nonneg (α β δ t : ℝ) : 0 ≤ bumpLower α β δ t := le_max_left _ _

lemma bumpUpper_le_one (α β δ t : ℝ) : bumpUpper α β δ t ≤ 1 :=
  max_le zero_le_one (min_le_left _ _)

lemma bumpLower_le_one (α β δ t : ℝ) : bumpLower α β δ t ≤ 1 :=
  max_le zero_le_one (min_le_left _ _)

lemma ind_le_bumpUpper {α β δ : ℝ} (hδ : 0 < δ) (t : ℝ) : indIcc α β t ≤ bumpUpper α β δ t := by
  unfold indIcc
  split_ifs with h
  · have h1 : (1:ℝ) ≤ (t - (α - δ)) / δ := by rw [le_div_iff₀ hδ]; linarith [h.1]
    have h2 : (1:ℝ) ≤ ((β + δ) - t) / δ := by rw [le_div_iff₀ hδ]; linarith [h.2]
    unfold bumpUpper
    rw [min_eq_left (le_min h1 h2), max_eq_right zero_le_one]
  · exact bumpUpper_nonneg _ _ _ _

lemma bumpLower_le_ind {α β δ : ℝ} (hδ : 0 < δ) (t : ℝ) : bumpLower α β δ t ≤ indIcc α β t := by
  unfold indIcc
  split_ifs with h
  · exact bumpLower_le_one _ _ _ _
  · unfold bumpLower
    rcases not_and_or.mp h with h1 | h1
    · have hle : (t - α) / δ ≤ 0 :=
        div_nonpos_of_nonpos_of_nonneg (by linarith [not_le.mp h1]) hδ.le
      rw [max_eq_left]
      exact le_trans (min_le_right _ _) (le_trans (min_le_left _ _) hle)
    · have hle : (β - t) / δ ≤ 0 :=
        div_nonpos_of_nonpos_of_nonneg (by linarith [not_le.mp h1]) hδ.le
      rw [max_eq_left]
      exact le_trans (min_le_right _ _) (le_trans (min_le_right _ _) hle)

lemma bumpUpper_eq_zero_left {α β δ t : ℝ} (hδ : 0 < δ) (ht : t ≤ α - δ) :
    bumpUpper α β δ t = 0 := by
  unfold bumpUpper
  have hle : (t - (α - δ)) / δ ≤ 0 := div_nonpos_of_nonpos_of_nonneg (by linarith) hδ.le
  exact max_eq_left (le_trans (min_le_right _ _) (le_trans (min_le_left _ _) hle))

lemma bumpUpper_eq_zero_right {α β δ t : ℝ} (hδ : 0 < δ) (ht : β + δ ≤ t) :
    bumpUpper α β δ t = 0 := by
  unfold bumpUpper
  have hle : ((β + δ) - t) / δ ≤ 0 := div_nonpos_of_nonpos_of_nonneg (by linarith) hδ.le
  exact max_eq_left (le_trans (min_le_right _ _) (le_trans (min_le_right _ _) hle))

lemma bumpLower_eq_one {α β δ t : ℝ} (hδ : 0 < δ) (h1 : α + δ ≤ t) (h2 : t ≤ β - δ) :
    bumpLower α β δ t = 1 := by
  unfold bumpLower
  have e1 : (1:ℝ) ≤ (t - α) / δ := by rw [le_div_iff₀ hδ]; linarith
  have e2 : (1:ℝ) ≤ (β - t) / δ := by rw [le_div_iff₀ hδ]; linarith
  rw [min_eq_left (le_min e1 e2), max_eq_right zero_le_one]

lemma stIntegral_bumpUpper_le {α β δ : ℝ} (hδ : 0 < δ) (hα : 0 ≤ α) (hαβ : α ≤ β) (hβ : β ≤ π) :
    stIntegral (bumpUpper α β δ) ≤ (∫ t in α..β, stDensity t) + (2 / π) * (2 * δ) := by
  set a1 : ℝ := max 0 (α - δ) with ha1def
  set a2 : ℝ := min π (β + δ) with ha2def
  have ha1_0 : 0 ≤ a1 := le_max_left _ _
  have ha1_α : a1 ≤ α := max_le hα (by linarith)
  have ha1_ge : α - δ ≤ a1 := le_max_right _ _
  have ha2_π : a2 ≤ π := min_le_left _ _
  have ha2_β : β ≤ a2 := le_min hβ (by linarith)
  have ha2_le : a2 ≤ β + δ := min_le_right _ _
  have hint : ∀ x y : ℝ, IntervalIntegrable (fun t => bumpUpper α β δ t * stDensity t)
      MeasureTheory.volume x y :=
    fun x y => ((continuous_bumpUpper α β δ).mul continuous_stDensity).intervalIntegrable x y
  have hsplit1 : (∫ t in (0:ℝ)..π, bumpUpper α β δ t * stDensity t)
      = (∫ t in (0:ℝ)..a1, bumpUpper α β δ t * stDensity t)
        + ∫ t in a1..π, bumpUpper α β δ t * stDensity t :=
    (intervalIntegral.integral_add_adjacent_intervals (hint 0 a1) (hint a1 π)).symm
  have hsplit2 : (∫ t in a1..π, bumpUpper α β δ t * stDensity t)
      = (∫ t in a1..a2, bumpUpper α β δ t * stDensity t)
        + ∫ t in a2..π, bumpUpper α β δ t * stDensity t :=
    (intervalIntegral.integral_add_adjacent_intervals (hint a1 a2) (hint a2 π)).symm
  have hz1 : (∫ t in (0:ℝ)..a1, bumpUpper α β δ t * stDensity t) = 0 := by
    rcases le_or_gt (α - δ) 0 with hc | hc
    · rw [show a1 = 0 from max_eq_left hc]; simp
    · have hae : a1 = α - δ := max_eq_right hc.le
      rw [show (∫ t in (0:ℝ)..a1, bumpUpper α β δ t * stDensity t)
          = ∫ _t in (0:ℝ)..a1, (0:ℝ) from intervalIntegral.integral_congr ?_]
      · simp
      · intro t ht
        rw [uIcc_of_le ha1_0] at ht
        show bumpUpper α β δ t * stDensity t = 0
        rw [bumpUpper_eq_zero_left hδ (by rw [← hae]; exact ht.2), zero_mul]
  have hz2 : (∫ t in a2..π, bumpUpper α β δ t * stDensity t) = 0 := by
    rcases le_or_gt π (β + δ) with hc | hc
    · rw [show a2 = π from min_eq_left hc]; simp
    · have hae : a2 = β + δ := min_eq_right hc.le
      rw [show (∫ t in a2..π, bumpUpper α β δ t * stDensity t)
          = ∫ _t in a2..π, (0:ℝ) from intervalIntegral.integral_congr ?_]
      · simp
      · intro t ht
        rw [uIcc_of_le ha2_π] at ht
        show bumpUpper α β δ t * stDensity t = 0
        rw [bumpUpper_eq_zero_right hδ (by rw [← hae]; exact ht.1), zero_mul]
  have hmid : (∫ t in a1..a2, bumpUpper α β δ t * stDensity t) ≤ ∫ t in a1..a2, stDensity t := by
    apply intervalIntegral.integral_mono_on (le_trans ha1_α (le_trans hαβ ha2_β))
      (hint a1 a2) (continuous_stDensity.intervalIntegrable _ _)
    intro t _
    nlinarith [bumpUpper_le_one α β δ t, stDensity_nonneg t, bumpUpper_nonneg α β δ t]
  have hadd : (∫ t in a1..a2, stDensity t)
      = (∫ t in a1..α, stDensity t) + (∫ t in α..β, stDensity t) + ∫ t in β..a2, stDensity t := by
    rw [intervalIntegral.integral_add_adjacent_intervals
      (continuous_stDensity.intervalIntegrable _ _) (continuous_stDensity.intervalIntegrable _ _),
      intervalIntegral.integral_add_adjacent_intervals
      (continuous_stDensity.intervalIntegrable _ _) (continuous_stDensity.intervalIntegrable _ _)]
  have hb1 : (∫ t in a1..α, stDensity t) ≤ (2 / π) * δ := by
    have h := stDensity_integral_le ha1_α
    have h2 : (0:ℝ) < 2 / π := by positivity
    nlinarith
  have hb2 : (∫ t in β..a2, stDensity t) ≤ (2 / π) * δ := by
    have h := stDensity_integral_le ha2_β
    have h2 : (0:ℝ) < 2 / π := by positivity
    nlinarith
  unfold stIntegral
  rw [hsplit1, hsplit2, hz1, hz2]
  rw [hadd] at hmid
  linarith

lemma stIntegral_bumpLower_ge {α β δ : ℝ} (hδ : 0 < δ) (hα : 0 ≤ α) (hαβ : α ≤ β) (hβ : β ≤ π) :
    (∫ t in α..β, stDensity t) - (2 / π) * (2 * δ) ≤ stIntegral (bumpLower α β δ) := by
  have hpi : (0:ℝ) < 2 / π := by positivity
  have hint : ∀ x y : ℝ, IntervalIntegrable (fun t => bumpLower α β δ t * stDensity t)
      MeasureTheory.volume x y :=
    fun x y => ((continuous_bumpLower α β δ).mul continuous_stDensity).intervalIntegrable x y
  have hnonneg : ∀ x y : ℝ, x ≤ y → 0 ≤ ∫ t in x..y, bumpLower α β δ t * stDensity t := by
    intro x y hxy
    exact intervalIntegral.integral_nonneg hxy
      (fun t _ => mul_nonneg (bumpLower_nonneg α β δ t) (stDensity_nonneg t))
  rcases lt_or_ge (β - δ) (α + δ) with hcase | hcase
  · have h1 : (∫ t in α..β, stDensity t) ≤ (2 / π) * (2 * δ) := by
      have h := stDensity_integral_le hαβ
      nlinarith
    have h2 : 0 ≤ stIntegral (bumpLower α β δ) := hnonneg 0 π Real.pi_pos.le
    linarith
  · set b1 : ℝ := α + δ with hb1
    set b2 : ℝ := β - δ with hb2
    have hb1_0 : 0 ≤ b1 := by rw [hb1]; linarith
    have hb2_π : b2 ≤ π := by rw [hb2]; linarith
    have hsplit1 : (∫ t in (0:ℝ)..π, bumpLower α β δ t * stDensity t)
        = (∫ t in (0:ℝ)..b1, bumpLower α β δ t * stDensity t)
          + ∫ t in b1..π, bumpLower α β δ t * stDensity t :=
      (intervalIntegral.integral_add_adjacent_intervals (hint 0 b1) (hint b1 π)).symm
    have hsplit2 : (∫ t in b1..π, bumpLower α β δ t * stDensity t)
        = (∫ t in b1..b2, bumpLower α β δ t * stDensity t)
          + ∫ t in b2..π, bumpLower α β δ t * stDensity t :=
      (intervalIntegral.integral_add_adjacent_intervals (hint b1 b2) (hint b2 π)).symm
    have hmid : (∫ t in b1..b2, bumpLower α β δ t * stDensity t)
        = ∫ t in b1..b2, stDensity t := by
      apply intervalIntegral.integral_congr
      intro t ht
      rw [uIcc_of_le hcase] at ht
      show bumpLower α β δ t * stDensity t = stDensity t
      rw [bumpLower_eq_one hδ ht.1 ht.2, one_mul]
    have hadd : (∫ t in α..β, stDensity t)
        = (∫ t in α..b1, stDensity t) + (∫ t in b1..b2, stDensity t)
          + ∫ t in b2..β, stDensity t := by
      rw [intervalIntegral.integral_add_adjacent_intervals
        (continuous_stDensity.intervalIntegrable _ _) (continuous_stDensity.intervalIntegrable _ _),
        intervalIntegral.integral_add_adjacent_intervals
        (continuous_stDensity.intervalIntegrable _ _) (continuous_stDensity.intervalIntegrable _ _)]
    have hc1 : (∫ t in α..b1, stDensity t) ≤ (2 / π) * δ := by
      have h := stDensity_integral_le (show α ≤ b1 by rw [hb1]; linarith)
      rw [hb1] at h
      nlinarith
    have hc2 : (∫ t in b2..β, stDensity t) ≤ (2 / π) * δ := by
      have h := stDensity_integral_le (show b2 ≤ β by rw [hb2]; linarith)
      rw [hb2] at h
      nlinarith
    have hz1 : 0 ≤ ∫ t in (0:ℝ)..b1, bumpLower α β δ t * stDensity t := hnonneg 0 b1 hb1_0
    have hz2 : 0 ≤ ∫ t in b2..π, bumpLower α β δ t * stDensity t := hnonneg b2 π hb2_π
    unfold stIntegral
    rw [hsplit1, hsplit2, hmid]
    linarith

/-- The proportion of primes `p ≤ N` whose angle `θ p` lies in `[α, β]`. -/
noncomputable def angleProportion (θ : ℕ → ℝ) (α β : ℝ) (N : ℕ) : ℝ :=
  (((primesUpTo N).filter (fun p => α ≤ θ p ∧ θ p ≤ β)).card : ℝ) / ((primesUpTo N).card : ℝ)

lemma angleProportion_eq_primeAvg (θ : ℕ → ℝ) (α β : ℝ) (N : ℕ) :
    angleProportion θ α β N = primeAvg θ (indIcc α β) N := by
  unfold angleProportion primeAvg indIcc
  congr 1
  rw [Finset.card_filter]
  push_cast
  rfl

lemma primeAvg_mono {θ : ℕ → ℝ} {f g : ℝ → ℝ} {N : ℕ} (hN : 2 ≤ N) (h : ∀ t, f t ≤ g t) :
    primeAvg θ f N ≤ primeAvg θ g N := by
  have hcard : 0 < ((primesUpTo N).card : ℝ) := by exact_mod_cast card_primesUpTo_pos hN
  have hsum : ∑ p ∈ primesUpTo N, f (θ p) ≤ ∑ p ∈ primesUpTo N, g (θ p) :=
    Finset.sum_le_sum fun p _ => h (θ p)
  simp only [primeAvg, div_eq_mul_inv]
  exact mul_le_mul_of_nonneg_right hsum (by positivity)

/-- **Sato–Tate in counting form.**  If the angles are Sato–Tate distributed, then for every
subinterval `[α, β] ⊆ [0, π]` the proportion of primes `p ≤ N` with `θ p ∈ [α, β]` converges
to the Sato–Tate measure `∫_α^β (2/π) sin²t dt` of that interval. -/
theorem satoTate_proportion_tendsto {θ : ℕ → ℝ} (h : SatoTateDistributed θ)
    {α β : ℝ} (hα : 0 ≤ α) (hαβ : α ≤ β) (hβ : β ≤ π) :
    Tendsto (fun N => angleProportion θ α β N) atTop (𝓝 (∫ t in α..β, stDensity t)) := by
  rw [Metric.tendsto_atTop]
  intro ε hε
  set I : ℝ := ∫ t in α..β, stDensity t with hI
  set δ : ℝ := min 1 (ε * π / 32) with hδdef
  have hδ : 0 < δ := lt_min one_pos (by positivity)
  have hδsmall : (2 / π) * (2 * δ) ≤ ε / 8 := by
    have h1 : δ ≤ ε * π / 32 := min_le_right _ _
    have hπ : (0:ℝ) < π := Real.pi_pos
    rw [div_mul_eq_mul_div, mul_comm]
    rw [div_le_iff₀ hπ]
    nlinarith
  have hup := h (bumpUpper α β δ) (continuous_bumpUpper α β δ)
  have hlo := h (bumpLower α β δ) (continuous_bumpLower α β δ)
  rw [Metric.tendsto_atTop] at hup hlo
  obtain ⟨N₁, hN₁⟩ := hup (ε / 8) (by linarith)
  obtain ⟨N₂, hN₂⟩ := hlo (ε / 8) (by linarith)
  refine ⟨max (max N₁ N₂) 2, fun N hN => ?_⟩
  have hN2 : 2 ≤ N := le_trans (le_max_right _ _) hN
  have hNa : N₁ ≤ N := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hN
  have hNb : N₂ ≤ N := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hN
  have h1 : |primeAvg θ (bumpUpper α β δ) N - stIntegral (bumpUpper α β δ)| < ε / 8 := by
    have := hN₁ N hNa; rwa [Real.dist_eq] at this
  have h2 : |primeAvg θ (bumpLower α β δ) N - stIntegral (bumpLower α β δ)| < ε / 8 := by
    have := hN₂ N hNb; rwa [Real.dist_eq] at this
  have hupI := stIntegral_bumpUpper_le hδ hα hαβ hβ
  have hloI := stIntegral_bumpLower_ge hδ hα hαβ hβ
  have hmono1 : primeAvg θ (indIcc α β) N ≤ primeAvg θ (bumpUpper α β δ) N :=
    primeAvg_mono hN2 (ind_le_bumpUpper hδ)
  have hmono2 : primeAvg θ (bumpLower α β δ) N ≤ primeAvg θ (indIcc α β) N :=
    primeAvg_mono hN2 (bumpLower_le_ind hδ)
  rw [Real.dist_eq, angleProportion_eq_primeAvg]
  rw [abs_lt] at h1 h2 ⊢
  constructor <;> [linarith; linarith]


/-- **Sato–Tate for Frobenius angles, counting form.**  If the symmetric power Weyl sums of a
trace-of-Frobenius function tend to `0`, then for every `[α, β] ⊆ [0, π]` the proportion of
primes `p ≤ N` whose Frobenius angle lies in `[α, β]` tends to the Sato–Tate measure
`∫_α^β (2/π) sin²t dt` of the interval. -/
theorem sato_tate_counting (a : ℕ → ℤ)
    (hW : ∀ m : ℕ, 1 ≤ m →
      Tendsto (fun N => primeAvg (frobeniusAngle a) (weyl m) N) atTop (𝓝 0))
    {α β : ℝ} (hα : 0 ≤ α) (hαβ : α ≤ β) (hβ : β ≤ π) :
    Tendsto (fun N => angleProportion (frobeniusAngle a) α β N) atTop
      (𝓝 (∫ t in α..β, stDensity t)) :=
  satoTate_proportion_tendsto
    ((satoTate_iff_weyl_tendsto_zero _
      fun _ => ⟨Real.arccos_nonneg _, Real.arccos_le_pi _⟩).mpr hW) hα hαβ hβ

end Math2

