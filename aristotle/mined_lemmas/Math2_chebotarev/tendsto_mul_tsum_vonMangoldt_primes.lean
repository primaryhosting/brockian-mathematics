import Mathlib

/-!
# Dirichlet density of primes in an invertible residue class

This file proves a quantitative form of Dirichlet's theorem on primes in arithmetic
progressions, in the logarithmic (Dirichlet) sense: if `a` is a unit of `ZMod q`, then

`(x - 1) * ∑' p prime, p ≡ a [q], log p / p ^ x → 1 / φ(q)`   as `x → 1⁺`.

This is the analytic input for the density form of the Chebotarev theorem for cyclotomic
extensions proved in `RequestProject.Main`.

The proof combines the results of `Mathlib.NumberTheory.LSeries.PrimesInAP`: the L-series of
the von Mangoldt function restricted to the residue class `a` has a simple pole at `s = 1`
with residue `1/φ(q)`, and the contribution of the proper prime powers is bounded.
-/

open scoped Classical

open ArithmeticFunction ArithmeticFunction.vonMangoldt Filter Topology Complex

namespace Math2

/-- The Dirichlet-density statement for primes in the residue class `a` mod `q`, in the form
of the logarithmically weighted prime sum: as `x → 1⁺`,
`(x - 1) * ∑_{p ≡ a (q)} (log p) p ^ (-x) → 1 / φ(q)`. -/

theorem tendsto_mul_tsum_vonMangoldt_primes {q : ℕ} [NeZero q] {a : ZMod q} (ha : IsUnit a) :
    Tendsto (fun x : ℝ => (x - 1) *
        ∑' k : ℕ, (if k.Prime then residueClass a k else 0) / (k : ℝ) ^ x)
      (𝓝[>] (1 : ℝ)) (𝓝 ((q.totient : ℝ)⁻¹)) := by
  -- summability of the L-series of the restricted von Mangoldt function for `x > 1`
  have hsummA : ∀ {x : ℝ}, 1 < x → Summable (fun k : ℕ => residueClass a k / (k : ℝ) ^ x) :=
    fun {x} hx => LSeries.summable_real_of_abscissaOfAbsConv_lt
      ((abscissaOfAbsConv_residueClass_le_one a).trans_lt (by exact_mod_cast hx))
  have hleP : ∀ (x : ℝ) (k : ℕ), (if k.Prime then residueClass a k else 0) / (k : ℝ) ^ x ≤
      residueClass a k / (k : ℝ) ^ x := by
    intro x k; gcongr; split
    · exact le_rfl
    · exact residueClass_nonneg a k
  have hleN : ∀ (x : ℝ) (k : ℕ), (if k.Prime then 0 else residueClass a k) / (k : ℝ) ^ x ≤
      residueClass a k / (k : ℝ) ^ x := by
    intro x k; gcongr; split
    · exact residueClass_nonneg a k
    · exact le_rfl
  have hnnP : ∀ (x : ℝ) (k : ℕ), 0 ≤ (if k.Prime then residueClass a k else 0) / (k : ℝ) ^ x := by
    intro x k
    refine div_nonneg ?_ (Real.rpow_nonneg (Nat.cast_nonneg k) x)
    split
    · exact residueClass_nonneg a k
    · exact le_rfl
  have hnnN : ∀ (x : ℝ) (k : ℕ), 0 ≤ (if k.Prime then 0 else residueClass a k) / (k : ℝ) ^ x := by
    intro x k
    refine div_nonneg ?_ (Real.rpow_nonneg (Nat.cast_nonneg k) x)
    split
    · exact le_rfl
    · exact residueClass_nonneg a k
  have hsummP : ∀ {x : ℝ}, 1 < x →
      Summable (fun k : ℕ => (if k.Prime then residueClass a k else 0) / (k : ℝ) ^ x) :=
    fun {x} hx => Summable.of_nonneg_of_le (hnnP x) (hleP x) (hsummA hx)
  have hsummN : ∀ {x : ℝ}, 1 < x →
      Summable (fun k : ℕ => (if k.Prime then 0 else residueClass a k) / (k : ℝ) ^ x) :=
    fun {x} hx => Summable.of_nonneg_of_le (hnnN x) (hleN x) (hsummA hx)
  -- splitting the series into its prime and non-prime parts
  have hsplit : ∀ {x : ℝ}, 1 < x →
      ∑' k : ℕ, (if k.Prime then residueClass a k else 0) / (k : ℝ) ^ x =
        (∑' k : ℕ, residueClass a k / (k : ℝ) ^ x) -
          ∑' k : ℕ, (if k.Prime then 0 else residueClass a k) / (k : ℝ) ^ x := by
    intro x hx
    rw [eq_sub_iff_add_eq, ← (hsummP hx).tsum_add (hsummN hx)]
    refine tsum_congr fun k => ?_
    rw [← add_div]
    congr 1
    split <;> simp
  -- the pole at `s = 1` with residue `1/φ(q)`
  have hA : ∀ {x : ℝ}, 1 < x → ∑' k : ℕ, residueClass a k / (k : ℝ) ^ x =
      (LFunctionResidueClassAux a x).re + (q.totient : ℝ)⁻¹ / (x - 1) := by
    intro x hx
    refine ofReal_injective ?_
    simp only [ofReal_tsum, ofReal_div, ofReal_cpow (Nat.cast_nonneg _), ofReal_natCast,
      ofReal_add, ofReal_inv, ofReal_sub, ofReal_one]
    simp_rw [← LFunctionResidueClassAux_real ha hx,
      eqOn_LFunctionResidueClassAux ha <| Set.mem_setOf.mpr (ofReal_re x ▸ hx), sub_add_cancel,
      LSeries, LSeries.term]
    refine tsum_congr fun k => ?_
    split_ifs with hk
    · simp only [hk, residueClass_apply_zero, ofReal_zero, zero_div]
    · rfl
  -- the contribution of the proper prime powers is uniformly bounded
  set D : ℝ := ∑' k : ℕ, (if k.Prime then 0 else residueClass a k) / (k : ℝ) with hDdef
  have hCbound : ∀ {x : ℝ}, 1 < x →
      ∑' k : ℕ, (if k.Prime then 0 else residueClass a k) / (k : ℝ) ^ x ≤ D := by
    intro x hx
    refine (hsummN hx).tsum_le_tsum (fun k => ?_) (summable_residueClass_non_primes_div a)
    rcases Nat.eq_zero_or_pos k with rfl | hk
    · simp
    · have h1 : (1 : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk
      have hnum : 0 ≤ (if k.Prime then 0 else residueClass a k) := by
        split
        · exact le_rfl
        · exact residueClass_nonneg a k
      have hle : (k : ℝ) ≤ (k : ℝ) ^ x := by
        conv_lhs => rw [← Real.rpow_one (k : ℝ)]
        exact Real.rpow_le_rpow_of_exponent_le h1 hx.le
      exact div_le_div_of_nonneg_left hnum (by linarith) hle
  -- the auxiliary function is continuous at `1`, so it does not contribute in the limit
  have hT1 : Tendsto (fun x : ℝ => (x - 1) * (LFunctionResidueClassAux a x).re)
      (𝓝[>] (1 : ℝ)) (𝓝 0) := by
    have hcont : ContinuousOn (fun x : ℝ ↦ (LFunctionResidueClassAux a x).re) (Set.Icc 1 2) :=
      continuous_re.continuousOn.comp (t := Set.univ) (continuousOn_LFunctionResidueClassAux a)
        (fun ⦃x⦄ _ ↦ trivial) |>.comp continuous_ofReal.continuousOn fun x hx ↦ by
          simpa only [Set.mem_setOf_eq, ofReal_re] using hx.1
    have h1 : Tendsto (fun x : ℝ => (LFunctionResidueClassAux a x).re) (𝓝[>] (1 : ℝ))
        (𝓝 ((LFunctionResidueClassAux a (1 : ℝ)).re)) := by
      refine (hcont 1 (by norm_num)).tendsto.mono_left ?_
      rw [← nhdsWithin_Ioc_eq_nhdsGT (by norm_num : (1 : ℝ) < 2)]
      exact nhdsWithin_mono _ Set.Ioc_subset_Icc_self
    have h2 : Tendsto (fun x : ℝ => x - 1) (𝓝[>] (1 : ℝ)) (𝓝 0) := by
      have hc : Continuous fun x : ℝ => x - 1 := by fun_prop
      simpa using (hc.tendsto 1).mono_left nhdsWithin_le_nhds
    simpa using h2.mul h1
  -- the prime powers do not contribute in the limit either
  have hT2 : Tendsto (fun x : ℝ =>
      (x - 1) * ∑' k : ℕ, (if k.Prime then 0 else residueClass a k) / (k : ℝ) ^ x)
      (𝓝[>] (1 : ℝ)) (𝓝 0) := by
    have h2 : Tendsto (fun x : ℝ => (x - 1) * D) (𝓝[>] (1 : ℝ)) (𝓝 0) := by
      have hc : Continuous fun x : ℝ => (x - 1) * D := by fun_prop
      simpa using (hc.tendsto 1).mono_left nhdsWithin_le_nhds
    refine squeeze_zero' ?_ ?_ h2
    · filter_upwards [self_mem_nhdsWithin] with x hx
      have hx1 : (0 : ℝ) ≤ x - 1 := by simp only [Set.mem_Ioi] at hx; linarith
      exact mul_nonneg hx1 (tsum_nonneg (hnnN x))
    · filter_upwards [self_mem_nhdsWithin] with x hx
      have hx1 : (0 : ℝ) ≤ x - 1 := by simp only [Set.mem_Ioi] at hx; linarith
      exact mul_le_mul_of_nonneg_left (hCbound hx) hx1
  -- putting everything together
  have hcomb := (hT1.add (tendsto_const_nhds (x := ((q.totient : ℝ)⁻¹)))).sub hT2
  simp only [zero_add, sub_zero] at hcomb
  refine hcomb.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with x hx
  have hx1 : (1 : ℝ) < x := hx
  have hxne : x - 1 ≠ 0 := by
    intro h
    exact absurd (by linarith : x = 1) (by linarith)
  rw [hsplit hx1, hA hx1, mul_sub, mul_add, mul_div_cancel₀ _ hxne]

/-- Changing the summation set on a finite set of indices does not affect the density limit. -/
