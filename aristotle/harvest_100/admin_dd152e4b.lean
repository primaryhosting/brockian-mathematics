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
theorem tendsto_mul_tsum_indicator_of_finite_symmDiff {S T : Set ℕ} {F : Finset ℕ} {c : ℝ}
    (hF : ∀ k ∉ F, (k ∈ S ↔ k ∈ T))
    (hTsumm : ∀ x : ℝ, 1 < x →
      Summable (Set.indicator T (fun k : ℕ => Real.log k / (k : ℝ) ^ x)))
    (hT : Tendsto (fun x : ℝ => (x - 1) *
        ∑' k : ℕ, Set.indicator T (fun k : ℕ => Real.log k / (k : ℝ) ^ x) k)
      (𝓝[>] (1 : ℝ)) (𝓝 c)) :
    Tendsto (fun x : ℝ => (x - 1) *
        ∑' k : ℕ, Set.indicator S (fun k : ℕ => Real.log k / (k : ℝ) ^ x) k)
      (𝓝[>] (1 : ℝ)) (𝓝 c) := by
  classical
  set g : ℝ → ℕ → ℝ := fun x k => Real.log k / (k : ℝ) ^ x with hgdef
  set u : ℝ → ℕ → ℝ := fun x k => Set.indicator S (g x) k - Set.indicator T (g x) k with hudef
  have husupp : ∀ (x : ℝ) (k : ℕ), k ∉ F → u x k = 0 := by
    intro x k hk
    by_cases hS : k ∈ S
    · have hTk : k ∈ T := (hF k hk).mp hS
      simp [hudef, Set.indicator_of_mem hS, Set.indicator_of_mem hTk]
    · have hTk : k ∉ T := fun h => hS ((hF k hk).mpr h)
      simp [hudef, Set.indicator_of_notMem hS, Set.indicator_of_notMem hTk]
  have husumm : ∀ x : ℝ, Summable (u x) := fun x => summable_of_ne_finset_zero (husupp x)
  have hutsum : ∀ x : ℝ, ∑' k : ℕ, u x k = ∑ k ∈ F, u x k := fun x => tsum_eq_sum (husupp x)
  -- the sum over `S` differs from the sum over `T` by the finite correction
  have hsplit : ∀ x : ℝ, 1 < x → ∑' k : ℕ, Set.indicator S (g x) k =
      (∑' k : ℕ, Set.indicator T (g x) k) + ∑ k ∈ F, u x k := by
    intro x hx
    rw [← hutsum x, ← (hTsumm x hx).tsum_add (husumm x)]
    exact tsum_congr fun k => by simp [hudef]
  -- the finite correction is negligible in the limit
  have hbound : ∀ (x : ℝ) (k : ℕ), 1 ≤ x → |u x k| ≤ Real.log k := by
    intro x k hx
    rcases Nat.eq_zero_or_pos k with rfl | hk
    · simp [hudef, hgdef]
    · have hk1 : (1 : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk
      have hlog : 0 ≤ Real.log k := Real.log_nonneg hk1
      have hpow : (1 : ℝ) ≤ (k : ℝ) ^ x := Real.one_le_rpow hk1 (by linarith)
      have hgle : |g x k| ≤ Real.log k := by
        rw [hgdef]
        simp only [abs_div, abs_of_nonneg hlog,
          abs_of_nonneg (Real.rpow_nonneg (Nat.cast_nonneg k) x)]
        exact div_le_self hlog hpow
      have hgnn : 0 ≤ g x k := div_nonneg hlog (Real.rpow_nonneg (Nat.cast_nonneg k) x)
      by_cases hS : k ∈ S <;> by_cases hTk : k ∈ T <;>
        simp only [hudef, Set.indicator_of_mem, Set.indicator_of_notMem, hS, hTk, sub_zero,
          zero_sub, sub_self, abs_zero, abs_neg, not_false_eq_true] <;>
        simp_all [abs_of_nonneg hgnn]
  have hT2 : Tendsto (fun x : ℝ => (x - 1) * ∑ k ∈ F, u x k) (𝓝[>] (1 : ℝ)) (𝓝 0) := by
    set M : ℝ := ∑ k ∈ F, Real.log k with hMdef
    have hlim : Tendsto (fun x : ℝ => |x - 1| * M) (𝓝[>] (1 : ℝ)) (𝓝 0) := by
      have hc : Continuous fun x : ℝ => |x - 1| * M := by fun_prop
      simpa using (hc.tendsto 1).mono_left nhdsWithin_le_nhds
    refine squeeze_zero_norm' ?_ hlim
    filter_upwards [self_mem_nhdsWithin] with x hx
    have hx1 : (1 : ℝ) ≤ x := le_of_lt hx
    have hsum : |∑ k ∈ F, u x k| ≤ M :=
      (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun k _ => hbound x k hx1)
    calc ‖(x - 1) * ∑ k ∈ F, u x k‖ = |x - 1| * |∑ k ∈ F, u x k| := by
          simp [abs_mul]
      _ ≤ |x - 1| * M := by
          exact mul_le_mul_of_nonneg_left hsum (abs_nonneg _)
  have hcomb := hT.add hT2
  rw [add_zero] at hcomb
  refine hcomb.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with x hx
  rw [hsplit x hx, mul_add]

end Math2

/-
# Chebotarev
Category: Frontier Math
Target: Math2.chebotarev
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Chebotarev
Category: Frontier Math
Target: Math2.chebotarev
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
set_option synthInstance.maxHeartbeats 400000
set_option synthInstance.maxSize 128

set_option relaxedAutoImplicit false
set_option autoImplicit false

set_option grind.warning false

open NumberField

namespace Math2

/-!
## Generalities on primes of a number field lying over a rational prime
-/

/-- A prime of `𝓞 L` lying over a rational prime has finite residue ring. -/
theorem finite_quotient_of_under_eq_span (L : Type) [Field L] [NumberField L] {p : ℕ}
    (hp : p.Prime) {Q : Ideal (𝓞 L)} (hQp : Ideal.under ℤ Q = Ideal.span {(p : ℤ)}) :
    Finite (𝓞 L ⧸ Q) := by
  have hinj := FaithfulSMul.algebraMap_injective ℤ (𝓞 L)
  have hne : Q ≠ ⊥ := by
    rintro rfl
    have hmem : (p : ℤ) ∈ Ideal.span {(p : ℤ)} := Ideal.subset_span rfl
    rw [← hQp, Ideal.mem_comap] at hmem
    simp only [Ideal.mem_bot] at hmem
    have : (p : ℤ) = 0 := hinj (by simpa using hmem)
    exact hp.ne_zero (by exact_mod_cast this)
  exact Ideal.finiteQuotientOfFreeOfNeBot Q hne

/-- Over a number field `L`, every rational prime `p` lies under some prime ideal `Q`
of the ring of integers, and the residue ring `𝓞 L ⧸ Q` is finite. -/
theorem exists_isPrime_under_eq_span (L : Type) [Field L] [NumberField L] (p : ℕ)
    (hp : p.Prime) :
    ∃ Q : Ideal (𝓞 L), Q.IsPrime ∧ Ideal.under ℤ Q = Ideal.span {(p : ℤ)} ∧
      Finite (𝓞 L ⧸ Q) := by
  have hinj := FaithfulSMul.algebraMap_injective ℤ (𝓞 L)
  have hP : (Ideal.span {(p : ℤ)}).IsPrime := by
    rw [Ideal.span_singleton_prime (by exact_mod_cast hp.ne_zero)]
    exact Nat.prime_iff_prime_int.mp hp
  obtain ⟨Q, -, hQ1, hQ2⟩ := Ideal.exists_ideal_over_prime_of_isIntegral (R := ℤ) (S := 𝓞 L)
    (Ideal.span {(p : ℤ)}) ⊥ (by
      intro x hx
      have hx' : algebraMap ℤ (𝓞 L) x = 0 := by simpa [Ideal.mem_comap] using hx
      have hx0 : x = 0 := hinj (by simpa using hx')
      simp [hx0])
  exact ⟨Q, hQ1, hQ2, finite_quotient_of_under_eq_span L hp hQ2⟩

/-- If `Q` lies over the rational prime `p` and `p ∤ n`, then `n` is not in `Q`. -/
theorem cast_not_mem_of_not_dvd (L : Type) [Field L] [NumberField L] {p n : ℕ}
    {Q : Ideal (𝓞 L)} (hQp : Ideal.under ℤ Q = Ideal.span {(p : ℤ)}) (hpn : ¬ p ∣ n) :
    (n : 𝓞 L) ∉ Q := by
  intro hmem
  have h1 : (n : ℤ) ∈ Ideal.under ℤ Q := by
    simpa [Ideal.under, Ideal.mem_comap] using hmem
  rw [hQp, Ideal.mem_span_singleton] at h1
  exact hpn (by exact_mod_cast h1)

/-- A Frobenius element at a prime `Q` above `p` raises roots of unity of order prime to `p`
to their `p`-th power. -/
theorem smul_eq_pow_of_isArithFrobAt (L : Type) [Field L] [NumberField L] {p : ℕ}
    {Q : Ideal (𝓞 L)} (hQp : Ideal.under ℤ Q = Ideal.span {(p : ℤ)}) {σ : L ≃ₐ[ℚ] L}
    (H : IsArithFrobAt ℤ σ Q) {n : ℕ} {ξ : 𝓞 L} (hξ : ξ ^ n = 1) (hn : (n : 𝓞 L) ∉ Q) :
    σ • ξ = ξ ^ p := by
  have hcard : Nat.card (ℤ ⧸ Ideal.under ℤ Q) = p := by
    rw [hQp, Nat.card_congr (Int.quotientSpanEquivZMod (p : ℤ)).toEquiv]
    simp
  have h := H.apply_of_pow_eq_one hξ hn
  rwa [hcard] at h

/-- If `x ^ n = 1` then the powers of `x` only depend on the exponent modulo `n`. -/
theorem pow_eq_pow_of_modEq {M : Type*} [CommMonoid M] {x : M} {n a b : ℕ} (hx : x ^ n = 1)
    (h : a ≡ b [MOD n]) : x ^ a = x ^ b := by
  have key : ∀ c : ℕ, x ^ c = x ^ (c % n) := by
    intro c
    conv_lhs => rw [← Nat.div_add_mod c n]
    rw [pow_add, pow_mul, hx, one_pow, one_mul]
  rw [key a, key b, h]

/-- A prime `p` whose class in `ZMod n` is a unit does not divide `n`. -/
theorem not_dvd_of_isUnit_natCast {n p : ℕ} [NeZero n] (hp : 1 < p)
    (h : IsUnit ((p : ZMod n))) : ¬ p ∣ n := by
  intro hdvd
  have hcop : p.Coprime n := (ZMod.isUnit_iff_coprime p n).mp h
  have hdvd1 : p ∣ Nat.gcd p n := Nat.dvd_gcd dvd_rfl hdvd
  rw [hcop] at hdvd1
  exact hp.ne' (Nat.dvd_one.mp hdvd1)

/-!
## Frobenius elements in cyclotomic extensions of `ℚ`
-/

section Cyclotomic

variable {n : ℕ} [NeZero n] (L : Type) [Field L] [NumberField L] [IsCyclotomicExtension {n} ℚ L]

/-- A choice of primitive `n`-th root of unity in `L = ℚ(ζₙ)`. -/
noncomputable abbrev zeta : L := IsCyclotomicExtension.zeta n ℚ L

theorem isPrimitiveRoot_zeta : IsPrimitiveRoot (zeta (n := n) L) n :=
  IsCyclotomicExtension.zeta_spec n ℚ L

/-- The primitive root of unity, viewed as an algebraic integer. -/
theorem exists_ringOfIntegers_coe_eq_zeta :
    ∃ ξ : 𝓞 L, (ξ : L) = zeta (n := n) L ∧ ξ ^ n = 1 := by
  have hζ := isPrimitiveRoot_zeta (n := n) L
  refine ⟨⟨zeta (n := n) L, hζ.isIntegral (NeZero.pos n)⟩, rfl, ?_⟩
  have : (((⟨zeta (n := n) L, hζ.isIntegral (NeZero.pos n)⟩ : 𝓞 L) ^ n : 𝓞 L) : L) =
      ((1 : 𝓞 L) : L) := by
    push_cast [hζ.pow_eq_one]
    rfl
  exact Subtype.ext this

/-- The unit of `ZMod n` attached to a Galois automorphism `σ` of `ℚ(ζₙ)`, characterised by
`σ ζₙ = ζₙ ^ a`.  This is the standard isomorphism `Gal(ℚ(ζₙ)/ℚ) ≃ (ZMod n)ˣ`. -/
noncomputable def cycloUnit (σ : L ≃ₐ[ℚ] L) : (ZMod n)ˣ :=
  IsPrimitiveRoot.autToPow ℚ (isPrimitiveRoot_zeta (n := n) L) σ

theorem zeta_pow_cycloUnit (σ : L ≃ₐ[ℚ] L) :
    zeta (n := n) L ^ ((cycloUnit (n := n) L σ : ZMod n)).val = σ (zeta (n := n) L) :=
  (isPrimitiveRoot_zeta (n := n) L).autToPow_spec ℚ σ

/-- If two automorphisms send `ζₙ` to the same power of `ζₙ`, they are equal. -/
theorem eq_of_zeta_eq {σ τ : L ≃ₐ[ℚ] L} (h : σ (zeta (n := n) L) = τ (zeta (n := n) L)) :
    σ = τ := by
  have hζ := isPrimitiveRoot_zeta (n := n) L
  have hvals : ((IsPrimitiveRoot.autToPow ℚ hζ) σ : ZMod n).val =
      ((IsPrimitiveRoot.autToPow ℚ hζ) τ : ZMod n).val := by
    refine hζ.pow_inj (ZMod.val_lt _) (ZMod.val_lt _) ?_
    rw [hζ.autToPow_spec ℚ σ, hζ.autToPow_spec ℚ τ, h]
  exact hζ.autToPow_injective ℚ (Units.ext (ZMod.val_injective n hvals))

/-- **Key step, one direction.** If `σ` is the Frobenius at a prime `Q` above a prime `p` that
does not divide `n`, then `σ` raises `ζₙ` to the `p`-th power. -/
theorem apply_zeta_eq_pow_of_isArithFrobAt {p : ℕ} {Q : Ideal (𝓞 L)}
    (hQp : Ideal.under ℤ Q = Ideal.span {(p : ℤ)}) (hpn : ¬ p ∣ n) {σ : L ≃ₐ[ℚ] L}
    (H : IsArithFrobAt ℤ σ Q) :
    σ (zeta (n := n) L) = zeta (n := n) L ^ p := by
  obtain ⟨ξ, hξc, hξpow⟩ := exists_ringOfIntegers_coe_eq_zeta (n := n) L
  have hnQ : (n : 𝓞 L) ∉ Q := cast_not_mem_of_not_dvd L hQp hpn
  have hsmul : σ • ξ = ξ ^ p := smul_eq_pow_of_isArithFrobAt L hQp H hξpow hnQ
  have h : ((σ • ξ : 𝓞 L) : L) = ((ξ ^ p : 𝓞 L) : L) := congrArg (fun y : 𝓞 L => (y : L)) hsmul
  have hl : ((σ • ξ : 𝓞 L) : L) = σ (zeta (n := n) L) := by rw [← hξc]; rfl
  rw [hl] at h
  simpa [hξc] using h

/-- **Key step, other direction.** Let `σ` be an automorphism of `L = ℚ(ζₙ)` sending `ζₙ` to
`ζₙ ^ p`, where `p` is a prime not dividing `n`. Then `σ` is the Frobenius element at *every*
prime `Q` of `𝓞 L` lying over `p`, i.e. `σ x ≡ x ^ p (mod Q)` for all `x : 𝓞 L`. -/
theorem isArithFrobAt_of_zeta_pow (σ : L ≃ₐ[ℚ] L) {p : ℕ} (hp : p.Prime) (hpn : ¬ p ∣ n)
    (hσ : σ (zeta (n := n) L) = zeta (n := n) L ^ p)
    (Q : Ideal (𝓞 L)) (hQprime : Q.IsPrime)
    (hQp : Ideal.under ℤ Q = Ideal.span {(p : ℤ)}) :
    IsArithFrobAt ℤ σ Q := by
  haveI : IsGalois ℚ L := IsCyclotomicExtension.isGalois {n} ℚ L
  haveI := hQprime
  haveI : Finite (𝓞 L ⧸ Q) := finite_quotient_of_under_eq_span L hp hQp
  set τ : L ≃ₐ[ℚ] L := arithFrobAt ℤ (L ≃ₐ[ℚ] L) Q with hτdef
  have hτ : IsArithFrobAt ℤ τ Q :=
    IsArithFrobAt.arithFrobAt (R := ℤ) (G := L ≃ₐ[ℚ] L) (S := 𝓞 L) Q
  have hτζ : τ (zeta (n := n) L) = zeta (n := n) L ^ p :=
    apply_zeta_eq_pow_of_isArithFrobAt L hQp hpn hτ
  have hτσ : τ = σ := eq_of_zeta_eq L (by rw [hτζ, hσ])
  rwa [hτσ] at hτ

/-- **Frobenius criterion.** For a prime `p` not dividing `n` and a prime `Q` of `𝓞 L` above
`p`, the automorphism `σ` is the Frobenius at `Q` if and only if the class of `p` in `ZMod n`
is the unit attached to `σ`. In particular the Frobenius depends only on `p`, not on `Q`. -/
theorem isArithFrobAt_iff (σ : L ≃ₐ[ℚ] L) {p : ℕ} (hp : p.Prime) (hpn : ¬ p ∣ n)
    (Q : Ideal (𝓞 L)) (hQprime : Q.IsPrime)
    (hQp : Ideal.under ℤ Q = Ideal.span {(p : ℤ)}) :
    IsArithFrobAt ℤ σ Q ↔ (p : ZMod n) = (cycloUnit (n := n) L σ : ZMod n) := by
  have hζ := isPrimitiveRoot_zeta (n := n) L
  set m : ℕ := ((cycloUnit (n := n) L σ : ZMod n)).val with hmdef
  have hmcast : ((m : ℕ) : ZMod n) = (cycloUnit (n := n) L σ : ZMod n) :=
    ZMod.natCast_zmod_val _
  have hσζ : zeta (n := n) L ^ m = σ (zeta (n := n) L) := zeta_pow_cycloUnit (n := n) L σ
  constructor
  · intro H
    have h1 : σ (zeta (n := n) L) = zeta (n := n) L ^ p :=
      apply_zeta_eq_pow_of_isArithFrobAt L hQp hpn H
    have h2 : zeta (n := n) L ^ (p % n) = zeta (n := n) L ^ (m % n) := by
      rw [pow_eq_pow_of_modEq hζ.pow_eq_one (Nat.mod_modEq p n),
        pow_eq_pow_of_modEq hζ.pow_eq_one (Nat.mod_modEq m n), ← h1, hσζ]
    have h3 : p % n = m % n :=
      hζ.pow_inj (Nat.mod_lt _ (NeZero.pos n)) (Nat.mod_lt _ (NeZero.pos n)) h2
    have : ((p : ℕ) : ZMod n) = ((m : ℕ) : ZMod n) := (ZMod.natCast_eq_natCast_iff p m n).mpr h3
    rw [this, hmcast]
  · intro h
    have hpm : p ≡ m [MOD n] := (ZMod.natCast_eq_natCast_iff p m n).mp (by rw [h, hmcast])
    refine isArithFrobAt_of_zeta_pow L σ hp hpn ?_ Q hQprime hQp
    rw [← hσζ]
    exact (pow_eq_pow_of_modEq hζ.pow_eq_one hpm).symm

/-- The set of primes whose Frobenius (at some, equivalently any, prime above it) is `σ`,
away from the primes dividing `n`, is the set of primes in the residue class attached to `σ`. -/
theorem exists_isArithFrobAt_iff (σ : L ≃ₐ[ℚ] L) {p : ℕ} (hp : p.Prime) (hpn : ¬ p ∣ n) :
    (∃ Q : Ideal (𝓞 L), Q.IsPrime ∧ Ideal.under ℤ Q = Ideal.span {(p : ℤ)} ∧
      IsArithFrobAt ℤ σ Q) ↔ (p : ZMod n) = (cycloUnit (n := n) L σ : ZMod n) := by
  obtain ⟨Q₀, hQ₀prime, hQ₀p, -⟩ := exists_isPrime_under_eq_span L p hp
  constructor
  · rintro ⟨Q, hQprime, hQp, H⟩
    exact (isArithFrobAt_iff L σ hp hpn Q hQprime hQp).mp H
  · intro h
    exact ⟨Q₀, hQ₀prime, hQ₀p, (isArithFrobAt_iff L σ hp hpn Q₀ hQ₀prime hQ₀p).mpr h⟩

end Cyclotomic

/-- **Chebotarev density theorem** (qualitative form, cyclotomic case), general version:
for `L = ℚ(ζₙ)` and any `σ` in the Galois group, there are infinitely many rational primes `p`
such that `σ` is the Frobenius element at every prime of `𝓞 L` lying over `p` (and at least one
such prime exists). -/
theorem chebotarev_cyclotomic (n : ℕ) [NeZero n] (L : Type) [Field L] [NumberField L]
    [IsCyclotomicExtension {n} ℚ L] (σ : L ≃ₐ[ℚ] L) :
    {p : ℕ | p.Prime ∧ (∃ Q : Ideal (𝓞 L), Q.IsPrime ∧ Ideal.under ℤ Q = Ideal.span {(p : ℤ)}) ∧
      ∀ Q : Ideal (𝓞 L), Q.IsPrime → Ideal.under ℤ Q = Ideal.span {(p : ℤ)} →
        IsArithFrobAt ℤ σ Q}.Infinite := by
  refine (Nat.infinite_setOf_prime_and_eq_mod (a := (cycloUnit (n := n) L σ : ZMod n))
    (cycloUnit (n := n) L σ).isUnit).mono ?_
  rintro p ⟨hp, hpa⟩
  have hpn : ¬ p ∣ n := not_dvd_of_isUnit_natCast hp.one_lt (hpa ▸ (cycloUnit (n := n) L σ).isUnit)
  obtain ⟨Q₀, hQ₀prime, hQ₀p, -⟩ := exists_isPrime_under_eq_span L p hp
  exact ⟨hp, ⟨Q₀, hQ₀prime, hQ₀p⟩, fun Q hQprime hQp =>
    (isArithFrobAt_iff L σ hp hpn Q hQprime hQp).mpr hpa⟩

/-- **Chebotarev density theorem** (qualitative form, cyclotomic case).

For the cyclotomic extension `ℚ(ζₙ)/ℚ` and any element `σ` of its Galois group, there are
infinitely many rational primes `p` admitting a prime `Q` of the ring of integers lying over
`p` whose Frobenius element is exactly `σ`; i.e. `σ x ≡ x ^ p (mod Q)` for all algebraic
integers `x`. Since the Galois group here is abelian, the Frobenius conjugacy class of such a
prime is the singleton `{σ}`, so every Frobenius conjugacy class is realized by infinitely
many primes. -/
theorem chebotarev (n : ℕ) [NeZero n]
    (σ : CyclotomicField n ℚ ≃ₐ[ℚ] CyclotomicField n ℚ) :
    {p : ℕ | p.Prime ∧ ∃ Q : Ideal (𝓞 (CyclotomicField n ℚ)), Q.IsPrime ∧
      Ideal.under ℤ Q = Ideal.span {(p : ℤ)} ∧ IsArithFrobAt ℤ σ Q}.Infinite := by
  refine (chebotarev_cyclotomic n (CyclotomicField n ℚ) σ).mono ?_
  rintro p ⟨hp, ⟨Q, hQprime, hQp⟩, hall⟩
  exact ⟨hp, Q, hQprime, hQp, hall Q hQprime hQp⟩

end Math2

