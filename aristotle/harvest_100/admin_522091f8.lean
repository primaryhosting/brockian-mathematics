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

namespace Math2

open ArithmeticFunction Complex Filter Topology

/-! ### The analytic input: Λ-weighted density of a residue class -/

/-- The terms of the `L`-series of the von Mangoldt function restricted to a residue class,
evaluated at a real point, are real. -/
theorem lseriesTerm_residueClass_ofReal (q : ℕ) (a : ZMod q) (s : ℝ) (n : ℕ) :
    LSeries.term (fun n => (vonMangoldt.residueClass a n : ℂ)) (s : ℂ) n
      = ((vonMangoldt.residueClass a n / (n : ℝ) ^ s : ℝ) : ℂ) := by
  rw [LSeries.term_def]
  rcases eq_or_ne n 0 with rfl | hn
  · simp
  · rw [if_neg hn]
    push_cast
    rw [← Complex.ofReal_natCast, ← Complex.ofReal_cpow (Nat.cast_nonneg n)]

/-- The real Dirichlet series of the von Mangoldt function restricted to a residue class
converges for `s > 1`. -/
theorem summable_residueClass_rpow (q : ℕ) (a : ZMod q) {s : ℝ} (hs : 1 < s) :
    Summable (fun n : ℕ => vonMangoldt.residueClass a n / (n : ℝ) ^ s) := by
  rw [← Complex.summable_ofReal]
  have h : LSeriesSummable (fun n => (vonMangoldt.residueClass a n : ℂ)) (s : ℂ) := by
    refine LSeriesSummable_of_abscissaOfAbsConv_lt_re ?_
    refine lt_of_le_of_lt (vonMangoldt.abscissaOfAbsConv_residueClass_le_one a) ?_
    simpa using (by exact_mod_cast hs : (1 : EReal) < ((s : ℝ) : EReal))
  exact h.congr fun n => lseriesTerm_residueClass_ofReal q a s n

/-- At a real point, the `L`-series of the von Mangoldt function restricted to a residue class
is the coercion of the corresponding real series. -/
theorem lseries_residueClass_ofReal (q : ℕ) (a : ZMod q) (s : ℝ) :
    LSeries (fun n => (vonMangoldt.residueClass a n : ℂ)) (s : ℂ)
      = ((∑' n : ℕ, vonMangoldt.residueClass a n / (n : ℝ) ^ s : ℝ) : ℂ) := by
  rw [LSeries, Complex.ofReal_tsum]
  exact tsum_congr fun n => lseriesTerm_residueClass_ofReal q a s n

/-- For `s > 1` the real Dirichlet series of the von Mangoldt function restricted to an
invertible residue class is a continuous function plus the principal part `(φ q)⁻¹ / (s - 1)`. -/
theorem tsum_residueClass_rpow_eq (q : ℕ) [NeZero q] {a : ZMod q} (ha : IsUnit a) (s : ℝ)
    (hs : 1 < s) :
    (∑' n : ℕ, vonMangoldt.residueClass a n / (n : ℝ) ^ s)
      = (vonMangoldt.LFunctionResidueClassAux a (s : ℂ)).re + (q.totient : ℝ)⁻¹ / (s - 1) := by
  have h := vonMangoldt.eqOn_LFunctionResidueClassAux ha
    (show (s : ℂ) ∈ {s : ℂ | 1 < s.re} by simpa using hs)
  simp only [lseries_residueClass_ofReal] at h
  have h2 : ((((∑' n : ℕ, vonMangoldt.residueClass a n / (n : ℝ) ^ s : ℝ)) : ℂ)
      - ((q.totient : ℂ))⁻¹ / ((s : ℂ) - 1)).re
      = (∑' n : ℕ, vonMangoldt.residueClass a n / (n : ℝ) ^ s) - (q.totient : ℝ)⁻¹ / (s - 1) := by
    rw [show ((q.totient : ℂ))⁻¹ / ((s : ℂ) - 1) = (((q.totient : ℝ)⁻¹ / (s - 1) : ℝ) : ℂ) by
      push_cast; ring, ← Complex.ofReal_sub, Complex.ofReal_re]
  rw [h, h2]; ring

/-- The auxiliary function is continuous at `s = 1` along the reals from the right. -/
theorem tendsto_aux_re (q : ℕ) [NeZero q] (a : ZMod q) :
    Tendsto (fun s : ℝ => (vonMangoldt.LFunctionResidueClassAux a (s : ℂ)).re) (𝓝[>] (1 : ℝ))
      (𝓝 ((vonMangoldt.LFunctionResidueClassAux a 1).re)) := by
  have hc : ContinuousWithinAt (vonMangoldt.LFunctionResidueClassAux a) {s : ℂ | 1 ≤ s.re} 1 :=
    vonMangoldt.continuousOn_LFunctionResidueClassAux a 1 (by simp)
  have h1 : Tendsto (fun s : ℝ => (s : ℂ)) (𝓝[>] (1 : ℝ)) (𝓝[{s : ℂ | 1 ≤ s.re}] 1) := by
    refine tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _ ?_ ?_
    · simpa using (Complex.continuous_ofReal.tendsto (1 : ℝ)).mono_left nhdsWithin_le_nhds
    · filter_upwards [self_mem_nhdsWithin] with s hs
      simpa using le_of_lt hs
  exact Complex.continuous_re.continuousAt.tendsto.comp (hc.tendsto.comp h1)

theorem tendsto_sub_one_nhdsGT : Tendsto (fun s : ℝ => s - 1) (𝓝[>] (1 : ℝ)) (𝓝 0) := by
  have h : Tendsto (fun s : ℝ => s - 1) (𝓝 (1 : ℝ)) (𝓝 ((1 : ℝ) - 1)) :=
    (continuous_id.tendsto (1 : ℝ)).sub_const 1
  simpa using h.mono_left nhdsWithin_le_nhds

/-- **Dirichlet density of a residue class** (von Mangoldt weighted form). -/
theorem tendsto_residueClass_density (q : ℕ) [NeZero q] {a : ZMod q} (ha : IsUnit a) :
    Tendsto (fun s : ℝ => (s - 1) * ∑' n : ℕ, vonMangoldt.residueClass a n / (n : ℝ) ^ s)
      (𝓝[>] (1 : ℝ)) (𝓝 ((q.totient : ℝ)⁻¹)) := by
  have h0 : Tendsto (fun s : ℝ => (s - 1) *
      (vonMangoldt.LFunctionResidueClassAux a (s : ℂ)).re + (q.totient : ℝ)⁻¹)
      (𝓝[>] (1 : ℝ)) (𝓝 ((q.totient : ℝ)⁻¹)) := by
    have h1 : Tendsto (fun s : ℝ => s - 1) (𝓝[>] (1 : ℝ)) (𝓝 0) :=
      tendsto_sub_one_nhdsGT
    simpa using ((h1.mul (tendsto_aux_re q a)).add_const ((q.totient : ℝ)⁻¹))
  refine h0.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with s hs
  have hs' : (1 : ℝ) < s := hs
  have hne : s - 1 ≠ 0 := by linarith
  have hc : (s - 1) * ((q.totient : ℝ)⁻¹ / (s - 1)) = (q.totient : ℝ)⁻¹ := by
    field_simp
  rw [tsum_residueClass_rpow_eq q ha s hs', mul_add, hc]

/-! ### Restricting to primes -/

/-- For `s ≥ 1`, the terms over non-primes are dominated by the corresponding terms at `s = 1`. -/
theorem nonprime_term_le (q : ℕ) (a : ZMod q) {s : ℝ} (hs : 1 ≤ s) (n : ℕ) :
    (if n.Prime then 0 else vonMangoldt.residueClass a n) / (n : ℝ) ^ s
      ≤ (if n.Prime then 0 else vonMangoldt.residueClass a n) / (n : ℝ) := by
  have hnum : 0 ≤ (if n.Prime then 0 else vonMangoldt.residueClass a n) := by
    split_ifs
    · exact le_refl 0
    · exact vonMangoldt.residueClass_nonneg a _
  rcases Nat.lt_or_ge n 2 with hn | hn
  · interval_cases n
    · simp
    · norm_num [vonMangoldt.residueClass]
  · have h2 : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast Nat.one_le_of_lt hn
    have hle : (n : ℝ) ≤ (n : ℝ) ^ s := by
      calc (n : ℝ) = (n : ℝ) ^ (1 : ℝ) := (Real.rpow_one _).symm
        _ ≤ _ := Real.rpow_le_rpow_of_exponent_le h2 hs
    exact div_le_div_of_nonneg_left hnum (by linarith) hle

theorem nonprime_term_nonneg (q : ℕ) (a : ZMod q) (s : ℝ) (n : ℕ) :
    0 ≤ (if n.Prime then 0 else vonMangoldt.residueClass a n) / (n : ℝ) ^ s := by
  have hnum : 0 ≤ (if n.Prime then 0 else vonMangoldt.residueClass a n) := by
    split_ifs
    · exact le_refl 0
    · exact vonMangoldt.residueClass_nonneg a _
  positivity

theorem prime_term_nonneg (q : ℕ) (a : ZMod q) (s : ℝ) (n : ℕ) :
    0 ≤ (if n.Prime then vonMangoldt.residueClass a n else 0) / (n : ℝ) ^ s := by
  have hnum : 0 ≤ (if n.Prime then vonMangoldt.residueClass a n else 0) := by
    split_ifs
    · exact vonMangoldt.residueClass_nonneg a _
    · exact le_refl 0
  positivity

theorem summable_nonprime_rpow (q : ℕ) (a : ZMod q) {s : ℝ} (hs : 1 ≤ s) :
    Summable (fun n : ℕ => (if n.Prime then 0 else vonMangoldt.residueClass a n) / (n : ℝ) ^ s) :=
  Summable.of_nonneg_of_le (nonprime_term_nonneg q a s) (nonprime_term_le q a hs)
    (vonMangoldt.summable_residueClass_non_primes_div a)

theorem summable_prime_rpow (q : ℕ) (a : ZMod q) {s : ℝ} (hs : 1 < s) :
    Summable (fun n : ℕ =>
      (if n.Prime then vonMangoldt.residueClass a n else 0) / (n : ℝ) ^ s) := by
  refine Summable.of_nonneg_of_le (prime_term_nonneg q a s) (fun n => ?_)
    (summable_residueClass_rpow q a hs)
  have h : (if n.Prime then vonMangoldt.residueClass a n else 0)
      ≤ vonMangoldt.residueClass a n := by
    split_ifs
    · exact le_rfl
    · exact vonMangoldt.residueClass_nonneg a _
  gcongr

/-- The non-prime part contributes nothing to the density. -/
theorem tendsto_nonprime_part (q : ℕ) (a : ZMod q) :
    Tendsto (fun s : ℝ => (s - 1) *
        ∑' n : ℕ, (if n.Prime then 0 else vonMangoldt.residueClass a n) / (n : ℝ) ^ s)
      (𝓝[>] (1 : ℝ)) (𝓝 0) := by
  set C : ℝ := ∑' n : ℕ, (if n.Prime then 0 else vonMangoldt.residueClass a n) / (n : ℝ)
  have h1 : Tendsto (fun s : ℝ => (s - 1) * C) (𝓝[>] (1 : ℝ)) (𝓝 0) := by
    simpa using tendsto_sub_one_nhdsGT.mul_const C
  refine squeeze_zero' (eventually_nhdsWithin_of_forall ?_) (eventually_nhdsWithin_of_forall ?_) h1
  · intro s hs
    have hs' : (1 : ℝ) < s := hs
    have hnn : 0 ≤ ∑' n : ℕ, (if n.Prime then 0 else vonMangoldt.residueClass a n) / (n : ℝ) ^ s :=
      tsum_nonneg fun n => nonprime_term_nonneg q a s n
    nlinarith [hnn]
  · intro s hs
    have hs' : (1 : ℝ) < s := hs
    have hle : ∑' n : ℕ, (if n.Prime then 0 else vonMangoldt.residueClass a n) / (n : ℝ) ^ s ≤ C :=
      Summable.tsum_le_tsum (nonprime_term_le q a hs'.le) (summable_nonprime_rpow q a hs'.le)
        (vonMangoldt.summable_residueClass_non_primes_div a)
    nlinarith [hle]

/-- **Dirichlet density of the primes in a residue class** (von Mangoldt weighted form). -/
theorem tendsto_primes_density (q : ℕ) [NeZero q] {a : ZMod q} (ha : IsUnit a) :
    Tendsto (fun s : ℝ => (s - 1) *
        ∑' n : ℕ, (if n.Prime then vonMangoldt.residueClass a n else 0) / (n : ℝ) ^ s)
      (𝓝[>] (1 : ℝ)) (𝓝 ((q.totient : ℝ)⁻¹)) := by
  have hsub := (tendsto_residueClass_density q ha).sub (tendsto_nonprime_part q a)
  simp only [sub_zero] at hsub
  refine hsub.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with s hs
  have hs' : (1 : ℝ) < s := hs
  have hsplit : ∑' n : ℕ, vonMangoldt.residueClass a n / (n : ℝ) ^ s
      = (∑' n : ℕ, (if n.Prime then vonMangoldt.residueClass a n else 0) / (n : ℝ) ^ s)
        + ∑' n : ℕ, (if n.Prime then 0 else vonMangoldt.residueClass a n) / (n : ℝ) ^ s := by
    rw [← Summable.tsum_add (summable_prime_rpow q a hs') (summable_nonprime_rpow q a hs'.le)]
    refine tsum_congr fun n => ?_
    by_cases hn : n.Prime <;> simp [hn]
  rw [hsplit]
  ring

/-! ### The Galois side: Frobenius elements of cyclotomic fields -/

/-- The `q`-th cyclotomic polynomial is irreducible over `ℚ`. -/
theorem irreducible_cyclotomic_rat (q : ℕ) [NeZero q] : Irreducible (Polynomial.cyclotomic q ℚ) :=
  Polynomial.cyclotomic.irreducible_rat (Nat.pos_of_neZero q)

/-- Powers of an element of exponent dividing `q` only depend on the exponent mod `q`. -/
theorem pow_mod_of_pow_eq_one {M : Type*} [Monoid M] {q : ℕ} {x : M}
    (hx : x ^ q = 1) (m : ℕ) : x ^ m = x ^ (m % q) := by
  conv_lhs => rw [← Nat.div_add_mod m q]
  rw [pow_add, pow_mul, hx, one_pow, one_mul]

/-- `σ` is a Frobenius element at `p` for the `q`-th cyclotomic extension of `ℚ` if it acts
on the `q`-th roots of unity as the `p`-th power map. -/
def IsFrobeniusAt (q p : ℕ) (σ : CyclotomicField q ℚ ≃ₐ[ℚ] CyclotomicField q ℚ) : Prop :=
  ∀ x : CyclotomicField q ℚ, x ^ q = 1 → σ x = x ^ p

/-- Each element of the Galois group is the Frobenius exactly at the natural numbers in a
fixed invertible residue class mod `q`. -/
theorem exists_residue_isFrobeniusAt (q : ℕ) [NeZero q]
    (σ : CyclotomicField q ℚ ≃ₐ[ℚ] CyclotomicField q ℚ) :
    ∃ a : ZMod q, IsUnit a ∧ ∀ n : ℕ, IsFrobeniusAt q n σ ↔ (n : ZMod q) = a := by
  have hq : 0 < q := Nat.pos_of_neZero q
  set L := CyclotomicField q ℚ
  set z := IsCyclotomicExtension.zeta q ℚ L with hzdef
  have hz : IsPrimitiveRoot z q := IsCyclotomicExtension.zeta_spec q ℚ L
  set u : (ZMod q)ˣ := hz.autToPow ℚ σ with hu
  have hspec : z ^ ((u : ZMod q)).val = σ z := hz.autToPow_spec ℚ σ
  have hzq : z ^ q = 1 := hz.pow_eq_one
  refine ⟨(u : ZMod q), u.isUnit, fun n => ?_⟩
  constructor
  · intro hf
    have h1 : z ^ ((u : ZMod q)).val = z ^ n := hspec.trans (hf z hzq)
    rw [pow_mod_of_pow_eq_one hzq ((u : ZMod q)).val, pow_mod_of_pow_eq_one hzq n] at h1
    have h2 := hz.pow_inj (Nat.mod_lt _ hq) (Nat.mod_lt _ hq) h1
    have h3 : n ≡ ((u : ZMod q)).val [MOD q] := h2.symm
    rw [← ZMod.natCast_eq_natCast_iff] at h3
    rw [h3, ZMod.natCast_zmod_val]
  · intro hn x hx
    obtain ⟨i, hi, rfl⟩ := hz.eq_pow_of_pow_eq_one hx
    have hnu : ((u : ZMod q)).val ≡ n [MOD q] := by
      have h : ((n : ZMod q)) = ((((u : ZMod q)).val : ℕ) : ZMod q) := by
        rw [hn, ZMod.natCast_zmod_val]
      exact (ZMod.natCast_eq_natCast_iff _ _ _ |>.mp h).symm
    have hmod : ((u : ZMod q)).val * i % q = i * n % q := by
      calc ((u : ZMod q)).val * i % q = n * i % q := hnu.mul_right i
        _ = i * n % q := by rw [mul_comm]
    rw [map_pow, ← hspec, ← pow_mul, ← pow_mul,
      pow_mod_of_pow_eq_one hzq (((u : ZMod q)).val * i), pow_mod_of_pow_eq_one hzq (i * n), hmod]

/-- The Galois group of a cyclotomic extension is abelian, so conjugacy classes are singletons. -/
theorem card_conjClass (q : ℕ) [NeZero q]
    (σ : CyclotomicField q ℚ ≃ₐ[ℚ] CyclotomicField q ℚ) :
    Nat.card {τ : CyclotomicField q ℚ ≃ₐ[ℚ] CyclotomicField q ℚ | IsConj σ τ} = 1 := by
  have hcomm : ∀ σ τ : CyclotomicField q ℚ ≃ₐ[ℚ] CyclotomicField q ℚ, σ * τ = τ * σ := by
    intro σ τ
    have e := IsCyclotomicExtension.autEquivPow (n := q) (K := ℚ) (CyclotomicField q ℚ)
      (irreducible_cyclotomic_rat q)
    exact e.injective (by rw [map_mul, map_mul, mul_comm])
  have hset : {τ : CyclotomicField q ℚ ≃ₐ[ℚ] CyclotomicField q ℚ | IsConj σ τ} = {σ} := by
    ext τ
    simp only [Set.mem_setOf_eq, Set.mem_singleton_iff]
    constructor
    · rintro ⟨c, hc⟩
      have h2 : (c : CyclotomicField q ℚ ≃ₐ[ℚ] CyclotomicField q ℚ) * σ = τ * c := hc.eq
      rw [hcomm (c : CyclotomicField q ℚ ≃ₐ[ℚ] CyclotomicField q ℚ) σ] at h2
      exact (mul_right_cancel h2).symm
    · rintro rfl
      exact IsConj.refl _
  rw [hset]
  simp

theorem card_gal (q : ℕ) [NeZero q] :
    Nat.card (CyclotomicField q ℚ ≃ₐ[ℚ] CyclotomicField q ℚ) = q.totient := by
  have e := IsCyclotomicExtension.autEquivPow (n := q) (K := ℚ) (CyclotomicField q ℚ)
    (irreducible_cyclotomic_rat q)
  rw [Nat.card_congr e.toEquiv, Nat.card_eq_fintype_card, ZMod.card_units_eq_totient]

/-! ### Chebotarev -/

/-- **Chebotarev density theorem** for the cyclotomic extension `ℚ(ζ_q)/ℚ`:
for every element `σ` of the Galois group `G`, the set of primes whose Frobenius is `σ`
(i.e. the primes `p` at which `σ` acts on the `q`-th roots of unity as `x ↦ x ^ p`) has
Dirichlet density equal to the relative size `|C| / |G|` of the conjugacy class `C` of `σ`.

The density is taken in the von Mangoldt weighted analytic sense: writing `S` for the set of
primes in question, `(s - 1) * ∑' p ∈ S, Λ p / p ^ s → |C| / |G|` as `s → 1⁺` along the reals.
Ramified primes (those dividing `q`) are automatically excluded, since for them no `σ`
satisfies the Frobenius condition. -/
theorem chebotarev (q : ℕ) [NeZero q]
    (σ : CyclotomicField q ℚ ≃ₐ[ℚ] CyclotomicField q ℚ) :
    Tendsto (fun s : ℝ => (s - 1) * ∑' n : ℕ,
        {p : ℕ | p.Prime ∧ IsFrobeniusAt q p σ}.indicator
          (fun n : ℕ => vonMangoldt n / (n : ℝ) ^ s) n)
      (𝓝[>] (1 : ℝ))
      (𝓝 ((Nat.card {τ : CyclotomicField q ℚ ≃ₐ[ℚ] CyclotomicField q ℚ | IsConj σ τ} : ℝ)
        / (Nat.card (CyclotomicField q ℚ ≃ₐ[ℚ] CyclotomicField q ℚ) : ℝ))) := by
  obtain ⟨a, ha, hfrob⟩ := exists_residue_isFrobeniusAt q σ
  rw [card_conjClass q σ, card_gal q]
  have hlim := tendsto_primes_density q ha
  simp only [Nat.cast_one, one_div]
  refine hlim.congr fun s => ?_
  congr 1
  refine tsum_congr fun n => ?_
  by_cases hn : n.Prime
  · by_cases hna : (n : ZMod q) = a
    · rw [Set.indicator_of_mem (by exact ⟨hn, (hfrob n).mpr hna⟩)]
      simp [hn, vonMangoldt.residueClass, hna]
    · rw [Set.indicator_of_notMem (by
        simp only [Set.mem_setOf_eq, not_and]
        intro _ hf
        exact hna ((hfrob n).mp hf))]
      simp [hn, vonMangoldt.residueClass, hna]
  · rw [Set.indicator_of_notMem (by
      simp only [Set.mem_setOf_eq, not_and]
      intro h
      exact absurd h hn)]
    simp [hn]

/-- A qualitative consequence of the above: for every element `σ` of the Galois group of
`ℚ(ζ_q)/ℚ` there are infinitely many primes whose Frobenius is `σ`. -/
theorem infinite_setOf_prime_isFrobeniusAt (q : ℕ) [NeZero q]
    (σ : CyclotomicField q ℚ ≃ₐ[ℚ] CyclotomicField q ℚ) :
    {p : ℕ | p.Prime ∧ IsFrobeniusAt q p σ}.Infinite := by
  obtain ⟨a, ha, hfrob⟩ := exists_residue_isFrobeniusAt q σ
  have hset : {p : ℕ | p.Prime ∧ IsFrobeniusAt q p σ} = {p : ℕ | p.Prime ∧ (p : ZMod q) = a} := by
    ext p
    exact and_congr_right fun _ => hfrob p
  rw [hset]
  exact Nat.infinite_setOf_prime_and_eq_mod ha

end Math2

