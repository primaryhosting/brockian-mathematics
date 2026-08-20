import Mathlib

/-!
# Chebotarev
Category: Frontier Math
Target: Math2.chebotarev
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

set_option maxHeartbeats 1000000
set_option relaxedAutoImplicit false
set_option autoImplicit false

namespace Math2

open NumberField

section NumberFields

variable (L : Type*) [Field L] [NumberField L]

/-- The group of `ℤ`-algebra automorphisms of the ring of integers of a number field is
finite. -/
lemma finite_aut_ringOfIntegers : Finite (𝓞 L ≃ₐ[ℤ] 𝓞 L) :=
  Finite.of_equiv _ (galRestrict ℤ ℚ L (𝓞 L)).toEquiv

/-- For `L/ℚ` Galois, the subring of `𝓞 L` fixed by all `ℤ`-algebra automorphisms is `ℤ`. -/
lemma isInvariant_ringOfIntegers [IsGalois ℚ L] :
    Algebra.IsInvariant ℤ (𝓞 L) (𝓞 L ≃ₐ[ℤ] 𝓞 L) :=
  Algebra.isInvariant_of_isGalois' ℤ ℚ L _

/-- There is a prime of the ring of integers above any rational prime, and its residue field
is finite. -/
lemma exists_prime_over {p : ℕ} (hp : p.Prime) :
    ∃ Q : Ideal (𝓞 L), Q.IsPrime ∧ Ideal.under ℤ Q = Ideal.span {(p : ℤ)} ∧ Finite (𝓞 L ⧸ Q) := by
  haveI : (Ideal.span {(p : ℤ)}).IsPrime := by
    rw [Ideal.span_singleton_prime (by exact_mod_cast hp.ne_zero)]
    exact Nat.prime_iff_prime_int.mp hp
  obtain ⟨Q, -, hQp, hQu⟩ :=
    Ideal.exists_ideal_over_prime_of_isIntegral (R := ℤ) (S := 𝓞 L) (Ideal.span {(p : ℤ)}) ⊥
      ((Ideal.comap_bot_le_of_injective _ (FaithfulSMul.algebraMap_injective ℤ _)).trans bot_le)
  refine ⟨Q, hQp, hQu, ?_⟩
  have hbot : Q ≠ ⊥ := by
    intro h
    rw [h] at hQu
    have hmem : ((p : ℤ)) ∈ Ideal.span {(p : ℤ)} := Ideal.mem_span_singleton_self _
    rw [← hQu] at hmem
    simp only [Ideal.mem_comap, Ideal.mem_bot] at hmem
    have hinj : Function.Injective (algebraMap ℤ (𝓞 L)) := FaithfulSMul.algebraMap_injective _ _
    have hp0 := hinj (by simpa using hmem : algebraMap ℤ (𝓞 L) p = algebraMap ℤ _ 0)
    exact hp.ne_zero (by exact_mod_cast hp0)
  exact Ideal.finiteQuotientOfFreeOfNeBot Q hbot

end NumberFields

section Cyclotomic

variable (n : ℕ) [NeZero n] (L : Type*) [Field L] [NumberField L]
  [IsCyclotomicExtension {n} ℚ L]

omit [NeZero n] in
include n in
/-- A cyclotomic extension of `ℚ` is Galois. -/
lemma isGalois_cyclotomic : IsGalois ℚ L :=
  IsCyclotomicExtension.isGalois {n} ℚ L

/-- A fixed primitive `n`-th root of unity in the ring of integers of a cyclotomic
field `L = ℚ(ζₙ)`. -/
noncomputable def zetaInt : 𝓞 L :=
  (IsCyclotomicExtension.zeta_spec n ℚ L).toInteger

lemma zetaInt_isPrimitiveRoot : IsPrimitiveRoot (zetaInt n L) n :=
  (IsCyclotomicExtension.zeta_spec n ℚ L).toInteger_isPrimitiveRoot

lemma algebraMap_zetaInt :
    algebraMap (𝓞 L) L (zetaInt n L) = IsCyclotomicExtension.zeta n ℚ L := rfl

variable {n L}

/-- Two `ℚ`-automorphisms of `L = ℚ(ζₙ)` agreeing on `ζₙ` are equal. -/
lemma algEquiv_ext_zeta {f g : L ≃ₐ[ℚ] L}
    (h : f (IsCyclotomicExtension.zeta n ℚ L) = g (IsCyclotomicExtension.zeta n ℚ L)) :
    f = g := by
  have hz := IsCyclotomicExtension.zeta_spec n ℚ L
  apply hz.autToPow_injective ℚ
  have h1 := hz.autToPow_spec ℚ f
  have h2 := hz.autToPow_spec ℚ g
  have hv : ((hz.autToPow ℚ f : (ZMod n)ˣ) : ZMod n).val =
      ((hz.autToPow ℚ g : (ZMod n)ˣ) : ZMod n).val :=
    hz.pow_inj (ZMod.val_lt _) (ZMod.val_lt _) (by rw [h1, h2, h])
  ext
  exact ZMod.val_injective _ hv

/-- Two `ℤ`-automorphisms of the ring of integers of `L = ℚ(ζₙ)` agreeing on `ζₙ` are equal. -/
lemma aut_ext_zetaInt {f g : 𝓞 L ≃ₐ[ℤ] 𝓞 L} (h : f (zetaInt n L) = g (zetaInt n L)) : f = g := by
  set e := galRestrict ℤ ℚ L (𝓞 L) with he
  have key : e.symm f = e.symm g := by
    apply algEquiv_ext_zeta (n := n)
    have h1 := algebraMap_galRestrict_apply (A := ℤ) (e.symm f) (zetaInt n L)
    have h2 := algebraMap_galRestrict_apply (A := ℤ) (e.symm g) (zetaInt n L)
    rw [he] at h1 h2
    simp only [MulEquiv.apply_symm_apply, algebraMap_zetaInt] at h1 h2
    rw [← h1, ← h2, h]
  simpa using congrArg e key

/-- Every `ℤ`-automorphism of the ring of integers raises `ζₙ` to a power prime to `n`. -/
lemma exists_unit_pow_zetaInt (f : 𝓞 L ≃ₐ[ℤ] 𝓞 L) :
    ∃ a : (ZMod n)ˣ, f (zetaInt n L) = zetaInt n L ^ ((a : ZMod n).val) :=
  ⟨(zetaInt_isPrimitiveRoot n L).autToPow ℤ f,
    ((zetaInt_isPrimitiveRoot n L).autToPow_spec ℤ f).symm⟩

/-- A Frobenius element at a prime `Q` above `p` (with `p ∤ n`) raises `ζₙ` to the `p`-th
power. -/
lemma isArithFrobAt_apply_zetaInt {p : ℕ} (hpn : ¬ p ∣ n) {Q : Ideal (𝓞 L)}
    (hQ : Ideal.under ℤ Q = Ideal.span {(p : ℤ)}) {f : 𝓞 L ≃ₐ[ℤ] 𝓞 L}
    (hf : IsArithFrobAt ℤ f Q) : f (zetaInt n L) = zetaInt n L ^ p := by
  have hpow : (zetaInt n L) ^ n = 1 := (zetaInt_isPrimitiveRoot n L).pow_eq_one
  have hmem : ((n : ℕ) : 𝓞 L) ∉ Q := by
    intro hmem
    have hn : ((n : ℤ)) ∈ Ideal.under ℤ Q := by
      simpa [Ideal.under, Ideal.mem_comap] using hmem
    rw [hQ, Ideal.mem_span_singleton] at hn
    exact hpn (by exact_mod_cast hn)
  have hfz := hf.apply_of_pow_eq_one hpow hmem
  have hcard : Nat.card (ℤ ⧸ Ideal.under ℤ Q) = p := by
    rw [hQ, Nat.card_congr (Int.quotientSpanNatEquivZMod p).toEquiv, Nat.card_zmod]
  rw [hcard] at hfz
  simpa using hfz

variable (n L)

include n in
/-- **Chebotarev density theorem** (qualitative form, for cyclotomic extensions of `ℚ`).

Let `n ≥ 1`, let `L = ℚ(ζₙ)` be an `n`-th cyclotomic field and let `G = 𝓞L ≃ₐ[ℤ] 𝓞L` be its
Galois group, acting on the ring of integers `𝓞L`.  Then for every `σ ∈ G` there are infinitely
many rational primes `p` whose Frobenius conjugacy class is the conjugacy class of `σ`: there is
a prime `Q` of `𝓞L` above `p` at which `σ` itself is an arithmetic Frobenius element, and at
*every* prime `Q` of `𝓞L` above `p` some conjugate of `σ` is an arithmetic Frobenius element. -/
theorem chebotarev (σ : 𝓞 L ≃ₐ[ℤ] 𝓞 L) :
    {p : ℕ | p.Prime ∧
        (∃ Q : Ideal (𝓞 L), Q.IsPrime ∧
          Ideal.under ℤ Q = Ideal.span {(p : ℤ)} ∧ IsArithFrobAt ℤ σ Q) ∧
        (∀ Q : Ideal (𝓞 L), Q.IsPrime → Ideal.under ℤ Q = Ideal.span {(p : ℤ)} →
          ∃ τ : 𝓞 L ≃ₐ[ℤ] 𝓞 L, IsArithFrobAt ℤ τ Q ∧ IsConj σ τ)}.Infinite := by
  haveI := finite_aut_ringOfIntegers L
  haveI := isGalois_cyclotomic n L
  haveI := isInvariant_ringOfIntegers L
  obtain ⟨a, ha⟩ := exists_unit_pow_zetaInt (n := n) (L := L) σ
  refine (Nat.infinite_setOf_prime_and_eq_mod (q := n) a.isUnit).mono ?_
  rintro p ⟨hp, hpa⟩
  -- `p` is coprime to `n`, hence does not divide `n`
  have hcop : Nat.Coprime p n := by
    rw [← ZMod.isUnit_iff_coprime, hpa]
    exact a.isUnit
  have hpn : ¬ p ∣ n := fun hdvd => by
    have : p ∣ 1 := hcop ▸ Nat.dvd_gcd dvd_rfl hdvd
    exact hp.one_lt.ne' (Nat.dvd_one.mp this)
  obtain ⟨Q, hQp, hQu, hQfin⟩ := exists_prime_over L hp
  haveI := hQp
  haveI := hQfin
  -- a Frobenius element `τ` at `Q` exists, and it sends `ζₙ` to `ζₙ ^ p = σ ζₙ`
  obtain ⟨τ, hτ⟩ := IsArithFrobAt.exists_of_isInvariant ℤ (𝓞 L ≃ₐ[ℤ] 𝓞 L) Q
  have hτz : τ (zetaInt n L) = zetaInt n L ^ p := isArithFrobAt_apply_zetaInt (n := n) hpn hQu hτ
  have hpow : zetaInt n L ^ p = zetaInt n L ^ ((a : ZMod n).val) := by
    have hzn : (zetaInt n L) ^ n = 1 := (zetaInt_isPrimitiveRoot n L).pow_eq_one
    have key : ∀ k : ℕ, zetaInt n L ^ k = zetaInt n L ^ (k % n) := by
      intro k
      conv_lhs => rw [← Nat.div_add_mod k n]
      rw [pow_add, pow_mul, hzn, one_pow, one_mul]
    have hmod : p ≡ (a : ZMod n).val [MOD n] := by
      rw [← ZMod.natCast_eq_natCast_iff, hpa]
      simp
    rw [key p, key ((a : ZMod n).val), hmod]
  have hστ : σ = τ := aut_ext_zetaInt (n := n) (by rw [ha, hτz, hpow])
  subst hστ
  refine ⟨hp, ⟨Q, hQp, hQu, hτ⟩, ?_⟩
  -- every prime above `p` also carries a Frobenius element conjugate to `σ`
  intro Q' hQ'p hQ'u
  haveI := hQ'p
  obtain ⟨g, hg⟩ := Algebra.IsInvariant.exists_smul_of_under_eq ℤ (𝓞 L) (𝓞 L ≃ₐ[ℤ] 𝓞 L) Q Q'
    (by rw [hQu, hQ'u])
  refine ⟨g * σ * g⁻¹, ?_, isConj_iff.mpr ⟨g, rfl⟩⟩
  rw [hg]
  exact hτ.conj g

/-- **Chebotarev density theorem** for the cyclotomic field `CyclotomicField n ℚ`, the
canonical model of `ℚ(ζₙ)`. -/
theorem chebotarev_cyclotomicField (m : ℕ) [NeZero m]
    (σ : 𝓞 (CyclotomicField m ℚ) ≃ₐ[ℤ] 𝓞 (CyclotomicField m ℚ)) :
    {p : ℕ | p.Prime ∧
        (∃ Q : Ideal (𝓞 (CyclotomicField m ℚ)), Q.IsPrime ∧
          Ideal.under ℤ Q = Ideal.span {(p : ℤ)} ∧ IsArithFrobAt ℤ σ Q) ∧
        (∀ Q : Ideal (𝓞 (CyclotomicField m ℚ)), Q.IsPrime →
          Ideal.under ℤ Q = Ideal.span {(p : ℤ)} →
          ∃ τ : 𝓞 (CyclotomicField m ℚ) ≃ₐ[ℤ] 𝓞 (CyclotomicField m ℚ),
            IsArithFrobAt ℤ τ Q ∧ IsConj σ τ)}.Infinite :=
  chebotarev m (CyclotomicField m ℚ) σ

end Cyclotomic

end Math2

