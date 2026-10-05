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

namespace Math2

/-- `IsFrobeniusAt R σ p` says that the ring automorphism `σ` of `R` is a Frobenius
automorphism at the rational prime `p`: there is a maximal ideal `P` of `R` lying above `p`
such that `σ x ≡ x ^ p (mod P)` for all `x : R`.

For `R` the ring of integers of a Galois number field this is the usual notion of (an element
of) the Frobenius conjugacy class at `p`. -/
def IsFrobeniusAt (R : Type*) [CommRing R] (σ : R ≃+* R) (p : ℕ) : Prop :=
  ∃ P : Ideal R, P.IsMaximal ∧ (p : R) ∈ P ∧ ∀ x : R, σ x - x ^ p ∈ P

section

variable {n : ℕ} {R : Type*} [CommRing R] [IsDomain R] [CharZero R] {ζ : R}

omit [IsDomain R] [CharZero R] in
/-- A root of unity of order `n` has `ζ ^ i = ζ ^ j` whenever `i ≡ j [MOD n]`. -/
theorem pow_eq_pow_of_modEq (hζ : IsPrimitiveRoot ζ n) {i j : ℕ} (h : i ≡ j [MOD n]) :
    ζ ^ i = ζ ^ j := by
  have key : ∀ k : ℕ, ζ ^ k = ζ ^ (k % n) := by
    intro k
    conv_lhs => rw [← Nat.div_add_mod k n]
    rw [pow_add, pow_mul, hζ.pow_eq_one, one_pow, one_mul]
  rw [key i, key j, h]

omit [CharZero R] in
/-- In `ℤ[ζ]` with `ζ` a primitive `n`-th root of unity, every ring automorphism sends `ζ`
to a power `ζ ^ a` with `a` coprime to `n`. -/
theorem exists_coprime_pow_eq_aut (hn : 0 < n) (hζ : IsPrimitiveRoot ζ n) (σ : R ≃+* R) :
    ∃ a : ℕ, Nat.Coprime a n ∧ σ ζ = ζ ^ a := by
  haveI : NeZero n := ⟨hn.ne'⟩
  have hprim : IsPrimitiveRoot (σ ζ) n := hζ.map_of_injective σ.injective
  obtain ⟨a, -, ha⟩ := hζ.eq_pow_of_pow_eq_one hprim.pow_eq_one
  exact ⟨a, ((hζ.pow_iff_coprime hn a).1 (ha ▸ hprim)), ha.symm⟩

omit [IsDomain R] [CharZero R] in
/-- `ℤ[ζ]` is integral over `ℤ`. -/
theorem isIntegral_of_adjoin_eq_top (hn : 0 < n) (hζ : IsPrimitiveRoot ζ n)
    (hgen : Algebra.adjoin ℤ ({ζ} : Set R) = ⊤) : Algebra.IsIntegral ℤ R := by
  constructor
  intro x
  have hx : x ∈ Algebra.adjoin ℤ ({ζ} : Set R) := by rw [hgen]; trivial
  have hle : Algebra.adjoin ℤ ({ζ} : Set R) ≤ integralClosure ℤ R :=
    Algebra.adjoin_le (by simpa using hζ.isIntegral hn)
  exact hle hx

omit [IsDomain R] in
/-- Any prime number is contained in some maximal ideal of a ring that is integral over `ℤ`
(and of characteristic zero). -/
theorem exists_maximal_mem_of_prime [Algebra.IsIntegral ℤ R] {p : ℕ} (hp : p.Prime) :
    ∃ P : Ideal R, P.IsMaximal ∧ (p : R) ∈ P := by
  have hpZ : Prime (p : ℤ) := Nat.prime_iff_prime_int.1 hp
  haveI : (Ideal.span ({(p : ℤ)} : Set ℤ)).IsMaximal :=
    PrincipalIdealRing.isMaximal_of_irreducible hpZ.irreducible
  have hker : RingHom.ker (algebraMap ℤ R) ≤ Ideal.span ({(p : ℤ)} : Set ℤ) := by
    have hinj : Function.Injective (algebraMap ℤ R) := (algebraMap ℤ R).injective_int
    rw [(RingHom.injective_iff_ker_eq_bot _).1 hinj]
    exact bot_le
  obtain ⟨Q, hQmax, hQ⟩ :=
    Ideal.exists_ideal_over_maximal_of_isIntegral (S := R) (Ideal.span ({(p : ℤ)} : Set ℤ)) hker
  refine ⟨Q, hQmax, ?_⟩
  have : (p : ℤ) ∈ Q.comap (algebraMap ℤ R) := by
    rw [hQ]; exact Ideal.subset_span rfl
  simpa using this

omit [IsDomain R] [CharZero R] in
/-- If `σ ζ = ζ ^ p` and `P` is a maximal ideal containing the prime `p`, then `σ` reduces to
the `p`-power Frobenius modulo `P`. -/
theorem frobenius_congr (hgen : Algebra.adjoin ℤ ({ζ} : Set R) = ⊤) (σ : R ≃+* R) {p : ℕ}
    (hp : p.Prime) {P : Ideal R} (hPmax : P.IsMaximal) (hpP : (p : R) ∈ P)
    (hσζ : σ ζ = ζ ^ p) (x : R) : σ x - x ^ p ∈ P := by
  haveI : P.IsMaximal := hPmax
  haveI : Fact p.Prime := ⟨hp⟩
  haveI hchar : CharP (R ⧸ P) p := by
    have hp0 : ((p : ℕ) : R ⧸ P) = 0 := by
      have : (Ideal.Quotient.mk P) (p : R) = 0 := Ideal.Quotient.eq_zero_iff_mem.2 hpP
      simpa using this
    have hdvd : ringChar (R ⧸ P) ∣ p := ringChar.dvd hp0
    haveI inst : CharP (R ⧸ P) (ringChar (R ⧸ P)) := ringChar.charP _
    rcases (hp.eq_one_or_self_of_dvd _ hdvd) with h1 | h1
    · exfalso
      have h10 : (1 : R ⧸ P) = 0 := by
        simpa using (CharP.cast_eq_zero_iff (R ⧸ P) (ringChar (R ⧸ P)) 1).2 (by rw [h1])
      exact one_ne_zero h10
    · exact h1 ▸ inst
  set f : R →ₐ[ℤ] R ⧸ P :=
    ((Ideal.Quotient.mk P).comp (σ : R →+* R)).toIntAlgHom with hf
  set g : R →ₐ[ℤ] R ⧸ P :=
    ((frobenius (R ⧸ P) p).comp (Ideal.Quotient.mk P)).toIntAlgHom with hg
  have hfg : f = g := by
    refine AlgHom.ext_of_adjoin_eq_top hgen ?_
    rintro y (rfl : y = ζ)
    simp [hf, hg, frobenius_def, hσζ]
  have hx : f x = g x := by rw [hfg]
  have : (Ideal.Quotient.mk P) (σ x) = (Ideal.Quotient.mk P) (x ^ p) := by
    simpa [hf, hg, frobenius_def] using hx
  have := sub_eq_zero.2 this
  rw [← map_sub] at this
  exact Ideal.Quotient.eq_zero_iff_mem.1 this

/-- **Chebotarev density theorem** (qualitative form, for cyclotomic extensions).

Let `R = ℤ[ζ]` be the ring generated by a primitive `n`-th root of unity `ζ` in a
characteristic-zero domain, i.e. the ring of integers of the cyclotomic field `ℚ(ζ_n)`, and let
`σ` be any automorphism of `R`, i.e. any element of the Galois group `Gal(ℚ(ζ_n)/ℚ)`.  Then
there are infinitely many rational primes `p` whose Frobenius conjugacy class (a single element,
the extension being abelian) is `σ`; that is, for infinitely many primes `p` there is a maximal
ideal `P` above `p` with `σ x ≡ x ^ p (mod P)` for all `x`. -/
theorem chebotarev (hn : 0 < n) (hζ : IsPrimitiveRoot ζ n)
    (hgen : Algebra.adjoin ℤ ({ζ} : Set R) = ⊤) (σ : R ≃+* R) :
    {p : ℕ | p.Prime ∧ IsFrobeniusAt R σ p}.Infinite := by
  obtain ⟨a, hacop, hσζ⟩ := exists_coprime_pow_eq_aut hn hζ σ
  haveI : Algebra.IsIntegral ℤ R := isIntegral_of_adjoin_eq_top hn hζ hgen
  have hsub : {p : ℕ | p.Prime ∧ p ≡ a [MOD n]} ⊆ {p : ℕ | p.Prime ∧ IsFrobeniusAt R σ p} := by
    rintro p ⟨hp, hpa⟩
    refine ⟨hp, ?_⟩
    obtain ⟨P, hPmax, hpP⟩ := exists_maximal_mem_of_prime (R := R) hp
    refine ⟨P, hPmax, hpP, ?_⟩
    have hζp : σ ζ = ζ ^ p := by
      rw [hσζ]
      exact pow_eq_pow_of_modEq hζ hpa.symm
    exact frobenius_congr hgen σ hp hPmax hpP hζp
  exact (Nat.infinite_setOf_prime_and_modEq hn.ne' hacop).mono hsub

end

/-- Concrete instance of `Math2.chebotarev`: for a primitive `n`-th root of unity `ζ ∈ ℂ` and
`A = ℤ[ζ]` the ring of integers of the cyclotomic field `ℚ(ζ)`, every automorphism of `A` (i.e.
every element of the Galois group of `ℚ(ζ)/ℚ`) is the Frobenius at infinitely many primes. -/
theorem chebotarev_cyclotomic_complex {n : ℕ} (hn : 0 < n) {ζ : ℂ} (hζ : IsPrimitiveRoot ζ n)
    (σ : Algebra.adjoin ℤ ({ζ} : Set ℂ) ≃+* Algebra.adjoin ℤ ({ζ} : Set ℂ)) :
    {p : ℕ | p.Prime ∧ IsFrobeniusAt (Algebra.adjoin ℤ ({ζ} : Set ℂ)) σ p}.Infinite := by
  have hmem : ζ ∈ Algebra.adjoin ℤ ({ζ} : Set ℂ) := Algebra.subset_adjoin rfl
  have hζ' : IsPrimitiveRoot (⟨ζ, hmem⟩ : Algebra.adjoin ℤ ({ζ} : Set ℂ)) n :=
    hζ.of_map_of_injective (f := (Algebra.adjoin ℤ ({ζ} : Set ℂ)).subtype) Subtype.val_injective
  have hgen : Algebra.adjoin ℤ
      ({(⟨ζ, hmem⟩ : Algebra.adjoin ℤ ({ζ} : Set ℂ))} : Set (Algebra.adjoin ℤ ({ζ} : Set ℂ))) = ⊤ := by
    have h := Algebra.adjoin_adjoin_coe_preimage (R := ℤ) (s := ({ζ} : Set ℂ))
    convert h using 2
    ext x
    simp [Subtype.ext_iff]
  exact chebotarev hn hζ' hgen σ

end Math2

