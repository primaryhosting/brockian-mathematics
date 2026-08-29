/-
# Chebotarev
Category: Frontier Math
Target: Math2.chebotarev
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

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

namespace Math2

section Cyclotomic

variable {n : ℕ} [NeZero n] {K : Type*} [Field K] [Algebra ℚ K]
  [IsCyclotomicExtension {n} ℚ K]

/-- An automorphism of a cyclotomic extension acts on *all* primitive `n`-th roots of unity
by the same exponent. -/
theorem exists_uniform_exponent (σ : K ≃ₐ[ℚ] K) :
    ∃ m : ℕ, Nat.Coprime m n ∧ ∀ ζ : K, IsPrimitiveRoot ζ n → σ ζ = ζ ^ m := by
  obtain ⟨ζ₀, hζ₀⟩ : ∃ z : K, IsPrimitiveRoot z n :=
    ⟨_, IsCyclotomicExtension.zeta_spec n ℚ K⟩
  have hσζ : IsPrimitiveRoot (σ ζ₀) n := hζ₀.map_of_injective σ.injective
  obtain ⟨m, -, hm⟩ := hζ₀.eq_pow_of_pow_eq_one hσζ.pow_eq_one
  refine ⟨m, (hζ₀.pow_iff_coprime (NeZero.pos n) m).mp (hm ▸ hσζ), ?_⟩
  intro ζ hζ
  obtain ⟨i, -, hi⟩ := hζ₀.eq_pow_of_pow_eq_one hζ.pow_eq_one
  rw [← hi, map_pow, ← hm, ← pow_mul, ← pow_mul, Nat.mul_comm]

/-- **Chebotarev theorem for Frobenius conjugacy classes**, in the qualitative form, for
cyclotomic extensions of `ℚ`.

If `K = ℚ(ζₙ)` and `C` is a conjugacy class of `Gal(K/ℚ)`, then there are infinitely many
rational primes `p` that are unramified in `K` (equivalently `p ∤ n`) whose Frobenius
automorphism lies in `C`. Here the Frobenius at an unramified prime `p` is characterised by
the property that it raises every primitive `n`-th root of unity to the `p`-th power, and the
conclusion is stated in the strong form "*every* element of `C` is a Frobenius at `p`".

This is the classical prototype of the Chebotarev density theorem: for cyclotomic fields it is
equivalent to Dirichlet's theorem on primes in arithmetic progressions, which supplies the
analytic input. The statement here is the qualitative (infinitude) form rather than the
quantitative statement about Dirichlet density. -/
theorem chebotarev (C : ConjClasses (K ≃ₐ[ℚ] K)) :
    {p : ℕ | p.Prime ∧ ¬ (p ∣ n) ∧
      ∀ σ ∈ C.carrier, ∀ ζ : K, IsPrimitiveRoot ζ n → σ ζ = ζ ^ p}.Infinite := by
  obtain ⟨σ, rfl⟩ := ConjClasses.mk_surjective C
  obtain ⟨m, hmco, hmspec⟩ := exists_uniform_exponent (n := n) σ
  refine Set.Infinite.mono ?_ (Nat.infinite_setOf_prime_and_modEq (NeZero.ne n) hmco)
  rintro p ⟨hp, hpm⟩
  have hpco : Nat.Coprime p n := by
    have h1 : IsUnit ((m : ZMod n)) := (ZMod.isUnit_iff_coprime m n).2 hmco
    have h2 : ((p : ZMod n)) = ((m : ZMod n)) := (ZMod.natCast_eq_natCast_iff _ _ _).2 hpm
    exact (ZMod.isUnit_iff_coprime p n).1 (h2 ▸ h1)
  refine ⟨hp, fun hdvd => ?_, ?_⟩
  · exact hp.coprime_iff_not_dvd.1 hpco hdvd
  · intro τ hτ ζ hζ
    have hconj : IsConj σ τ :=
      ConjClasses.mk_eq_mk_iff_isConj.1 (ConjClasses.mem_carrier_iff_mk_eq.1 hτ).symm
    obtain ⟨c, hc⟩ := isConj_iff.1 hconj
    have hcz : IsPrimitiveRoot (c⁻¹ ζ) n := hζ.map_of_injective (c⁻¹ : K ≃ₐ[ℚ] K).injective
    have key : τ ζ = ζ ^ m := by
      rw [← hc]
      simp only [AlgEquiv.mul_apply]
      rw [hmspec _ hcz, map_pow]
      congr 1
      simp
    have hmod : ∀ k : ℕ, ζ ^ k = ζ ^ (k % n) := by
      intro k
      conv_lhs => rw [← Nat.div_add_mod k n]
      rw [pow_add, pow_mul, hζ.pow_eq_one, one_pow, one_mul]
    have hpow : ζ ^ p = ζ ^ m := by rw [hmod p, hmod m, hpm]
    rw [key, hpow]

end Cyclotomic

/-- The Chebotarev statement instantiated at the concrete cyclotomic field `ℚ(ζₙ)`; this also
witnesses that the hypotheses of `Math2.chebotarev` are satisfiable. -/
theorem chebotarev_cyclotomicField (n : ℕ) [NeZero n]
    (C : ConjClasses (CyclotomicField n ℚ ≃ₐ[ℚ] CyclotomicField n ℚ)) :
    {p : ℕ | p.Prime ∧ ¬ (p ∣ n) ∧
      ∀ σ ∈ C.carrier, ∀ ζ : CyclotomicField n ℚ,
        IsPrimitiveRoot ζ n → σ ζ = ζ ^ p}.Infinite :=
  chebotarev C

end Math2

#print axioms Math2.chebotarev
#print axioms Math2.chebotarev_cyclotomicField

