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

/-- Auxiliary step: an automorphism `σ` of a field containing a primitive `n`-th root of unity
`ζ` sends `ζ` to `ζ ^ m` for some `m` that is invertible modulo `n`. -/
theorem exists_unit_pow_eq_aut {n : ℕ} [NeZero n] {K : Type*} [Field K] [Algebra ℚ K]
    {ζ : K} (hζ : IsPrimitiveRoot ζ n) (σ : K ≃ₐ[ℚ] K) :
    ∃ a : ZMod n, IsUnit a ∧ ζ ^ a.val = σ ζ :=
  ⟨((hζ.autToPow ℚ σ : (ZMod n)ˣ) : ZMod n), Units.isUnit _, hζ.autToPow_spec ℚ σ⟩

/-- Auxiliary step: powers of an `n`-th root of unity only depend on the exponent mod `n`. -/
theorem pow_eq_pow_of_modEq {M : Type*} [Monoid M] {ζ : M} {n i j : ℕ}
    (h1 : ζ ^ n = 1) (h : i ≡ j [MOD n]) : ζ ^ i = ζ ^ j := by
  have key : ∀ k : ℕ, ζ ^ k = ζ ^ (k % n) := by
    intro k
    conv_lhs => rw [← Nat.div_add_mod k n, pow_add, pow_mul, h1, one_pow, one_mul]
  rw [key i, key j, h]

/-- Auxiliary step: if `p` is a prime whose residue class mod `n` is a unit, then `p ∤ n`,
i.e. `p` is unramified in the `n`-th cyclotomic extension. -/
theorem not_dvd_of_isUnit_cast {n p : ℕ} (hp : p.Prime) (h : IsUnit ((p : ZMod n))) :
    ¬ p ∣ n := by
  intro hdvd
  have hcop : Nat.Coprime p n := (ZMod.isUnit_iff_coprime p n).mp h
  have : p ∣ 1 := hcop ▸ Nat.dvd_gcd dvd_rfl hdvd
  exact hp.one_lt.ne' (Nat.dvd_one.mp this)

/-- **Chebotarev density theorem** (qualitative form) for cyclotomic extensions.

Let `K` be a field of characteristic zero containing a primitive `n`-th root of unity `ζ`,
and let `σ` be any element of the Galois group `Gal(K/ℚ)` (whose conjugacy classes are
singletons, since the Galois group of a cyclotomic extension is abelian).

Then there are infinitely many primes `p`, unramified (`p ∤ n`), whose Frobenius element
at `p` — characterized by the congruence `Frob_p (ζ) = ζ ^ p` — is exactly `σ`.

Equivalently: the set of primes whose Frobenius conjugacy class is the class of `σ`
is infinite. The proof reduces the Frobenius condition to a congruence condition
`p ≡ m (mod n)` and then applies Dirichlet's theorem on primes in arithmetic
progressions. -/
theorem chebotarev {n : ℕ} [NeZero n] {K : Type*} [Field K] [Algebra ℚ K]
    {ζ : K} (hζ : IsPrimitiveRoot ζ n) (σ : K ≃ₐ[ℚ] K) :
    {p : ℕ | p.Prime ∧ ¬ p ∣ n ∧ σ ζ = ζ ^ p}.Infinite := by
  obtain ⟨a, ha, hspec⟩ := exists_unit_pow_eq_aut hζ σ
  refine Set.Infinite.mono ?_ (Nat.infinite_setOf_prime_and_eq_mod ha)
  rintro p ⟨hp, hpa⟩
  have hcast : IsUnit ((p : ZMod n)) := hpa ▸ ha
  refine ⟨hp, not_dvd_of_isUnit_cast hp hcast, ?_⟩
  have hmod : p ≡ a.val [MOD n] := by
    have : ((p : ℕ) : ZMod n) = ((a.val : ℕ) : ZMod n) := by
      simp [hpa, ZMod.natCast_val, ZMod.cast_id]
    exact (ZMod.natCast_eq_natCast_iff _ _ _).mp this
  rw [← hspec, pow_eq_pow_of_modEq hζ.pow_eq_one hmod.symm]

/-- Conjugacy-class form of the Chebotarev density theorem for cyclotomic extensions:
for every `σ` in the Galois group there are infinitely many unramified primes `p`
admitting a Frobenius element `f` at `p` (i.e. `f ζ = ζ ^ p`) conjugate to `σ`. -/
theorem chebotarev_isConj {n : ℕ} [NeZero n] {K : Type*} [Field K] [Algebra ℚ K]
    {ζ : K} (hζ : IsPrimitiveRoot ζ n) (σ : K ≃ₐ[ℚ] K) :
    {p : ℕ | p.Prime ∧ ¬ p ∣ n ∧ ∃ f : K ≃ₐ[ℚ] K, f ζ = ζ ^ p ∧ IsConj f σ}.Infinite := by
  refine Set.Infinite.mono ?_ (chebotarev hζ σ)
  rintro p ⟨hp, hpn, hpζ⟩
  exact ⟨hp, hpn, σ, hpζ, IsConj.refl σ⟩

/-- Sanity check that the hypotheses are satisfiable: applied to the cyclotomic field
`ℚ(ζ₅)` and the identity automorphism, the theorem says that there are infinitely many
primes `p` with `p ≡ 1 (mod 5)`, phrased as `Frob_p = 1`. -/
example :
    {p : ℕ | p.Prime ∧ ¬ p ∣ 5 ∧
      (AlgEquiv.refl : CyclotomicField 5 ℚ ≃ₐ[ℚ] CyclotomicField 5 ℚ)
          (IsCyclotomicExtension.zeta 5 ℚ (CyclotomicField 5 ℚ))
        = (IsCyclotomicExtension.zeta 5 ℚ (CyclotomicField 5 ℚ)) ^ p}.Infinite :=
  chebotarev (IsCyclotomicExtension.zeta_spec 5 ℚ (CyclotomicField 5 ℚ)) AlgEquiv.refl

end Math2

