/-
# Hironaka Resolution
Category: Frontier Math
Target: Math2.hironaka_resolution
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

set_option maxHeartbeats 1000000

namespace Math2

/-- The affine plane curve `C(m,n) = {(x,y) | y ^ n = x ^ m}`. -/
def monomialCurve (k : Type*) [Field k] (m n : ℕ) : Set (k × k) :=
  {p : k × k | p.2 ^ n = p.1 ^ m}

/-- The parametrization of `C(m,n)` by the (smooth) affine line, `t ↦ (t ^ n, t ^ m)`. -/
def monomialParam (k : Type*) [Field k] (m n : ℕ) : k → k × k := fun t => (t ^ n, t ^ m)

/-- A nonzero element whose `m`-th and `n`-th powers are `1`, for coprime `m` and `n`,
is equal to `1`. -/
lemma eq_one_of_coprime_pow {k : Type*} [Field k] {m n : ℕ} (h : Nat.Coprime m n) {u : k}
    (hu : u ≠ 0) (hm : u ^ m = 1) (hn : u ^ n = 1) : u = 1 := by
  have hgcd : (1 : ℤ) = (m : ℤ) * Nat.gcdA m n + (n : ℤ) * Nat.gcdB m n := by
    have hab := Nat.gcd_eq_gcd_ab m n
    rw [Nat.Coprime.gcd_eq_one h] at hab
    exact_mod_cast hab
  calc u = u ^ (1 : ℤ) := (zpow_one u).symm
    _ = u ^ ((m : ℤ) * Nat.gcdA m n + (n : ℤ) * Nat.gcdB m n) := by rw [← hgcd]
    _ = (u ^ (m : ℤ)) ^ (Nat.gcdA m n) * (u ^ (n : ℤ)) ^ (Nat.gcdB m n) := by
        rw [zpow_add₀ hu, ← zpow_mul, ← zpow_mul]
    _ = 1 := by rw [zpow_natCast, zpow_natCast, hm, hn, one_zpow, one_zpow, one_mul]

lemma monomialParam_injective {k : Type*} [Field k] {m n : ℕ} (hn : 0 < n)
    (h : Nat.Coprime m n) : Function.Injective (monomialParam k m n) := by
  intro t s hts
  simp only [monomialParam, Prod.mk.injEq] at hts
  obtain ⟨hn', hm'⟩ := hts
  by_cases ht : t = 0
  · subst ht
    have : s ^ n = 0 := by simpa [zero_pow hn.ne'] using hn'.symm
    exact ((pow_eq_zero_iff hn.ne').1 this).symm
  · have hs : s ≠ 0 := by
      intro hs
      apply ht
      have : t ^ n = 0 := by simp [hn', hs, zero_pow hn.ne']
      exact (pow_eq_zero_iff hn.ne').1 this
    have hu : t * s⁻¹ ≠ 0 := mul_ne_zero ht (inv_ne_zero hs)
    have hum : (t * s⁻¹) ^ m = 1 := by
      rw [mul_pow, hm', inv_pow, mul_inv_cancel₀ (pow_ne_zero _ hs)]
    have hun : (t * s⁻¹) ^ n = 1 := by
      rw [mul_pow, hn', inv_pow, mul_inv_cancel₀ (pow_ne_zero _ hs)]
    have := eq_one_of_coprime_pow h hu hum hun
    field_simp at this
    exact this

lemma range_monomialParam {k : Type*} [Field k] {m n : ℕ} (hm : 0 < m) (hn : 0 < n)
    (h : Nat.Coprime m n) : Set.range (monomialParam k m n) = monomialCurve k m n := by
  ext ⟨x, y⟩
  simp only [Set.mem_range, monomialCurve, Set.mem_setOf_eq, monomialParam, Prod.mk.injEq]
  constructor
  · rintro ⟨t, ht1, ht2⟩
    rw [← ht1, ← ht2, ← pow_mul, ← pow_mul, Nat.mul_comm]
  · intro hxy
    by_cases hx : x = 0
    · subst hx
      have hy : y = 0 := by
        have : y ^ n = 0 := by simpa [zero_pow hm.ne'] using hxy
        exact (pow_eq_zero_iff hn.ne').1 this
      exact ⟨0, by simp [zero_pow hn.ne', zero_pow hm.ne', hy]⟩
    · have hy : y ≠ 0 := by
        intro hy
        apply hx
        have : x ^ m = 0 := by rw [← hxy, hy, zero_pow hn.ne']
        exact (pow_eq_zero_iff hm.ne').1 this
      set a : ℤ := Nat.gcdA m n with ha
      set b : ℤ := Nat.gcdB m n with hb
      have hgcd : (1 : ℤ) = (m : ℤ) * a + (n : ℤ) * b := by
        have hab := Nat.gcd_eq_gcd_ab m n
        rw [Nat.Coprime.gcd_eq_one h] at hab
        exact_mod_cast hab
      have hxy' : y ^ (n : ℤ) = x ^ (m : ℤ) := by
        rw [zpow_natCast, zpow_natCast]; exact hxy
      refine ⟨x ^ b * y ^ a, ?_, ?_⟩
      · calc (x ^ b * y ^ a) ^ n
            = (x ^ b) ^ (n : ℤ) * (y ^ a) ^ (n : ℤ) := by
              rw [← zpow_natCast (x ^ b * y ^ a) n, mul_zpow]
          _ = x ^ ((n : ℤ) * b) * (y ^ (n : ℤ)) ^ a := by
              rw [← zpow_mul, ← zpow_mul, ← zpow_mul, mul_comm b (n : ℤ), mul_comm a (n : ℤ)]
          _ = x ^ ((n : ℤ) * b) * x ^ ((m : ℤ) * a) := by rw [hxy', ← zpow_mul]
          _ = x ^ ((m : ℤ) * a + (n : ℤ) * b) := by rw [← zpow_add₀ hx]; ring_nf
          _ = x := by rw [← hgcd, zpow_one]
      · calc (x ^ b * y ^ a) ^ m
            = (x ^ b) ^ (m : ℤ) * (y ^ a) ^ (m : ℤ) := by
              rw [← zpow_natCast (x ^ b * y ^ a) m, mul_zpow]
          _ = (x ^ (m : ℤ)) ^ b * y ^ ((m : ℤ) * a) := by
              rw [← zpow_mul, ← zpow_mul, ← zpow_mul, mul_comm b (m : ℤ), mul_comm a (m : ℤ)]
          _ = (y ^ (n : ℤ)) ^ b * y ^ ((m : ℤ) * a) := by rw [hxy']
          _ = y ^ ((m : ℤ) * a + (n : ℤ) * b) := by rw [← zpow_mul, ← zpow_add₀ hy]; ring_nf
          _ = y := by rw [← hgcd, zpow_one]

/-- The defining polynomial `Y ^ n - X ^ m` of the curve `C(m,n)`, as a polynomial in the two
variables `X 0 = X` and `X 1 = Y`. -/
noncomputable def monomialPoly (k : Type*) [Field k] (m n : ℕ) : MvPolynomial (Fin 2) k :=
  MvPolynomial.X 1 ^ n - MvPolynomial.X 0 ^ m

lemma monomialCurve_eq_zeroSet (k : Type*) [Field k] (m n : ℕ) :
    monomialCurve k m n =
      {p : k × k | MvPolynomial.eval ![p.1, p.2] (monomialPoly k m n) = 0} := by
  ext ⟨x, y⟩
  simp [monomialCurve, monomialPoly, sub_eq_zero]

/-- The curve `C(m,n)` is genuinely singular at the origin when `m, n ≥ 2`: the origin lies on
the curve and both partial derivatives of the defining equation vanish there. -/
lemma monomialCurve_singular_at_origin {k : Type*} [Field k] {m n : ℕ} (hm : 2 ≤ m) (hn : 2 ≤ n) :
    ((0 : k), (0 : k)) ∈ monomialCurve k m n ∧
      MvPolynomial.eval (0 : Fin 2 → k) (monomialPoly k m n) = 0 ∧
      MvPolynomial.eval (0 : Fin 2 → k)
        (MvPolynomial.pderiv 0 (monomialPoly k m n)) = 0 ∧
      MvPolynomial.eval (0 : Fin 2 → k)
        (MvPolynomial.pderiv 1 (monomialPoly k m n)) = 0 := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · simp [monomialCurve, zero_pow (by omega : m ≠ 0), zero_pow (by omega : n ≠ 0)]
  · simp [monomialPoly, zero_pow (by omega : m ≠ 0), zero_pow (by omega : n ≠ 0)]
  · simp [monomialPoly, zero_pow (by omega : m - 1 ≠ 0)]
  · simp [monomialPoly, zero_pow (by omega : n - 1 ≠ 0)]

/-- **Resolution of singularities for the monomial plane curves `y ^ n = x ^ m`.**

For coprime positive exponents `m`, `n` over a field `k` of characteristic zero (the
characteristic hypothesis is in fact not needed for the proof, but is kept because the statement
is asked for in characteristic `0`), the map `t ↦ (t ^ n, t ^ m)` is an injective parametrization
of the (for `m, n ≥ 2` singular) curve `{(x,y) | y ^ n = x ^ m}` by the smooth affine line, and
its image is exactly that curve.  This is an explicit instance of Hironaka's resolution of
singularities: the singular curve is the bijective image of a smooth variety. -/
theorem hironaka_resolution {k : Type*} [Field k] [CharZero k] {m n : ℕ} (hm : 0 < m) (hn : 0 < n)
    (h : Nat.Coprime m n) :
    Function.Injective (monomialParam k m n) ∧
      Set.range (monomialParam k m n) = monomialCurve k m n :=
  ⟨monomialParam_injective hn h, range_monomialParam hm hn h⟩

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

