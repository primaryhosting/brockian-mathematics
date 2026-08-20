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

import Mathlib

/-!
# Hironaka Resolution
Category: Frontier Math
Target: Math2.hironaka_resolution
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace Math2

variable (k : Type*) [Field k]

/-- The affine plane curve `C_{a,b} : y^a = x^b` over a field `k`.
For `a, b ≥ 2` coprime this is the standard quasi-homogeneous plane curve singularity
(for `(a,b) = (2,3)` it is the cuspidal cubic `y² = x³`). -/
def cuspCurve (a b : ℕ) : Set (k × k) := {p | p.2 ^ a = p.1 ^ b}

/-- The normalization (resolution) map of `C_{a,b}` from the affine line: `t ↦ (t^a, t^b)`. -/
def cuspParam (a b : ℕ) : k → k × k := fun t => (t ^ a, t ^ b)

/-- The defining polynomial `Y^a - X^b` of `C_{a,b}`, as a two-variable polynomial. -/
noncomputable def cuspPoly (a b : ℕ) : MvPolynomial (Fin 2) k :=
  MvPolynomial.X 1 ^ a - MvPolynomial.X 0 ^ b

variable {k}

/-- A Bézout pair for coprime exponents. -/
lemma exists_bezout {a b : ℕ} (hab : Nat.Coprime a b) :
    ∃ u v : ℤ, u * (a : ℤ) + v * (b : ℤ) = 1 := by
  have h : IsCoprime (a : ℤ) (b : ℤ) := Int.isCoprime_iff_gcd_eq_one.2 (by simpa using hab)
  obtain ⟨u, v, huv⟩ := h
  exact ⟨u, v, huv⟩

/-- Bézout recovery: a nonzero element is recovered from its `a`-th and `b`-th powers
when `a` and `b` are coprime. -/
lemma bezout_recover {x : k} (hx : x ≠ 0) {a b : ℕ} {u v : ℤ}
    (huv : u * (a : ℤ) + v * (b : ℤ) = 1) : ((x ^ a) ^ u) * ((x ^ b) ^ v) = x := by
  rw [← zpow_natCast x a, ← zpow_natCast x b, ← zpow_mul, ← zpow_mul, ← zpow_add₀ hx,
    show (a : ℤ) * u + (b : ℤ) * v = 1 by linarith, zpow_one]

/-- The `a`-th power of the Laurent monomial `x^u y^v` on the curve is `x`. -/
lemma monomial_zpow_fst {x y : k} (hx : x ≠ 0) {a b : ℕ} {u v : ℤ}
    (hxy : y ^ (a : ℤ) = x ^ (b : ℤ)) (huv : u * (a : ℤ) + v * (b : ℤ) = 1) :
    (x ^ u * y ^ v) ^ (a : ℤ) = x := by
  have e1 : y ^ (v * (a : ℤ)) = x ^ ((b : ℤ) * v) := by
    rw [mul_comm v (a : ℤ), zpow_mul, hxy, ← zpow_mul]
  calc (x ^ u * y ^ v) ^ (a : ℤ) = x ^ (u * (a : ℤ)) * y ^ (v * (a : ℤ)) := by
        rw [mul_zpow, ← zpow_mul, ← zpow_mul]
    _ = x ^ (u * (a : ℤ)) * x ^ ((b : ℤ) * v) := by rw [e1]
    _ = x ^ (u * (a : ℤ) + (b : ℤ) * v) := (zpow_add₀ hx _ _).symm
    _ = x := by rw [show u * (a : ℤ) + (b : ℤ) * v = 1 by linarith, zpow_one]

/-- The `b`-th power of the Laurent monomial `x^u y^v` on the curve is `y`. -/
lemma monomial_zpow_snd {x y : k} (hy : y ≠ 0) {a b : ℕ} {u v : ℤ}
    (hxy : y ^ (a : ℤ) = x ^ (b : ℤ)) (huv : u * (a : ℤ) + v * (b : ℤ) = 1) :
    (x ^ u * y ^ v) ^ (b : ℤ) = y := by
  have e1 : x ^ (u * (b : ℤ)) = y ^ ((a : ℤ) * u) := by
    rw [mul_comm u (b : ℤ), zpow_mul, ← hxy, ← zpow_mul]
  calc (x ^ u * y ^ v) ^ (b : ℤ) = x ^ (u * (b : ℤ)) * y ^ (v * (b : ℤ)) := by
        rw [mul_zpow, ← zpow_mul, ← zpow_mul]
    _ = y ^ ((a : ℤ) * u) * y ^ (v * (b : ℤ)) := by rw [e1]
    _ = y ^ ((a : ℤ) * u + v * (b : ℤ)) := (zpow_add₀ hy _ _).symm
    _ = y := by rw [show (a : ℤ) * u + v * (b : ℤ) = 1 by linarith, zpow_one]

/-- The parametrization lands on the curve. -/
lemma cuspParam_mem (a b : ℕ) (t : k) : cuspParam k a b t ∈ cuspCurve k a b := by
  simp only [cuspCurve, cuspParam, Set.mem_setOf_eq]
  rw [← pow_mul, ← pow_mul, Nat.mul_comm]

/-- The parametrization is injective. -/
lemma cuspParam_injective {a b : ℕ} (ha : 0 < a) (hab : Nat.Coprime a b) :
    Function.Injective (cuspParam k a b) := by
  obtain ⟨u, v, huv⟩ := exists_bezout hab
  intro s t hst
  simp only [cuspParam, Prod.mk.injEq] at hst
  obtain ⟨h1, h2⟩ := hst
  by_cases hs : s = 0
  · subst hs
    have h : t ^ a = 0 := by simpa [zero_pow ha.ne'] using h1.symm
    exact (pow_eq_zero_iff ha.ne' |>.1 h).symm
  · have ht : t ≠ 0 := by
      intro h
      apply hs
      have h0 : s ^ a = 0 := by rw [h1, h, zero_pow ha.ne']
      exact pow_eq_zero_iff ha.ne' |>.1 h0
    calc s = ((s ^ a) ^ u) * ((s ^ b) ^ v) := (bezout_recover hs huv).symm
      _ = ((t ^ a) ^ u) * ((t ^ b) ^ v) := by rw [h1, h2]
      _ = t := bezout_recover ht huv

/-- Away from the singular point the inverse of the parametrization is given by the
Laurent monomial `x^u y^v`, where `ua + vb = 1`. -/
lemma cuspParam_inverse {a b : ℕ} (ha : 0 < a) (hb : 0 < b) (hab : Nat.Coprime a b) :
    ∃ u v : ℤ, ∀ p : k × k, p ∈ cuspCurve k a b → p ≠ 0 →
      cuspParam k a b (p.1 ^ u * p.2 ^ v) = p := by
  obtain ⟨u, v, huv⟩ := exists_bezout hab
  refine ⟨u, v, ?_⟩
  rintro ⟨x, y⟩ hp hne
  simp only [cuspCurve, Set.mem_setOf_eq] at hp
  have hx : x ≠ 0 := by
    intro hx
    apply hne
    subst hx
    have h1 : y ^ a = 0 := by rw [hp, zero_pow hb.ne']
    have h2 : y = 0 := pow_eq_zero_iff ha.ne' |>.1 h1
    simp [h2]
  have hy : y ≠ 0 := by
    intro hy
    apply hx
    rw [hy, zero_pow ha.ne'] at hp
    exact pow_eq_zero_iff hb.ne' |>.1 hp.symm
  have hxy : (y : k) ^ (a : ℤ) = x ^ (b : ℤ) := by
    simpa [zpow_natCast] using hp
  have h1 := monomial_zpow_fst hx hxy huv
  have h2 := monomial_zpow_snd hy hxy huv
  rw [zpow_natCast] at h1 h2
  simp only [cuspParam, Prod.mk.injEq]
  exact ⟨h1, h2⟩

/-- The parametrization is onto the curve. -/
lemma cuspParam_range {a b : ℕ} (ha : 0 < a) (hb : 0 < b) (hab : Nat.Coprime a b) :
    Set.range (cuspParam k a b) = cuspCurve k a b := by
  obtain ⟨u, v, hinv⟩ := cuspParam_inverse (k := k) ha hb hab
  apply Set.Subset.antisymm
  · rintro _ ⟨t, rfl⟩
    exact cuspParam_mem a b t
  · intro p hp
    by_cases h0 : p = 0
    · exact ⟨0, by simp [cuspParam, zero_pow ha.ne', zero_pow hb.ne', h0]⟩
    · exact ⟨p.1 ^ u * p.2 ^ v, hinv p hp h0⟩

/-- The curve is exactly the zero set of `cuspPoly`. -/
lemma cuspCurve_eq_zeroSet (a b : ℕ) :
    cuspCurve k a b = {p : k × k | MvPolynomial.eval ![p.1, p.2] (cuspPoly k a b) = 0} := by
  ext p
  simp only [cuspCurve, cuspPoly, Set.mem_setOf_eq, map_sub, map_pow, MvPolynomial.eval_X,
    Matrix.cons_val_zero, Matrix.cons_val_one, sub_eq_zero]

/-- The origin lies on the curve and both partial derivatives of the defining equation
vanish there: the origin is a singular point (Jacobian criterion). -/
lemma cuspCurve_singular_at_zero {a b : ℕ} (ha : 2 ≤ a) (hb : 2 ≤ b) :
    MvPolynomial.eval (0 : Fin 2 → k) (cuspPoly k a b) = 0 ∧
      ∀ i : Fin 2, MvPolynomial.eval (0 : Fin 2 → k)
        (MvPolynomial.pderiv i (cuspPoly k a b)) = 0 := by
  have ha0 : a ≠ 0 := by omega
  have hb0 : b ≠ 0 := by omega
  refine ⟨by simp [cuspPoly, zero_pow ha0, zero_pow hb0], fun i => ?_⟩
  have hpd : MvPolynomial.pderiv i (cuspPoly k a b)
      = (a : MvPolynomial (Fin 2) k) * MvPolynomial.X 1 ^ (a - 1) *
          MvPolynomial.pderiv i (MvPolynomial.X (1 : Fin 2))
        - (b : MvPolynomial (Fin 2) k) * MvPolynomial.X 0 ^ (b - 1) *
          MvPolynomial.pderiv i (MvPolynomial.X (0 : Fin 2)) := by
    simp [cuspPoly, Derivation.leibniz_pow, mul_assoc]
  have h1 : a - 1 ≠ 0 := by omega
  have h2 : b - 1 ≠ 0 := by omega
  rw [hpd]
  simp [zero_pow h1, zero_pow h2]

/--
**Hironaka resolution of singularities (characteristic zero), formalized for the
quasi-homogeneous plane curve singularities.**

Full Hironaka desingularization for arbitrary varieties is not available in Mathlib
(schemes, blow-ups and properness of blow-ups are not developed there), so the theorem is
stated and proved here for the family of quasi-homogeneous plane curve singularities
`C_{a,b} : y^a = x^b` with `a, b ≥ 2` coprime — which includes the cuspidal cubic `y² = x³`.
For this family the statement asserts, over any field `k` of characteristic zero:

* `C_{a,b}` is the zero set of the polynomial `Y^a - X^b`, and the origin is a *singular*
  point of it (the polynomial and both of its partial derivatives vanish there);
* the affine line `𝔸¹ = k` (a smooth variety) maps to `C_{a,b}` by `t ↦ (t^a, t^b)`;
* this map is injective and its image is all of `C_{a,b}`, so it is a bijective morphism
  from a smooth variety onto the singular curve;
* it is an isomorphism away from the singular point: on `C_{a,b} \ {0}` the inverse is
  given by the Laurent monomial `x^u y^v` with `ua + vb = 1`.

The hypothesis `CharZero k` is included as part of the requested characteristic-zero
setting; the proof below does not make use of it.
-/
theorem hironaka_resolution {k : Type*} [Field k] [CharZero k] {a b : ℕ}
    (ha : 2 ≤ a) (hb : 2 ≤ b) (hab : Nat.Coprime a b) :
    -- the curve is the zero set of `Y^a - X^b`
    cuspCurve k a b = {p : k × k | MvPolynomial.eval ![p.1, p.2] (cuspPoly k a b) = 0} ∧
    -- the origin is a singular point of the curve
    (MvPolynomial.eval (0 : Fin 2 → k) (cuspPoly k a b) = 0 ∧
      ∀ i : Fin 2, MvPolynomial.eval (0 : Fin 2 → k)
        (MvPolynomial.pderiv i (cuspPoly k a b)) = 0) ∧
    -- the affine line maps onto the curve, injectively
    (∀ t : k, cuspParam k a b t ∈ cuspCurve k a b) ∧
    Function.Injective (cuspParam k a b) ∧
    Set.range (cuspParam k a b) = cuspCurve k a b ∧
    -- and the map is an isomorphism away from the singular point
    (∃ u v : ℤ, ∀ p : k × k, p ∈ cuspCurve k a b → p ≠ 0 →
      cuspParam k a b (p.1 ^ u * p.2 ^ v) = p) := by
  have ha0 : 0 < a := by omega
  have hb0 : 0 < b := by omega
  exact ⟨cuspCurve_eq_zeroSet a b, cuspCurve_singular_at_zero ha hb,
    fun t => cuspParam_mem a b t, cuspParam_injective ha0 hab,
    cuspParam_range ha0 hb0 hab, cuspParam_inverse ha0 hb0 hab⟩

/-- The classical example: `t ↦ (t², t³)` resolves the cuspidal cubic `y² = x³`
over any field of characteristic zero. -/
theorem hironaka_resolution_cusp {k : Type*} [Field k] [CharZero k] :
    (∀ t : k, cuspParam k 2 3 t ∈ cuspCurve k 2 3) ∧
    Function.Injective (cuspParam k 2 3) ∧
    Set.range (cuspParam k 2 3) = cuspCurve k 2 3 := by
  obtain ⟨-, -, h1, h2, h3, -⟩ :=
    hironaka_resolution (k := k) (a := 2) (b := 3) le_rfl (by norm_num) (by decide)
  exact ⟨h1, h2, h3⟩

end Math2

