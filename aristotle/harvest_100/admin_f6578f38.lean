/-
# Hironaka Resolution
Category: Frontier Math
Target: Math2.hironaka_resolution
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Hironaka Resolution
Category: Frontier Math
Target: Math2.hironaka_resolution
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

open MvPolynomial

variable {k : Type*} [Field k]

/-- The affine plane curve `C_{p,q} : y^p = x^q`, as a polynomial in two variables. -/
noncomputable def cuspCurve (k : Type*) [Field k] (p q : ℕ) : MvPolynomial (Fin 2) k :=
  X 1 ^ p - X 0 ^ q

/-- The set of `k`-points of the affine plane curve defined by `f`. -/
def zeroLocus (f : MvPolynomial (Fin 2) k) : Set (Fin 2 → k) := {x | eval x f = 0}

/-- Jacobian criterion: a point of the plane curve `f = 0` is *singular* when all partial
derivatives of `f` vanish there. -/
def IsSingularPoint (f : MvPolynomial (Fin 2) k) (x : Fin 2 → k) : Prop :=
  eval x f = 0 ∧ ∀ i, eval x (pderiv i f) = 0

/-- The monomial parametrization `𝔸¹ → 𝔸²`, `t ↦ (t^p, t^q)`, of the curve `y^p = x^q`. -/
def param (p q : ℕ) (t : k) : Fin 2 → k := ![t ^ p, t ^ q]

@[simp] lemma param_zero_coord (p q : ℕ) (t : k) : param p q t 0 = t ^ p := rfl

@[simp] lemma param_one_coord (p q : ℕ) (t : k) : param p q t 1 = t ^ q := rfl

lemma param_zero (p q : ℕ) (hp : p ≠ 0) (hq : q ≠ 0) : param p q (0 : k) = 0 := by
  funext i
  fin_cases i <;> simp [param, zero_pow, hp, hq]

lemma eq_zero_of_coords {x : Fin 2 → k} (h0 : x 0 = 0) (h1 : x 1 = 0) : x = 0 := by
  funext i
  fin_cases i
  · simpa using h0
  · simpa using h1

/-- A Bézout monomial reconstructs `t` from `t ^ p` and `t ^ q`. -/
lemma zpow_bezout {p q : ℕ} {a b : ℤ} (hab : a * p + b * q = 1) {t : k} (ht : t ≠ 0) :
    (t ^ p) ^ a * (t ^ q) ^ b = t := by
  rw [← zpow_natCast t p, ← zpow_natCast t q, ← zpow_mul, ← zpow_mul, ← zpow_add₀ ht]
  rw [show (p : ℤ) * a + (q : ℤ) * b = 1 by linarith [hab]]
  simp

/-- Bézout coefficients for coprime exponents. -/
lemma exists_bezout {p q : ℕ} (h : Nat.Coprime p q) : ∃ a b : ℤ, a * p + b * q = 1 := by
  refine ⟨Nat.gcdA p q, Nat.gcdB p q, ?_⟩
  have := Nat.gcd_eq_gcd_ab p q
  rw [h] at this
  push_cast at this ⊢
  linarith [this]

section

variable {p q : ℕ}

lemma eval_cuspCurve (x : Fin 2 → k) :
    eval x (cuspCurve k p q) = (x 1) ^ p - (x 0) ^ q := by
  simp [cuspCurve]

lemma eval_pderiv_zero (x : Fin 2 → k) :
    eval x (pderiv (0 : Fin 2) (cuspCurve k p q)) = -((q : k) * x 0 ^ (q - 1)) := by
  simp [cuspCurve, Derivation.leibniz_pow]

lemma eval_pderiv_one (x : Fin 2 → k) :
    eval x (pderiv (1 : Fin 2) (cuspCurve k p q)) = (p : k) * x 1 ^ (p - 1) := by
  simp [cuspCurve, Derivation.leibniz_pow]

/-- The parametrization lands on the curve. -/
lemma param_mem_zeroLocus (t : k) : param p q t ∈ zeroLocus (cuspCurve k p q) := by
  simp [zeroLocus, eval_cuspCurve, param, ← pow_mul, Nat.mul_comm]

/-- Finiteness (properness) of the parametrization: the coordinate ring `k[t]` of the source is
integral over the image of the coordinate ring of the curve, namely `k[t^p, t^q]`. -/
lemma param_isIntegral (hp : p ≠ 0) :
    IsIntegral
      (Algebra.adjoin k ({Polynomial.X ^ p, Polynomial.X ^ q} : Set (Polynomial k)))
      (Polynomial.X : Polynomial k) := by
  set A := Algebra.adjoin k ({Polynomial.X ^ p, Polynomial.X ^ q} : Set (Polynomial k))
  have hmem : (Polynomial.X ^ p : Polynomial k) ∈ A := Algebra.subset_adjoin (by simp)
  exact ⟨Polynomial.X ^ p - Polynomial.C (⟨Polynomial.X ^ p, hmem⟩ : A),
    Polynomial.monic_X_pow_sub_C _ hp, by simp⟩

/-- The parametrization is injective. -/
lemma param_injective (hp : p ≠ 0) (hcop : Nat.Coprime p q) :
    Function.Injective (param (k := k) p q) := by
  obtain ⟨a, b, hab⟩ := exists_bezout hcop
  intro s t hst
  have h0 : s ^ p = t ^ p := congrFun hst 0
  have h1 : s ^ q = t ^ q := congrFun hst 1
  rcases eq_or_ne s 0 with hs | hs
  · subst hs
    have : t ^ p = 0 := by simpa [zero_pow hp] using h0.symm
    exact (pow_eq_zero_iff hp).mp this |>.symm
  · have ht : t ≠ 0 := by
      intro h
      subst h
      exact hs ((pow_eq_zero_iff hp).mp (by simpa [zero_pow hp] using h0))
    rw [← zpow_bezout hab hs, ← zpow_bezout hab ht, h0, h1]

/-- Every point of the curve is in the image of the parametrization; the preimage is given by
an explicit monomial with integer exponents. -/
lemma param_surjOn (hp : p ≠ 0) (hq : q ≠ 0) {a b : ℤ} (hab : a * p + b * q = 1) :
    ∀ x ∈ zeroLocus (cuspCurve k p q), param p q ((x 0) ^ a * (x 1) ^ b) = x := by
  intro x hx
  have hcur : (x 1) ^ p = (x 0) ^ q := by
    have := hx
    simp only [zeroLocus, Set.mem_setOf_eq, eval_cuspCurve, sub_eq_zero] at this
    exact this
  rcases eq_or_ne (x 0) 0 with hx0 | hx0
  · have hx1 : x 1 = 0 := by
      have : (x 1) ^ p = 0 := by rw [hcur, hx0, zero_pow hq]
      exact (pow_eq_zero_iff hp).mp this
    have hab0 : a ≠ 0 ∨ b ≠ 0 := by
      by_contra hcon
      push_neg at hcon
      rw [hcon.1, hcon.2] at hab
      simp at hab
    have ht0 : ((x 0) ^ a * (x 1) ^ b : k) = 0 := by
      rw [hx0, hx1]
      rcases hab0 with h | h
      · rw [zero_zpow a h, zero_mul]
      · rw [zero_zpow b h, mul_zero]
    rw [ht0, param_zero p q hp hq]
    exact (eq_zero_of_coords hx0 hx1).symm
  · have hx1 : x 1 ≠ 0 := by
      intro h
      apply hx0
      have : (x 0) ^ q = 0 := by rw [← hcur, h, zero_pow hp]
      exact (pow_eq_zero_iff hq).mp this
    set t : k := (x 0) ^ a * (x 1) ^ b with ht
    have hcurz : ((x 1) ^ (p : ℤ) : k) = ((x 0) ^ (q : ℤ) : k) := by
      rw [← zpow_natCast (x 1) p, ← zpow_natCast (x 0) q] at hcur
      exact hcur
    have hp' : t ^ p = x 0 := by
      rw [ht, mul_pow, ← zpow_natCast ((x 0) ^ a) p, ← zpow_natCast ((x 1) ^ b) p,
        ← zpow_mul, ← zpow_mul]
      have : ((x 1) ^ (b * (p : ℤ)) : k) = ((x 0) ^ ((q : ℤ) * b) : k) := by
        rw [mul_comm b (p : ℤ), zpow_mul, hcurz, ← zpow_mul]
      rw [this, ← zpow_add₀ hx0]
      rw [show (a * (p : ℤ) + (q : ℤ) * b) = 1 by linarith [hab]]
      simp
    have hq' : t ^ q = x 1 := by
      rw [ht, mul_pow, ← zpow_natCast ((x 0) ^ a) q, ← zpow_natCast ((x 1) ^ b) q,
        ← zpow_mul, ← zpow_mul]
      have : ((x 0) ^ (a * (q : ℤ)) : k) = ((x 1) ^ ((p : ℤ) * a) : k) := by
        rw [mul_comm a (q : ℤ), zpow_mul, ← hcurz, ← zpow_mul]
      rw [this, ← zpow_add₀ hx1]
      rw [show ((p : ℤ) * a + b * (q : ℤ)) = 1 by linarith [hab]]
      simp
    funext i
    fin_cases i
    · simpa using hp'
    · simpa using hq'

end

/-- **Resolution of singularities for the monomial plane curve singularities `y^p = x^q`**
(an explicit instance, in characteristic zero, of Hironaka's resolution theorem).

Let `k` be a field of characteristic `0` and let `p, q ≥ 2` be coprime.  For the plane curve
`C : y^p = x^q` the following hold.

1. `C` is singular exactly at the origin (Jacobian criterion).
2. The map `π : 𝔸¹ → 𝔸²`, `t ↦ (t^p, t^q)`, is a bijection from the smooth curve `𝔸¹` onto `C`,
   i.e. `π` is a surjective, injective (in particular proper, quasi-finite) parametrization.
3. `π` restricts to a bijection of `𝔸¹ ∖ {0}` onto the smooth locus `C ∖ {0}`, and its inverse
   there is given by the monomial rational function `x ↦ x₀^a · x₁^b` for Bézout exponents
   `a·p + b·q = 1`; hence `π` is birational and is an isomorphism over the smooth locus.
4. The exceptional fibre over the singular point is the single point `t = 0`.
5. Away from the exceptional point the differential of `π` is nonzero, so `π` is an immersion
   there.
6. `π` is a finite (hence proper) morphism: the coordinate ring `k[t]` of the source is integral
   over the coordinate ring `k[t^p, t^q]` of the curve. -/
theorem hironaka_resolution (k : Type*) [Field k] [CharZero k] (p q : ℕ)
    (hp : 2 ≤ p) (hq : 2 ≤ q) (hcop : Nat.Coprime p q) :
    -- (1) the singular locus of `C` is exactly the origin
    {x | IsSingularPoint (cuspCurve k p q) x} = {0} ∧
    -- (2) `π` is a bijection from the smooth source `𝔸¹` onto `C`
    Set.BijOn (param p q) (Set.univ : Set k) (zeroLocus (cuspCurve k p q)) ∧
    -- (3) `π` is an isomorphism over the smooth locus, with monomial (rational) inverse
    (∃ a b : ℤ, a * p + b * q = 1 ∧
      Set.BijOn (param p q) {t : k | t ≠ 0} (zeroLocus (cuspCurve k p q) \ {0}) ∧
      (∀ t : k, t ≠ 0 → (param p q t 0) ^ a * (param p q t 1) ^ b = t) ∧
      (∀ x ∈ zeroLocus (cuspCurve k p q), param p q ((x 0) ^ a * (x 1) ^ b) = x)) ∧
    -- (4) the exceptional fibre over the singular point is a single reduced point
    (param (k := k) p q) ⁻¹' {0} = {0} ∧
    -- (5) `π` is an immersion away from the exceptional point
    (∀ t : k, t ≠ 0 → ((p : k) * t ^ (p - 1), (q : k) * t ^ (q - 1)) ≠ (0, 0)) ∧
    -- (6) `π` is finite: the source is integral over the curve
    IsIntegral
      (Algebra.adjoin k ({Polynomial.X ^ p, Polynomial.X ^ q} : Set (Polynomial k)))
      (Polynomial.X : Polynomial k) := by
  have hp0 : p ≠ 0 := by omega
  have hq0 : q ≠ 0 := by omega
  have hpk : (p : k) ≠ 0 := Nat.cast_ne_zero.mpr hp0
  have hqk : (q : k) ≠ 0 := Nat.cast_ne_zero.mpr hq0
  obtain ⟨a, b, hab⟩ := exists_bezout hcop
  have hinj : Function.Injective (param (k := k) p q) := param_injective hp0 hcop
  have hsurj : ∀ x ∈ zeroLocus (cuspCurve k p q), param p q ((x 0) ^ a * (x 1) ^ b) = x :=
    param_surjOn hp0 hq0 hab
  have hmem : ∀ t : k, param p q t ∈ zeroLocus (cuspCurve k p q) := fun t =>
    param_mem_zeroLocus t
  have hp0' : param (k := k) p q 0 = 0 := param_zero p q hp0 hq0
  refine ⟨?_, ?_, ⟨a, b, hab, ?_, ?_, hsurj⟩, ?_, ?_, param_isIntegral hp0⟩
  · -- (1) singular locus
    ext x
    simp only [Set.mem_setOf_eq, Set.mem_singleton_iff, IsSingularPoint]
    constructor
    · rintro ⟨-, hd⟩
      have h0 := hd 0
      have h1 := hd 1
      rw [eval_pderiv_zero] at h0
      rw [eval_pderiv_one] at h1
      have hx0 : x 0 = 0 := by
        have : x 0 ^ (q - 1) = 0 := by
          rcases mul_eq_zero.mp (neg_eq_zero.mp h0) with h | h
          · exact absurd h hqk
          · exact h
        exact pow_eq_zero_iff (by omega : q - 1 ≠ 0) |>.mp this
      have hx1 : x 1 = 0 := by
        have : x 1 ^ (p - 1) = 0 := by
          rcases mul_eq_zero.mp h1 with h | h
          · exact absurd h hpk
          · exact h
        exact pow_eq_zero_iff (by omega : p - 1 ≠ 0) |>.mp this
      exact eq_zero_of_coords hx0 hx1
    · rintro rfl
      refine ⟨?_, ?_⟩
      · rw [eval_cuspCurve]
        simp [zero_pow, hp0, hq0]
      · intro i
        fin_cases i
        · show eval (0 : Fin 2 → k) (pderiv (0 : Fin 2) (cuspCurve k p q)) = 0
          rw [eval_pderiv_zero]
          simp [zero_pow (by omega : q - 1 ≠ 0)]
        · show eval (0 : Fin 2 → k) (pderiv (1 : Fin 2) (cuspCurve k p q)) = 0
          rw [eval_pderiv_one]
          simp [zero_pow (by omega : p - 1 ≠ 0)]
  · -- (2) bijection onto the curve
    refine ⟨fun t _ => hmem t, fun s _ t _ h => hinj h, ?_⟩
    intro x hx
    exact ⟨(x 0) ^ a * (x 1) ^ b, Set.mem_univ _, hsurj x hx⟩
  · -- (3a) bijection onto the smooth locus
    refine ⟨?_, fun s _ t _ h => hinj h, ?_⟩
    · intro t ht
      refine ⟨hmem t, ?_⟩
      simp only [Set.mem_singleton_iff]
      intro hcon
      exact ht (hinj (hcon.trans hp0'.symm))
    · rintro x ⟨hx, hx0⟩
      refine ⟨(x 0) ^ a * (x 1) ^ b, ?_, hsurj x hx⟩
      simp only [Set.mem_setOf_eq]
      intro hcon
      apply hx0
      simp only [Set.mem_singleton_iff]
      rw [← hsurj x hx, hcon, hp0']
  · -- (3b) the monomial inverse
    intro t ht
    simpa using zpow_bezout hab ht
  · -- (4) exceptional fibre
    ext t
    simp only [Set.mem_preimage, Set.mem_singleton_iff]
    constructor
    · intro h
      exact hinj (h.trans hp0'.symm)
    · rintro rfl
      exact hp0'
  · -- (5) immersion away from the exceptional point
    intro t ht hcon
    have : (p : k) * t ^ (p - 1) = 0 := congrArg Prod.fst hcon
    rcases mul_eq_zero.mp this with h | h
    · exact hpk h
    · exact ht (pow_eq_zero_iff (by omega : p - 1 ≠ 0) |>.mp h)

end Math2

