import RequestProject.Places

/-!
# Divisors, Riemann–Roch spaces and their dimensions on the projective line

* `Math2.Divisor K` : divisors on `ℙ¹_K`, i.e. finitely supported `ℤ`-valued functions on the
  set of closed points;
* `Math2.deg D` : the degree of a divisor;
* `Math2.riemannRochSpace D` : the Riemann–Roch space `L(D) = {f : ord_v f ≥ -D v for all v}`;
* `Math2.ell D` : its dimension `ℓ(D)` over `K`.

The main result of this file is `Math2.ell_eq`: `ℓ(D) = max (deg D + 1) 0`.
-/

open Polynomial

noncomputable section

namespace Math2

variable {K : Type*} [Field K]

/-- The degree of a closed point of `ℙ¹_K`: the degree of the corresponding monic irreducible
polynomial, resp. `1` for the point at infinity. -/
def degPlace : Place K → ℤ
  | none => 1
  | some p => ((p : K[X]).natDegree : ℤ)

@[simp] theorem degPlace_infty : degPlace (none : Place K) = 1 := rfl

@[simp] theorem degPlace_finite (p : FinitePlace K) :
    degPlace (some p) = ((p : K[X]).natDegree : ℤ) := rfl

/-- Divisors on `ℙ¹_K`. -/
abbrev Divisor (K : Type*) [Field K] : Type _ := Place K →₀ ℤ

/-- The degree homomorphism on divisors. -/
def degHom : Divisor K →+ ℤ :=
  Finsupp.liftAddHom fun v => AddMonoidHom.mulRight (degPlace v)

/-- The degree of a divisor. -/
def deg (D : Divisor K) : ℤ := degHom D

theorem deg_def (D : Divisor K) : deg D = ∑ v ∈ D.support, D v * degPlace v := rfl

@[simp] theorem deg_single (v : Place K) (n : ℤ) :
    deg (Finsupp.single v n) = n * degPlace v := by
  simp [deg, degHom]

theorem deg_sub (D E : Divisor K) : deg (D - E) = deg D - deg E := by
  simp [deg, map_sub]

/-- The Riemann–Roch space `L(D)` of a divisor `D`: the rational functions whose order of
vanishing at every place `v` is at least `-D v` (together with `0`). -/
def riemannRochSpace (D : Divisor K) : Submodule K (RatFunc K) where
  carrier := {f | f = 0 ∨ ∀ v : Place K, -(D v) ≤ ord v f}
  zero_mem' := Or.inl rfl
  add_mem' := by
    rintro f g (rfl | hf) hg
    · simpa using hg
    · rcases hg with rfl | hg
      · simpa using Or.inr hf
      rcases eq_or_ne f 0 with rfl | hf0
      · simpa using Or.inr hg
      rcases eq_or_ne g 0 with rfl | hg0
      · simpa using Or.inr hf
      rcases eq_or_ne (f + g) 0 with h0 | h0
      · exact Or.inl h0
      refine Or.inr fun v => ?_
      have := min_le_ord_add v hf0 hg0 h0
      have h1 := hf v
      have h2 := hg v
      omega
  smul_mem' := by
    rintro c f (rfl | hf)
    · simpa using Or.inl rfl
    · rcases eq_or_ne c 0 with rfl | hc
      · simpa using Or.inl rfl
      rcases eq_or_ne f 0 with rfl | hf0
      · simpa using Or.inl rfl
      refine Or.inr fun v => ?_
      have hCc : (RatFunc.C c : RatFunc K) ≠ 0 := by
        simpa using hc
      rw [RatFunc.smul_eq_C_mul, ord_mul v hCc hf0, ord_C]
      simpa using hf v

theorem mem_riemannRochSpace {D : Divisor K} {f : RatFunc K} :
    f ∈ riemannRochSpace D ↔ f = 0 ∨ ∀ v : Place K, -(D v) ≤ ord v f := Iff.rfl

/-- The dimension `ℓ(D)` of the Riemann–Roch space of `D`. -/
def ell (D : Divisor K) : ℕ := Module.finrank K (riemannRochSpace D)

/-- The rational function attached to a place: the monic irreducible polynomial itself at a
finite place, and `1` at the place at infinity. -/
def placeElt : Place K → RatFunc K
  | none => 1
  | some p => algebraMap K[X] (RatFunc K) (p : K[X])

theorem placeElt_ne_zero (v : Place K) : placeElt v ≠ 0 := by
  cases v with
  | none => simp [placeElt]
  | some p => exact RatFunc.algebraMap_ne_zero p.ne_zero

theorem ord_placeElt_finite (q p : FinitePlace K) :
    ord (some q) (placeElt (some p)) = if p = q then 1 else 0 := by
  rw [placeElt, ord_polynomial_finite]
  by_cases h : p = q
  · subst h; simp
  · simp [h, mult_eq_zero_of_ne q p (Ne.symm h)]

theorem ord_placeElt_infty (v : Place K) :
    ord (none : Place K) (placeElt v) = -degPlace v + (if v = none then 1 else 0) := by
  cases v with
  | none => simp [placeElt]
  | some p => simp [placeElt, ord_polynomial_infty]

theorem ord_finite_placeElt_infty (q : FinitePlace K) :
    ord (some q) (placeElt (none : Place K)) = 0 := by
  simp [placeElt]

/-- A rational function whose divisor is the "finite part" of `D`. -/
def divFun (D : Divisor K) : RatFunc K := ∏ v ∈ D.support, placeElt v ^ (D v)

theorem divFun_ne_zero (D : Divisor K) : divFun D ≠ 0 :=
  Finset.prod_ne_zero_iff.2 fun v _ => zpow_ne_zero _ (placeElt_ne_zero v)

theorem ord_divFun (w : Place K) (D : Divisor K) :
    ord w (divFun D) = ∑ v ∈ D.support, D v * ord w (placeElt v) := by
  rw [divFun, ord_prod w _ _ fun v _ => zpow_ne_zero _ (placeElt_ne_zero v)]
  exact Finset.sum_congr rfl fun v _ => ord_zpow w (placeElt_ne_zero v) (D v)

theorem ord_divFun_finite (D : Divisor K) (q : FinitePlace K) :
    ord (some q) (divFun D) = D (some q) := by
  classical
  rw [ord_divFun]
  rw [Finset.sum_congr rfl (g := fun v => if v = some q then D v else 0) ?_]
  · rw [Finset.sum_ite_eq' D.support (some q) (fun v => D v)]
    by_cases h : some q ∈ D.support
    · simp [h]
    · simp only [h, if_false]
      exact (Finsupp.notMem_support_iff.1 h).symm
  · intro v _
    cases v with
    | none => simp [ord_finite_placeElt_infty]
    | some p =>
      rw [ord_placeElt_finite]
      by_cases h : p = q
      · subst h; simp
      · simp [h, Ne.symm h, Option.some_inj]

theorem ord_divFun_infty (D : Divisor K) :
    ord (none : Place K) (divFun D) = D none - deg D := by
  classical
  rw [ord_divFun]
  have : ∀ v ∈ D.support, D v * ord (none : Place K) (placeElt v)
      = -(D v * degPlace v) + (if v = none then D v else 0) := by
    intro v _
    rw [ord_placeElt_infty]
    by_cases h : v = none <;> simp [h] <;> ring
  rw [Finset.sum_congr rfl this, Finset.sum_add_distrib, ← Finset.sum_neg_distrib,
    Finset.sum_ite_eq' D.support none (fun v => D v)]
  have hdeg : deg D = ∑ v ∈ D.support, D v * degPlace v := rfl
  by_cases h : (none : Place K) ∈ D.support
  · simp [h, hdeg]
    ring
  · simp only [h, if_false]
    rw [Finsupp.notMem_support_iff.1 h]
    simp [hdeg]

/-- The space of polynomials of degree `< m`, viewed inside the rational function field. -/
def polySpace (K : Type*) [Field K] (m : ℕ) : Submodule K (RatFunc K) :=
  Submodule.map (Algebra.linearMap K[X] (RatFunc K)) (Polynomial.degreeLT K m)

theorem mem_polySpace {m : ℕ} {f : RatFunc K} :
    f ∈ polySpace K m ↔ ∃ a : K[X], a.degree < (m : ℕ) ∧ f = algebraMap K[X] (RatFunc K) a := by
  constructor
  · rintro ⟨a, ha, rfl⟩
    exact ⟨a, (Polynomial.mem_degreeLT).1 ha, rfl⟩
  · rintro ⟨a, ha, rfl⟩
    exact ⟨a, (Polynomial.mem_degreeLT).2 ha, rfl⟩

theorem finrank_polySpace (m : ℕ) : Module.finrank K (polySpace K m) = m := by
  have hinj : Function.Injective (Algebra.linearMap K[X] (RatFunc K)) := by
    intro a b hab
    exact RatFunc.algebraMap_injective K (by simpa using hab)
  have e : (Polynomial.degreeLT K m) ≃ₗ[K] (polySpace K m) :=
    Submodule.equivMapOfInjective _ hinj _
  rw [← e.finrank_eq, (Polynomial.degreeLTEquiv K m).finrank_eq, Module.finrank_fin_fun]

/-- The key structural result: `L(D)` is obtained from the space of polynomials of degree
`≤ deg D` by dividing by the function `divFun D`. -/
theorem riemannRochSpace_eq_map (D : Divisor K) :
    riemannRochSpace D
      = Submodule.map (LinearMap.mulRight K (divFun D)⁻¹) (polySpace K (deg D + 1).toNat) := by
  classical
  set h : RatFunc K := divFun D with hh
  have hne : h ≠ 0 := divFun_ne_zero D
  ext f
  simp only [Submodule.mem_map, LinearMap.mulRight_apply, mem_polySpace, mem_riemannRochSpace]
  constructor
  · rintro (rfl | hf)
    · exact ⟨0, ⟨0, by simp, by simp⟩, by simp⟩
    rcases eq_or_ne f 0 with rfl | hf0
    · exact ⟨0, ⟨0, by simp, by simp⟩, by simp⟩
    · -- `g = f * h` is a polynomial of degree `≤ deg D`
      have hfh : f * h ≠ 0 := mul_ne_zero hf0 hne
      have hordfin : ∀ p : FinitePlace K, 0 ≤ ord (some p) (f * h) := by
        intro p
        rw [ord_mul _ hf0 hne, ord_divFun_finite]
        have := hf (some p)
        omega
      obtain ⟨a, ha⟩ := isPolynomial_of_ord_nonneg hfh hordfin
      have ha0 : a ≠ 0 := by
        intro h0
        rw [h0] at ha
        simp at ha
        exact hfh ha
      have hordinf : ord (none : Place K) (f * h) = ord (none : Place K) f + (D none - deg D) := by
        rw [ord_mul _ hf0 hne, ord_divFun_infty]
      have hdegle : (a.natDegree : ℤ) ≤ deg D := by
        have h1 := hf none
        have h2 : ord (none : Place K) (f * h) = -(a.natDegree : ℤ) := by
          rw [ha, ord_polynomial_infty]
        omega
      refine ⟨f * h, ⟨a, ?_, ha⟩, ?_⟩
      · rw [Polynomial.degree_eq_natDegree ha0]
        have : (a.natDegree : ℤ) < (deg D + 1).toNat := by omega
        exact_mod_cast this
      · field_simp
  · rintro ⟨g, ⟨a, hadeg, rfl⟩, rfl⟩
    rcases eq_or_ne a 0 with rfl | ha0
    · left; simp
    right
    intro v
    have hane : (algebraMap K[X] (RatFunc K) a) ≠ 0 := RatFunc.algebraMap_ne_zero ha0
    have hordv : ord v (algebraMap K[X] (RatFunc K) a * h⁻¹)
        = ord v (algebraMap K[X] (RatFunc K) a) - ord v h := by
      rw [ord_mul v hane (inv_ne_zero hne), ord_inv]
      ring
    have hdeg : (a.natDegree : ℤ) ≤ deg D := by
      have h1 : a.degree = (a.natDegree : ℕ) := Polynomial.degree_eq_natDegree ha0
      rw [h1] at hadeg
      have : a.natDegree < (deg D + 1).toNat := by exact_mod_cast hadeg
      omega
    cases v with
    | none =>
      rw [hordv, ord_polynomial_infty, ord_divFun_infty]
      omega
    | some p =>
      rw [hordv, ord_polynomial_finite, ord_divFun_finite]
      have := mult_nonneg p a
      omega

/-- The dimension of the Riemann–Roch space of `D` on `ℙ¹_K`. -/
theorem ell_eq (D : Divisor K) : (ell D : ℤ) = max (deg D + 1) 0 := by
  have hne : divFun D ≠ 0 := divFun_ne_zero D
  have hinj : Function.Injective (LinearMap.mulRight K (divFun D)⁻¹) := by
    intro x y hxy
    simp only [LinearMap.mulRight_apply] at hxy
    exact mul_right_cancel₀ (inv_ne_zero hne) hxy
  have e : (polySpace K (deg D + 1).toNat) ≃ₗ[K]
      (Submodule.map (LinearMap.mulRight K (divFun D)⁻¹) (polySpace K (deg D + 1).toNat)) :=
    Submodule.equivMapOfInjective _ hinj _
  have : ell D = (deg D + 1).toNat := by
    rw [ell, riemannRochSpace_eq_map D, ← e.finrank_eq, finrank_polySpace]
  rw [this]
  omega

end Math2

end

import Mathlib

/-!
# Places and orders of vanishing on the projective line

This file develops the elementary valuation theory of the rational function field `K(x)`,
i.e. of the smooth projective curve `ℙ¹_K`:

* `Math2.FinitePlace K` : the finite (closed) points of `ℙ¹_K`, i.e. the monic irreducible
  polynomials of `K[X]`;
* `Math2.Place K` : all closed points, i.e. the finite ones together with the point at
  infinity (`none`);
* `Math2.ord v f` : the order of vanishing of a rational function `f` at the place `v`.
-/

open Polynomial

noncomputable section

namespace Math2

variable {K : Type*} [Field K]

/-- The finite closed points of the projective line over `K`, i.e. the monic irreducible
polynomials over `K`. -/
abbrev FinitePlace (K : Type*) [Field K] : Type _ := {p : K[X] // p.Monic ∧ Irreducible p}

/-- The closed points of the projective line over `K`: the finite places together with the
point at infinity, denoted `none`. -/
abbrev Place (K : Type*) [Field K] : Type _ := Option (FinitePlace K)

namespace FinitePlace

theorem ne_zero (p : FinitePlace K) : (p : K[X]) ≠ 0 := p.2.1.ne_zero

theorem prime (p : FinitePlace K) : Prime (p : K[X]) :=
  (UniqueFactorizationMonoid.irreducible_iff_prime).1 p.2.2

theorem not_isUnit (p : FinitePlace K) : ¬ IsUnit (p : K[X]) := p.2.2.not_isUnit

@[ext] theorem ext {p q : FinitePlace K} (h : (p : K[X]) = q) : p = q := Subtype.ext h

end FinitePlace

open scoped Classical in
/-- The multiplicity of the monic irreducible `p` in a polynomial, as an integer
(with the convention that it is `0` at the zero polynomial). -/
def mult (p : FinitePlace K) (a : K[X]) : ℤ :=
  if a = 0 then 0 else (multiplicity (p : K[X]) a : ℤ)

theorem finiteMultiplicity_of_ne_zero (p : FinitePlace K) {a : K[X]} (ha : a ≠ 0) :
    FiniteMultiplicity (p : K[X]) a :=
  FiniteMultiplicity.of_prime_left p.prime ha

theorem mult_of_ne_zero (p : FinitePlace K) {a : K[X]} (ha : a ≠ 0) :
    mult p a = (multiplicity (p : K[X]) a : ℤ) := if_neg ha

@[simp] theorem mult_zero (p : FinitePlace K) : mult p 0 = 0 := if_pos rfl

theorem mult_nonneg (p : FinitePlace K) (a : K[X]) : 0 ≤ mult p a := by
  unfold mult
  split <;> simp

theorem mult_mul (p : FinitePlace K) {a b : K[X]} (ha : a ≠ 0) (hb : b ≠ 0) :
    mult p (a * b) = mult p a + mult p b := by
  have hfin : FiniteMultiplicity (p : K[X]) (a * b) :=
    finiteMultiplicity_of_ne_zero p (mul_ne_zero ha hb)
  rw [mult_of_ne_zero p (mul_ne_zero ha hb), mult_of_ne_zero p ha, mult_of_ne_zero p hb,
    multiplicity_mul p.prime hfin]
  push_cast
  ring

@[simp] theorem mult_one (p : FinitePlace K) : mult p 1 = 0 := by
  rw [mult_of_ne_zero p one_ne_zero, multiplicity_of_one_right p.not_isUnit]
  simp

theorem mult_C (p : FinitePlace K) (c : K) : mult p (Polynomial.C c) = 0 := by
  rcases eq_or_ne c 0 with rfl | hc
  · simp
  · have hu : IsUnit (Polynomial.C c) := isUnit_C.2 hc.isUnit
    rw [mult_of_ne_zero p (by simpa using hc), multiplicity_of_isUnit_right p.not_isUnit hu]
    simp

theorem min_le_mult_add (p : FinitePlace K) {a b : K[X]} (hab : a + b ≠ 0) :
    min (mult p a) (mult p b) ≤ mult p (a + b) := by
  rcases eq_or_ne a 0 with rfl | ha
  · simp
  rcases eq_or_ne b 0 with rfl | hb
  · simp
  have h := @min_le_emultiplicity_add _ _ (p : K[X]) a b
  rw [(finiteMultiplicity_of_ne_zero p ha).emultiplicity_eq_multiplicity,
    (finiteMultiplicity_of_ne_zero p hb).emultiplicity_eq_multiplicity,
    (finiteMultiplicity_of_ne_zero p hab).emultiplicity_eq_multiplicity] at h
  have h' : min (multiplicity (p : K[X]) a) (multiplicity (p : K[X]) b)
      ≤ multiplicity (p : K[X]) (a + b) := by
    have : ((min (multiplicity (p : K[X]) a) (multiplicity (p : K[X]) b) : ℕ) : ℕ∞)
        ≤ ((multiplicity (p : K[X]) (a + b) : ℕ) : ℕ∞) := by
      simpa [Nat.cast_min] using h
    exact_mod_cast this
  rw [mult_of_ne_zero p ha, mult_of_ne_zero p hb, mult_of_ne_zero p hab]
  exact_mod_cast h'

theorem mult_eq_zero_of_ne (p q : FinitePlace K) (h : p ≠ q) : mult p (q : K[X]) = 0 := by
  rw [mult_of_ne_zero p q.ne_zero]
  simp only [Nat.cast_eq_zero]
  refine multiplicity_eq_zero.2 fun hdvd => h (FinitePlace.ext ?_)
  exact Polynomial.eq_of_monic_of_associated p.2.1 q.2.1 (p.2.2.associated_of_dvd q.2.2 hdvd)

@[simp] theorem mult_self (p : FinitePlace K) : mult p (p : K[X]) = 1 := by
  have h := multiplicity_pow_self_of_prime p.prime 1
  rw [pow_one] at h
  rw [mult_of_ne_zero p p.ne_zero, h]
  simp

/-- The order of vanishing of a rational function at a place of `ℙ¹_K`.  At a finite place `p`
this is the multiplicity of `p` in the numerator minus that in the denominator; at the place at
infinity it is minus the degree.  By convention the order of `0` is `0`; the zero function is
treated separately everywhere. -/
def ord : Place K → RatFunc K → ℤ
  | none, f => -f.intDegree
  | some p, f => mult p f.num - mult p f.denom

@[simp] theorem ord_infty (f : RatFunc K) : ord (none : Place K) f = -f.intDegree := rfl

@[simp] theorem ord_finite (p : FinitePlace K) (f : RatFunc K) :
    ord (some p) f = mult p f.num - mult p f.denom := rfl

@[simp] theorem ord_zero (v : Place K) : ord v (0 : RatFunc K) = 0 := by
  cases v with
  | none => simp
  | some p => simp

/-- The order of vanishing computed from an arbitrary representation as a quotient. -/
theorem ord_finite_div (p : FinitePlace K) {a b : K[X]} (ha : a ≠ 0) (hb : b ≠ 0) :
    ord (some p) (algebraMap K[X] (RatFunc K) a / algebraMap K[X] (RatFunc K) b)
      = mult p a - mult p b := by
  set f : RatFunc K := algebraMap K[X] (RatFunc K) a / algebraMap K[X] (RatFunc K) b with hf
  have hfne : f ≠ 0 :=
    div_ne_zero (RatFunc.algebraMap_ne_zero ha) (RatFunc.algebraMap_ne_zero hb)
  have key : f.num * b = a * f.denom := (RatFunc.num_mul_eq_mul_denom_iff hb).2 hf
  have hnum : f.num ≠ 0 := RatFunc.num_ne_zero hfne
  have hden : f.denom ≠ 0 := RatFunc.denom_ne_zero f
  have hmul := congrArg (mult p) key
  rw [mult_mul p hnum hb, mult_mul p ha hden] at hmul
  simp only [ord_finite]
  omega

theorem ord_polynomial_finite (p : FinitePlace K) (a : K[X]) :
    ord (some p) (algebraMap K[X] (RatFunc K) a) = mult p a := by
  simp [ord_finite]

theorem ord_polynomial_infty (a : K[X]) :
    ord (none : Place K) (algebraMap K[X] (RatFunc K) a) = -(a.natDegree : ℤ) := by
  simp [ord_infty]

@[simp] theorem ord_one (v : Place K) : ord v (1 : RatFunc K) = 0 := by
  cases v with
  | none => simp
  | some p => simp

theorem ord_C (v : Place K) (c : K) : ord v (RatFunc.C c) = 0 := by
  cases v with
  | none => simp
  | some p => simp [RatFunc.num_C, RatFunc.denom_C, mult_C]

theorem ord_mul (v : Place K) {f g : RatFunc K} (hf : f ≠ 0) (hg : g ≠ 0) :
    ord v (f * g) = ord v f + ord v g := by
  cases v with
  | none =>
    simp only [ord_infty, RatFunc.intDegree_mul hf hg]
    ring
  | some p =>
    have hfn := RatFunc.num_ne_zero hf
    have hgn := RatFunc.num_ne_zero hg
    have hfd := RatFunc.denom_ne_zero f
    have hgd := RatFunc.denom_ne_zero g
    have hprod : f * g = algebraMap K[X] (RatFunc K) (f.num * g.num)
        / algebraMap K[X] (RatFunc K) (f.denom * g.denom) := by
      rw [map_mul, map_mul, ← div_mul_div_comm, RatFunc.num_div_denom, RatFunc.num_div_denom]
    rw [hprod, ord_finite_div p (mul_ne_zero hfn hgn) (mul_ne_zero hfd hgd),
      mult_mul p hfn hgn, mult_mul p hfd hgd]
    simp only [ord_finite]
    ring

theorem ord_inv (v : Place K) (f : RatFunc K) : ord v f⁻¹ = -ord v f := by
  rcases eq_or_ne f 0 with rfl | hf
  · simp
  · have h : ord v (f * f⁻¹) = ord v f + ord v f⁻¹ := ord_mul v hf (inv_ne_zero hf)
    rw [mul_inv_cancel₀ hf, ord_one] at h
    omega

theorem ord_pow (v : Place K) {f : RatFunc K} (hf : f ≠ 0) (n : ℕ) :
    ord v (f ^ n) = n * ord v f := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [pow_succ, ord_mul v (pow_ne_zero n hf) hf, ih]
    push_cast
    ring

theorem ord_zpow (v : Place K) {f : RatFunc K} (hf : f ≠ 0) (n : ℤ) :
    ord v (f ^ n) = n * ord v f := by
  rcases n with n | n
  · simpa using ord_pow v hf n
  · rw [zpow_negSucc, ord_inv, ord_pow v hf (n + 1), Int.negSucc_eq]
    push_cast
    ring

theorem ord_prod {ι : Type*} (v : Place K) (s : Finset ι) (f : ι → RatFunc K)
    (hf : ∀ i ∈ s, f i ≠ 0) : ord v (∏ i ∈ s, f i) = ∑ i ∈ s, ord v (f i) := by
  classical
  induction s using Finset.induction with
  | empty => simp
  | insert a s ha ih =>
    have hprod : (∏ i ∈ s, f i) ≠ 0 :=
      Finset.prod_ne_zero_iff.2 fun i hi => hf i (Finset.mem_insert_of_mem hi)
    rw [Finset.prod_insert ha, Finset.sum_insert ha,
      ord_mul v (hf a (Finset.mem_insert_self a s)) hprod,
      ih fun i hi => hf i (Finset.mem_insert_of_mem hi)]

theorem min_le_ord_add (v : Place K) {f g : RatFunc K} (hf : f ≠ 0) (hg : g ≠ 0)
    (hfg : f + g ≠ 0) : min (ord v f) (ord v g) ≤ ord v (f + g) := by
  cases v with
  | none =>
    have h := RatFunc.intDegree_add_le hg hfg
    simp only [ord_infty]
    omega
  | some p =>
    have hfn := RatFunc.num_ne_zero hf
    have hgn := RatFunc.num_ne_zero hg
    have hfd := RatFunc.denom_ne_zero f
    have hgd := RatFunc.denom_ne_zero g
    have hsum : f + g = algebraMap K[X] (RatFunc K) (f.num * g.denom + f.denom * g.num)
        / algebraMap K[X] (RatFunc K) (f.denom * g.denom) := by
      conv_lhs => rw [← RatFunc.num_div_denom f, ← RatFunc.num_div_denom g]
      rw [div_add_div _ _ (RatFunc.algebraMap_ne_zero hfd) (RatFunc.algebraMap_ne_zero hgd),
        map_add, map_mul, map_mul, map_mul]
    have hnum_ne : f.num * g.denom + f.denom * g.num ≠ 0 := by
      intro h
      apply hfg
      rw [hsum, h]
      simp
    rw [hsum, ord_finite_div p hnum_ne (mul_ne_zero hfd hgd)]
    have h1 : mult p (f.num * g.denom) = mult p f.num + mult p g.denom := mult_mul p hfn hgd
    have h2 : mult p (f.denom * g.num) = mult p f.denom + mult p g.num := mult_mul p hfd hgn
    have h3 := min_le_mult_add p hnum_ne
    have h4 : mult p (f.denom * g.denom) = mult p f.denom + mult p g.denom := mult_mul p hfd hgd
    simp only [ord_finite]
    rw [h1, h2] at h3
    omega

/-- A nonzero rational function all of whose orders at finite places are nonnegative is a
polynomial. -/
theorem isPolynomial_of_ord_nonneg {f : RatFunc K} (hf : f ≠ 0)
    (h : ∀ p : FinitePlace K, 0 ≤ ord (some p) f) :
    ∃ a : K[X], f = algebraMap K[X] (RatFunc K) a := by
  have hden : f.denom ≠ 0 := RatFunc.denom_ne_zero f
  by_cases hu : IsUnit f.denom
  · refine ⟨f.num, ?_⟩
    have h1 : f.denom = 1 := (RatFunc.monic_denom f).eq_one_of_isUnit hu
    conv_lhs => rw [← RatFunc.num_div_denom f]
    rw [h1]
    simp
  · exfalso
    obtain ⟨r, hr, hrdvd⟩ := WfDvdMonoid.exists_irreducible_factor hu hden
    have hr0 : r ≠ 0 := hr.ne_zero
    set p : K[X] := r * Polynomial.C r.leadingCoeff⁻¹ with hp
    have hpm : p.Monic := Polynomial.monic_mul_leadingCoeff_inv hr0
    have hassoc : Associated r p := by
      have hcu : IsUnit (Polynomial.C r.leadingCoeff⁻¹) :=
        isUnit_C.2 (isUnit_iff_ne_zero.2 (by
          simpa [inv_eq_zero, Polynomial.leadingCoeff_eq_zero] using hr0))
      obtain ⟨u, hu'⟩ := hcu
      exact ⟨u, by rw [hu', hp]⟩
    have hpi : Irreducible p := hassoc.irreducible hr
    have hpdvd : p ∣ f.denom := (hassoc.dvd_iff_dvd_left).1 hrdvd
    have hP := h ⟨p, hpm, hpi⟩
    have h1 : 1 ≤ mult ⟨p, hpm, hpi⟩ f.denom := by
      have hpos : 0 < multiplicity p f.denom := multiplicity_pos_of_dvd hpdvd
      rw [mult_of_ne_zero _ hden]
      exact_mod_cast hpos
    have h2 : mult ⟨p, hpm, hpi⟩ f.num = 0 := by
      rw [mult_of_ne_zero _ (RatFunc.num_ne_zero hf)]
      simp only [Nat.cast_eq_zero]
      refine multiplicity_eq_zero.2 fun hdvd => ?_
      exact hpi.not_isUnit ((RatFunc.isCoprime_num_denom f).isUnit_of_dvd' hdvd hpdvd)
    rw [ord_finite] at hP
    omega

end Math2

end

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

