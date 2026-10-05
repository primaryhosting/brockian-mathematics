/-
# Riemann Roch Curve
Category: Frontier Math
Target: Math2.riemann_roch_curve
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/
import Mathlib

/-!
# Riemann Roch Curve
Category: Frontier Math
Target: Math2.riemann_roch_curve
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)

## Contents

This file develops, from scratch, the divisor theory of the smooth projective curve `ℙ¹`
over an arbitrary field `k`, through its function field `k(X) = RatFunc k`, and proves the
Riemann–Roch theorem for it:

  `ℓ(D) - ℓ(K - D) = deg D + 1 - g`.

Nothing is assumed: all of the following are defined here and all statements are proved.

* `Place k`: the closed points of `ℙ¹`, namely the monic irreducible polynomials
  (finite points) together with the point at infinity.
* `placeDeg`, `Divisor k`, `degDiv`: degrees of points, divisors and their degrees.
* `ord v f`: the order of vanishing of a rational function at a closed point, and
  `divisorOf f` the principal divisor of `f`.
* `RRSpace D` (`= L(D)`) and `ell D` (`= ℓ(D) = dim_k L(D)`).
* `canonicalDivisor k = -2·[∞]`, the divisor of the differential `dX`, and
  `genus k = ℓ(K)`, the dimension of the space of regular differentials.

The main results are `Math2.riemann_roch_curve`, together with `Math2.ell_eq`
(`ℓ(D) = max (deg D + 1) 0`), `Math2.genus_eq_zero` (`ℙ¹` has genus `0`),
`Math2.degDiv_canonical_eq` (`deg K = 2g - 2`) and `Math2.degDiv_divisorOf` (a principal
divisor has degree `0`).

The scope is the projective line: Mathlib has no theory of divisors, linear systems or
Serre duality for general curves, so the curve treated here is `ℙ¹`, for which the whole
theory is built by hand.
-/

namespace Math2

open Polynomial UniqueFactorizationMonoid

variable {k : Type*} [Field k]

/-- A finite closed point of the projective line `ℙ¹` over `k`: a monic irreducible
polynomial in `k[X]`. -/
abbrev FinPlace (k : Type*) [Field k] : Type _ := {p : k[X] // p.Monic ∧ Irreducible p}

/-- The closed points of `ℙ¹` over `k`: the finite places together with the point at
infinity, represented by `none`. -/
abbrev Place (k : Type*) [Field k] : Type _ := Option (FinPlace k)

/-- The degree of a closed point: `1` at infinity, `deg p` at a finite place `p`. -/
def placeDeg : Place k → ℤ
  | none => 1
  | some p => (p.1.natDegree : ℤ)

/-- Divisors on `ℙ¹`: finitely supported formal `ℤ`-combinations of closed points. -/
abbrev Divisor (k : Type*) [Field k] := Place k →₀ ℤ

/-- The degree of a divisor. -/
noncomputable def degDiv (D : Divisor k) : ℤ := D.sum fun v n => n * placeDeg v

/-- The order of vanishing of a nonzero polynomial at a place: the multiplicity of the
irreducible `p` at a finite place, and `-deg a` at infinity. -/
noncomputable def polOrd : Place k → k[X] → ℤ
  | none, a => -(a.natDegree : ℤ)
  | some p, a => (multiplicity p.1 a : ℤ)

/-- The order of vanishing of a rational function at a closed point of `ℙ¹`. -/
noncomputable def ord (v : Place k) (f : RatFunc k) : ℤ := polOrd v f.num - polOrd v f.denom

lemma FinPlace.prime (p : FinPlace k) : Prime p.1 := p.2.2.prime

lemma algMap_ne_zero {b : k[X]} (hb : b ≠ 0) : (algebraMap k[X] (RatFunc k)) b ≠ 0 :=
  fun h => hb (RatFunc.algebraMap_injective k (by rw [h, map_zero]))

lemma polOrd_mul {a b : k[X]} (ha : a ≠ 0) (hb : b ≠ 0) (v : Place k) :
    polOrd v (a * b) = polOrd v a + polOrd v b := by
  cases v with
  | none => simp only [polOrd, Polynomial.natDegree_mul ha hb]; push_cast; ring
  | some p =>
    simp only [polOrd]
    rw [multiplicity_mul p.prime (FiniteMultiplicity.of_prime_left p.prime (mul_ne_zero ha hb))]
    push_cast; ring

lemma polOrd_one (v : Place k) : polOrd v (1 : k[X]) = 0 := by
  cases v with
  | none => simp [polOrd]
  | some p =>
    simp [polOrd, multiplicity_eq_zero.2 (fun h => p.2.2.not_isUnit (isUnit_of_dvd_one h))]

lemma polOrd_C {c : k} (hc : c ≠ 0) (v : Place k) : polOrd v (C c) = 0 := by
  have hu : IsUnit (C c : k[X]) := isUnit_C.2 hc.isUnit
  cases v with
  | none => simp [polOrd]
  | some p =>
    simp [polOrd, multiplicity_eq_zero.2 (fun h => p.2.2.not_isUnit (isUnit_of_dvd_unit h hu))]

/-- The ultrametric inequality for `polOrd`. -/
lemma polOrd_add_ge {x y : k[X]} (hxy : x + y ≠ 0) (v : Place k) :
    min (polOrd v x) (polOrd v y) ≤ polOrd v (x + y) := by
  cases v with
  | none =>
    simp only [polOrd, min_le_iff, neg_le_neg_iff]
    have := Polynomial.natDegree_add_le x y
    rcases le_total x.natDegree y.natDegree with h | h
    · right; exact_mod_cast le_trans (by exact_mod_cast this) (by simpa using h)
    · left; exact_mod_cast le_trans (by exact_mod_cast this) (by simpa using h)
  | some p =>
    simp only [polOrd, ← Nat.cast_min, Nat.cast_le]
    have hdx : p.1 ^ (min (multiplicity p.1 x) (multiplicity p.1 y)) ∣ x :=
      dvd_trans (pow_dvd_pow _ (min_le_left _ _)) (pow_multiplicity_dvd _ _)
    have hdy : p.1 ^ (min (multiplicity p.1 x) (multiplicity p.1 y)) ∣ y :=
      dvd_trans (pow_dvd_pow _ (min_le_right _ _)) (pow_multiplicity_dvd _ _)
    exact (FiniteMultiplicity.of_prime_left p.prime hxy).pow_dvd_iff_le_multiplicity.mp
      (dvd_add hdx hdy)

/-- `ord` may be computed from any representation of `f` as a quotient of polynomials. -/
lemma ord_eq {a b : k[X]} (ha : a ≠ 0) (hb : b ≠ 0) (v : Place k) :
    ord v ((algebraMap k[X] (RatFunc k) a) / (algebraMap k[X] (RatFunc k) b))
      = polOrd v a - polOrd v b := by
  set f : RatFunc k := (algebraMap k[X] (RatFunc k) a) / (algebraMap k[X] (RatFunc k) b) with hf
  have hb' := algMap_ne_zero hb
  have hd := algMap_ne_zero (RatFunc.denom_ne_zero f)
  have hfne : f ≠ 0 := div_ne_zero (algMap_ne_zero ha) hb'
  have key : f.num * b = a * f.denom := by
    have h1 : (algebraMap k[X] (RatFunc k)) f.num / (algebraMap k[X] (RatFunc k)) f.denom
        = (algebraMap k[X] (RatFunc k)) a / (algebraMap k[X] (RatFunc k)) b :=
      RatFunc.num_div_denom f
    rw [div_eq_div_iff hd hb'] at h1
    exact RatFunc.algebraMap_injective k (by rw [map_mul, map_mul]; exact h1)
  have hnum : f.num ≠ 0 := RatFunc.num_ne_zero hfne
  have h2 := polOrd_mul hnum hb v
  rw [key, polOrd_mul ha (RatFunc.denom_ne_zero f) v] at h2
  simp only [ord]
  omega

lemma ord_algebraMap {a : k[X]} (ha : a ≠ 0) (v : Place k) :
    ord v (algebraMap k[X] (RatFunc k) a) = polOrd v a := by
  have := ord_eq ha (one_ne_zero (α := k[X])) v
  simpa [polOrd_one] using this

lemma ord_one (v : Place k) : ord v (1 : RatFunc k) = 0 := by
  have := ord_algebraMap (one_ne_zero (α := k[X])) v
  simpa [polOrd_one] using this

lemma ord_mul {f g : RatFunc k} (hf : f ≠ 0) (hg : g ≠ 0) (v : Place k) :
    ord v (f * g) = ord v f + ord v g := by
  have hfg : f * g = (algebraMap k[X] (RatFunc k) (f.num * g.num))
      / (algebraMap k[X] (RatFunc k) (f.denom * g.denom)) := by
    rw [map_mul, map_mul, ← div_mul_div_comm, RatFunc.num_div_denom, RatFunc.num_div_denom]
  rw [hfg, ord_eq (mul_ne_zero (RatFunc.num_ne_zero hf) (RatFunc.num_ne_zero hg))
      (mul_ne_zero (RatFunc.denom_ne_zero f) (RatFunc.denom_ne_zero g)) v,
    polOrd_mul (RatFunc.num_ne_zero hf) (RatFunc.num_ne_zero hg),
    polOrd_mul (RatFunc.denom_ne_zero f) (RatFunc.denom_ne_zero g)]
  simp only [ord]; ring

lemma ord_inv {f : RatFunc k} (hf : f ≠ 0) (v : Place k) : ord v f⁻¹ = -ord v f := by
  have h := ord_mul hf (inv_ne_zero hf) v
  rw [mul_inv_cancel₀ hf, ord_one] at h
  omega

lemma ord_zpow {f : RatFunc k} (hf : f ≠ 0) (n : ℤ) (v : Place k) :
    ord v (f ^ n) = n * ord v f := by
  induction n using Int.induction_on with
  | zero => simpa using ord_one v
  | succ i ih =>
    have : f ^ ((i : ℤ) + 1) = f ^ (i : ℤ) * f := by rw [zpow_add₀ hf]; simp
    rw [this, ord_mul (zpow_ne_zero _ hf) hf, ih]; ring
  | pred i ih =>
    have : f ^ (-(i : ℤ) - 1) = f ^ (-(i : ℤ)) * f⁻¹ := by
      rw [sub_eq_add_neg, zpow_add₀ hf]; simp
    rw [this, ord_mul (zpow_ne_zero _ hf) (inv_ne_zero hf), ord_inv hf, ih]; ring

lemma ord_smul {c : k} (hc : c ≠ 0) {f : RatFunc k} (hf : f ≠ 0) (v : Place k) :
    ord v (c • f) = ord v f := by
  rw [RatFunc.smul_eq_C_mul, ← RatFunc.algebraMap_C,
    ord_mul (algMap_ne_zero (by simpa using hc)) hf, ord_algebraMap (by simpa using hc) v,
    polOrd_C hc]
  ring

/-- The ultrametric inequality for `ord`. -/
lemma ord_add_ge {f g : RatFunc k} (hf : f ≠ 0) (hg : g ≠ 0) (hfg : f + g ≠ 0) (v : Place k) :
    min (ord v f) (ord v g) ≤ ord v (f + g) := by
  set a : k[X] := f.num * g.denom + g.num * f.denom with ha
  have hden : f.denom * g.denom ≠ 0 :=
    mul_ne_zero (RatFunc.denom_ne_zero f) (RatFunc.denom_ne_zero g)
  have hrep : f + g = (algebraMap k[X] (RatFunc k) a)
      / (algebraMap k[X] (RatFunc k) (f.denom * g.denom)) := by
    have h1 := algMap_ne_zero (RatFunc.denom_ne_zero f)
    have h2 := algMap_ne_zero (RatFunc.denom_ne_zero g)
    rw [ha, map_add, map_mul, map_mul, map_mul, eq_div_iff (mul_ne_zero h1 h2)]
    nth_rewrite 1 [← RatFunc.num_div_denom f, ← RatFunc.num_div_denom g]
    field_simp
  have hane : a ≠ 0 := by
    intro h
    apply hfg
    rw [hrep, h, map_zero, zero_div]
  rw [hrep, ord_eq hane hden v]
  have h1 : polOrd v (f.num * g.denom) = polOrd v f.num + polOrd v g.denom :=
    polOrd_mul (RatFunc.num_ne_zero hf) (RatFunc.denom_ne_zero g) v
  have h2 : polOrd v (g.num * f.denom) = polOrd v g.num + polOrd v f.denom :=
    polOrd_mul (RatFunc.num_ne_zero hg) (RatFunc.denom_ne_zero f) v
  have h3 : polOrd v (f.denom * g.denom) = polOrd v f.denom + polOrd v g.denom :=
    polOrd_mul (RatFunc.denom_ne_zero f) (RatFunc.denom_ne_zero g) v
  have h4 := polOrd_add_ge (x := f.num * g.denom) (y := g.num * f.denom) (by rwa [← ha]) v
  rw [← ha] at h4
  simp only [ord]
  rw [h3]
  rw [h1, h2] at h4
  omega

/-- A nonzero rational function has nonzero order at only finitely many places. -/
lemma ord_support_finite {f : RatFunc k} (hf : f ≠ 0) :
    (Function.support fun v : Place k => ord v f).Finite := by
  classical
  have hane : f.num * f.denom ≠ 0 :=
    mul_ne_zero (RatFunc.num_ne_zero hf) (RatFunc.denom_ne_zero f)
  have hSfin : {p : FinPlace k | ord (some p) f ≠ 0}.Finite := by
    apply Set.Finite.of_finite_image (f := (Subtype.val : FinPlace k → k[X]))
      _ (Set.injOn_of_injective Subtype.val_injective)
    apply Set.Finite.subset
      ((normalizedFactors (f.num * f.denom)).toFinset : Finset k[X]).finite_toSet
    rintro x ⟨p, hp, rfl⟩
    have hdvd : p.1 ∣ f.num * f.denom := by
      by_contra hnd
      have h1 : ¬ p.1 ∣ f.num := fun h => hnd (h.mul_right _)
      have h2 : ¬ p.1 ∣ f.denom := fun h => hnd (h.mul_left _)
      exact hp (by simp [ord, polOrd, multiplicity_eq_zero.2 h1, multiplicity_eq_zero.2 h2])
    have : p.1 ∈ normalizedFactors (f.num * f.denom) :=
      (mem_normalizedFactors_iff' hane).2 ⟨p.2.2, p.2.1.normalize_eq_self, hdvd⟩
    simpa using this
  apply Set.Finite.subset ((hSfin.image some).insert none)
  rintro (_ | p) hv
  · exact Set.mem_insert _ _
  · exact Set.mem_insert_of_mem _ ⟨p, hv, rfl⟩

/-- The principal divisor of a nonzero rational function (and `0` for `f = 0`). -/
noncomputable def divisorOf (f : RatFunc k) : Divisor k := by
  classical
  exact if hf : f = 0 then 0 else Finsupp.ofSupportFinite _ (ord_support_finite hf)

@[simp] lemma divisorOf_apply {f : RatFunc k} (hf : f ≠ 0) (v : Place k) :
    divisorOf f v = ord v f := by
  classical
  rw [divisorOf, dif_neg hf]
  rfl

lemma divisorOf_one : divisorOf (1 : RatFunc k) = 0 := by
  ext v
  rw [divisorOf_apply (one_ne_zero' (RatFunc k)), ord_one]
  simp

lemma divisorOf_mul {f g : RatFunc k} (hf : f ≠ 0) (hg : g ≠ 0) :
    divisorOf (f * g) = divisorOf f + divisorOf g := by
  ext v
  rw [Finsupp.add_apply, divisorOf_apply (mul_ne_zero hf hg), divisorOf_apply hf,
    divisorOf_apply hg, ord_mul hf hg]

lemma divisorOf_zpow {f : RatFunc k} (hf : f ≠ 0) (n : ℤ) :
    divisorOf (f ^ n) = n • divisorOf f := by
  ext v
  rw [divisorOf_apply (zpow_ne_zero _ hf), Finsupp.smul_apply, divisorOf_apply hf,
    ord_zpow hf, smul_eq_mul]

/-- The Riemann–Roch space `L(D) = {f : ord_v f ≥ -D(v) for all v} ∪ {0}`. -/
def RRSpace (D : Divisor k) : Submodule k (RatFunc k) where
  carrier := {f | f ≠ 0 → ∀ v : Place k, -(D v) ≤ ord v f}
  add_mem' := by
    rintro f g hf hg hfg v
    rcases eq_or_ne f 0 with rfl | hf0
    · simpa using hg (by simpa using hfg) v
    rcases eq_or_ne g 0 with rfl | hg0
    · simpa using hf (by simpa using hfg) v
    exact le_trans (le_min (hf hf0 v) (hg hg0 v)) (ord_add_ge hf0 hg0 hfg v)
  zero_mem' := by simp
  smul_mem' := by
    rintro c f hf hcf v
    rcases eq_or_ne c 0 with rfl | hc0
    · simp at hcf
    rcases eq_or_ne f 0 with rfl | hf0
    · simp at hcf
    rw [ord_smul hc0 hf0]
    exact hf hf0 v

lemma mem_RRSpace_iff {D : Divisor k} {f : RatFunc k} :
    f ∈ RRSpace D ↔ (f ≠ 0 → ∀ v : Place k, -(D v) ≤ ord v f) := Iff.rfl

/-- `ℓ(D)`, the dimension of the Riemann–Roch space. -/
noncomputable def ell (D : Divisor k) : ℕ := Module.finrank k (RRSpace D)

/-- The canonical divisor of `ℙ¹`, the divisor of the differential `dX`, namely `-2·[∞]`. -/
noncomputable def canonicalDivisor (k : Type*) [Field k] : Divisor k := Finsupp.single none (-2)

/-- The genus, defined intrinsically as `ℓ(K)`, the dimension of the space of regular
differentials. -/
noncomputable def genus (k : Type*) [Field k] : ℕ := ell (canonicalDivisor k)

/-! ### Invariance of `ℓ` under linear equivalence of divisors -/

lemma divisorOf_inv {g : RatFunc k} (hg : g ≠ 0) : divisorOf g⁻¹ = -divisorOf g := by
  ext v
  rw [divisorOf_apply (inv_ne_zero hg), Finsupp.neg_apply, divisorOf_apply hg, ord_inv hg]

lemma mul_mem_RRSpace {D : Divisor k} {f g : RatFunc k} (hg : g ≠ 0) (hf : f ∈ RRSpace D) :
    f * g ∈ RRSpace (D - divisorOf g) := by
  intro hfg v
  have hf0 : f ≠ 0 := by rintro rfl; exact hfg (zero_mul g)
  rw [ord_mul hf0 hg, Finsupp.sub_apply, divisorOf_apply hg]
  have := hf hf0 v
  omega

/-- Multiplication by a nonzero rational function `g` identifies `L(D)` with `L(D - div g)`. -/
noncomputable def RRSpaceMulEquiv (D : Divisor k) {g : RatFunc k} (hg : g ≠ 0) :
    RRSpace D ≃ₗ[k] RRSpace (D - divisorOf g) where
  toFun f := ⟨f.1 * g, mul_mem_RRSpace hg f.2⟩
  map_add' x y := by ext; simp [add_mul]
  map_smul' c x := by ext; simp
  invFun f := ⟨f.1 * g⁻¹, by
    have h := mul_mem_RRSpace (D := D - divisorOf g) (inv_ne_zero hg) f.2
    rwa [divisorOf_inv hg, sub_neg_eq_add, sub_add_cancel] at h⟩
  left_inv f := by
    apply Subtype.ext
    simp [mul_assoc, mul_inv_cancel₀ hg]
  right_inv f := by
    apply Subtype.ext
    simp [mul_assoc, inv_mul_cancel₀ hg]

lemma ell_sub_divisorOf (D : Divisor k) {g : RatFunc k} (hg : g ≠ 0) :
    ell (D - divisorOf g) = ell D := ((RRSpaceMulEquiv D hg).finrank_eq).symm

/-! ### Degrees of divisors -/

@[simp] lemma degDiv_zero : degDiv (0 : Divisor k) = 0 := by simp [degDiv]

lemma degDiv_add (D E : Divisor k) : degDiv (D + E) = degDiv D + degDiv E := by
  simp only [degDiv]
  exact Finsupp.sum_add_index' (by simp) (by intros; ring)

@[simp] lemma degDiv_single (v : Place k) (n : ℤ) :
    degDiv (Finsupp.single v n) = n * placeDeg v := by
  simp only [degDiv]
  exact Finsupp.sum_single_index (by simp)

lemma degDiv_neg (D : Divisor k) : degDiv (-D) = -degDiv D := by
  have h := degDiv_add D (-D)
  rw [add_neg_cancel, degDiv_zero] at h
  omega

lemma degDiv_sub (D E : Divisor k) : degDiv (D - E) = degDiv D - degDiv E := by
  rw [sub_eq_add_neg, degDiv_add, degDiv_neg, sub_eq_add_neg]

/-! ### Every divisor is linearly equivalent to a multiple of the point at infinity -/

lemma multiplicity_finPlace_self (p : FinPlace k) : multiplicity p.1 p.1 = 1 := multiplicity_self

lemma multiplicity_finPlace_ne {p q : FinPlace k} (h : q ≠ p) : multiplicity q.1 p.1 = 0 := by
  refine multiplicity_eq_zero.2 fun hdvd => h ?_
  obtain ⟨c, hc⟩ := hdvd
  rcases p.2.2.isUnit_or_isUnit hc with hu | hu
  · exact absurd hu q.2.2.not_isUnit
  · exact Subtype.ext (Polynomial.eq_of_monic_of_associated q.2.1 p.2.1
      ⟨hu.unit, by rw [IsUnit.unit_spec]; exact hc.symm⟩)

lemma divisorOf_finPlace (p : FinPlace k) :
    divisorOf (algebraMap k[X] (RatFunc k) p.1)
      = (Finsupp.single (some p) 1 : Divisor k)
        - Finsupp.single (none : Place k) (placeDeg (some p)) := by
  have hp0 : p.1 ≠ 0 := p.2.2.ne_zero
  ext v
  rw [divisorOf_apply (algMap_ne_zero hp0), ord_algebraMap hp0, Finsupp.sub_apply]
  cases v with
  | none =>
    rw [Finsupp.single_eq_of_ne (by simp : (none : Place k) ≠ some p), Finsupp.single_eq_same]
    simp [polOrd, placeDeg]
  | some q =>
    rw [Finsupp.single_eq_of_ne (by simp : (some q : Place k) ≠ none)]
    rcases eq_or_ne q p with rfl | h
    · rw [Finsupp.single_eq_same]
      simp [polOrd]
    · rw [Finsupp.single_eq_of_ne (by simpa using h : (some q : Place k) ≠ some p)]
      simp [polOrd, multiplicity_finPlace_ne h]

/-- For every place `v` there is a rational function with divisor `[v] - deg(v)·[∞]`. -/
lemma exists_base (a : Place k) : ∃ h : RatFunc k, h ≠ 0 ∧
    divisorOf h = (Finsupp.single a 1 : Divisor k)
      - Finsupp.single (none : Place k) (placeDeg a) := by
  cases a with
  | none =>
    refine ⟨1, one_ne_zero' (RatFunc k), ?_⟩
    rw [divisorOf_one]
    simp [placeDeg]
  | some p =>
    exact ⟨algebraMap k[X] (RatFunc k) p.1, algMap_ne_zero p.2.2.ne_zero, divisorOf_finPlace p⟩

/-- Every divisor on `ℙ¹` is linearly equivalent to `(deg D)·[∞]`. -/
lemma exists_principal (D : Divisor k) :
    ∃ g : RatFunc k, g ≠ 0 ∧ D - divisorOf g = Finsupp.single none (degDiv D) := by
  induction D using Finsupp.induction with
  | zero => exact ⟨1, one_ne_zero' (RatFunc k), by simp [divisorOf_one]⟩
  | single_add a b F _ _ ih =>
    obtain ⟨g', hg', hF⟩ := ih
    obtain ⟨h, hh, hdh⟩ := exists_base a
    refine ⟨h ^ b * g', mul_ne_zero (zpow_ne_zero _ hh) hg', ?_⟩
    rw [divisorOf_mul (zpow_ne_zero _ hh) hg', divisorOf_zpow hh, hdh, degDiv_add,
      degDiv_single, smul_sub, Finsupp.smul_single, Finsupp.smul_single, smul_eq_mul,
      smul_eq_mul, mul_one]
    have key : Finsupp.single a b + F -
        (Finsupp.single a b - Finsupp.single (none : Place k) (b * placeDeg a) + divisorOf g')
        = (F - divisorOf g') + Finsupp.single (none : Place k) (b * placeDeg a) := by abel
    rw [key, hF, ← Finsupp.single_add, add_comm]

/-! ### The Riemann–Roch space of a multiple of the point at infinity -/

/-- The inclusion of polynomials into rational functions, as a `k`-linear map. -/
noncomputable def polyToRatFunc (k : Type*) [Field k] : k[X] →ₗ[k] RatFunc k :=
  (IsScalarTower.toAlgHom k k[X] (RatFunc k)).toLinearMap

lemma polyToRatFunc_apply (a : k[X]) : polyToRatFunc k a = algebraMap k[X] (RatFunc k) a := rfl

lemma polyToRatFunc_injective : Function.Injective (polyToRatFunc k) :=
  RatFunc.algebraMap_injective k

/-- A rational function with no poles at the finite places is a polynomial. -/
lemma denom_eq_one_of_ord_nonneg {f : RatFunc k} (h : ∀ p : FinPlace k, 0 ≤ ord (some p) f) :
    f.denom = 1 := by
  by_contra hne
  have hu : ¬ IsUnit f.denom := fun hu => hne ((RatFunc.monic_denom f).eq_one_of_isUnit hu)
  obtain ⟨q, hqm, hqi, hqd⟩ := Polynomial.exists_monic_irreducible_factor _ hu
  have h1 : multiplicity q f.num = 0 := multiplicity_eq_zero.2 fun hdvd =>
    hqi.not_isUnit ((RatFunc.isCoprime_num_denom f).isUnit_of_dvd' hdvd hqd)
  have h2 : 1 ≤ multiplicity q f.denom :=
    (FiniteMultiplicity.of_prime_left hqi.prime (RatFunc.denom_ne_zero f)).pow_dvd_iff_le_multiplicity.mp
      (by simpa using hqd)
  have h3 := h ⟨q, hqm, hqi⟩
  simp only [ord, polOrd, h1] at h3
  omega

lemma mem_RRSpace_single_none {n : ℤ} {f : RatFunc k} :
    f ∈ RRSpace (Finsupp.single (none : Place k) n) ↔
      ∃ a : k[X], (a = 0 ∨ (a.natDegree : ℤ) ≤ n) ∧ f = algebraMap k[X] (RatFunc k) a := by
  constructor
  · intro hf
    rcases eq_or_ne f 0 with rfl | hf0
    · exact ⟨0, Or.inl rfl, by simp⟩
    have hden : f.denom = 1 := denom_eq_one_of_ord_nonneg fun p => by
      have := hf hf0 (some p)
      simpa [Finsupp.single_apply] using this
    have hfa : f = algebraMap k[X] (RatFunc k) f.num := by
      conv_lhs => rw [← RatFunc.num_div_denom f]
      rw [hden, map_one, div_one]
    refine ⟨f.num, Or.inr ?_, hfa⟩
    have := hf hf0 none
    simp only [ord, polOrd, hden, Finsupp.single_eq_same] at this
    simpa using this
  · rintro ⟨a, ha, rfl⟩
    intro hne v
    have ha0 : a ≠ 0 := by
      rintro rfl; exact hne (by simp)
    rw [ord_algebraMap ha0]
    cases v with
    | none =>
      rcases ha with rfl | ha
      · exact absurd rfl ha0
      · simpa [polOrd] using ha
    | some p => simp [polOrd]

lemma RRSpace_single_none (n : ℤ) :
    RRSpace (Finsupp.single (none : Place k) n)
      = Submodule.map (polyToRatFunc k) (Polynomial.degreeLT k (n + 1).toNat) := by
  ext f
  rw [mem_RRSpace_single_none, Submodule.mem_map]
  constructor
  · rintro ⟨a, ha, rfl⟩
    refine ⟨a, ?_, rfl⟩
    rcases ha with rfl | ha
    · exact Submodule.zero_mem _
    rcases eq_or_ne a 0 with rfl | ha0
    · exact Submodule.zero_mem _
    rw [Polynomial.mem_degreeLT, Polynomial.degree_eq_natDegree ha0]
    have h : a.natDegree < (n + 1).toNat := by omega
    exact_mod_cast h
  · rintro ⟨a, ha, rfl⟩
    rw [Polynomial.mem_degreeLT] at ha
    refine ⟨a, ?_, rfl⟩
    rcases eq_or_ne a 0 with rfl | ha0
    · exact Or.inl rfl
    · right
      rw [Polynomial.degree_eq_natDegree ha0] at ha
      have : (a.natDegree : ℤ) < ((n + 1).toNat : ℤ) := by exact_mod_cast ha
      omega

lemma ell_single_none (n : ℤ) :
    (ell (Finsupp.single (none : Place k) n) : ℤ) = max (n + 1) 0 := by
  rw [ell, RRSpace_single_none,
    ← (Submodule.equivMapOfInjective (polyToRatFunc k) polyToRatFunc_injective
      (Polynomial.degreeLT k (n + 1).toNat)).finrank_eq,
    (Polynomial.degreeLTEquiv k (n + 1).toNat).finrank_eq, Module.finrank_fin_fun,
    Int.toNat_eq_max]

theorem ell_eq (D : Divisor k) : (ell D : ℤ) = max (degDiv D + 1) 0 := by
  obtain ⟨g, hg, hD⟩ := exists_principal D
  rw [← ell_sub_divisorOf D hg, hD, ell_single_none]

theorem degDiv_canonical : degDiv (canonicalDivisor k) = -2 := by
  rw [canonicalDivisor, degDiv_single]
  simp [placeDeg]

/-- The projective line has genus zero. -/
theorem genus_eq_zero : genus k = 0 := by
  have h := ell_eq (canonicalDivisor k)
  rw [degDiv_canonical] at h
  have : ((genus k : ℤ)) = 0 := by rw [genus, h]; norm_num
  exact_mod_cast this

/-- The canonical divisor has degree `2g - 2`. -/
theorem degDiv_canonical_eq : degDiv (canonicalDivisor k) = 2 * (genus k : ℤ) - 2 := by
  rw [degDiv_canonical, genus_eq_zero]
  norm_num

/-- `ℓ(0) = 1`: the only rational functions without poles anywhere are the constants. -/
theorem ell_zero_divisor : ell (0 : Divisor k) = 1 := by
  have h := ell_eq (0 : Divisor k)
  rw [degDiv_zero] at h
  norm_num at h
  exact_mod_cast h

/-- The degree of a principal divisor is zero. -/
theorem degDiv_divisorOf {f : RatFunc k} (hf : f ≠ 0) : degDiv (divisorOf f) = 0 := by
  have h1 : ell ((0 : Divisor k) - divisorOf f) = ell (0 : Divisor k) := ell_sub_divisorOf 0 hf
  have h2 := ell_eq ((0 : Divisor k) - divisorOf f)
  rw [h1, ell_zero_divisor, degDiv_sub, degDiv_zero] at h2
  omega

/-- **Riemann–Roch** for the smooth projective curve `ℙ¹` over an arbitrary field `k`:
`ℓ(D) - ℓ(K - D) = deg D + 1 - g`. -/
theorem riemann_roch_curve (D : Divisor k) :
    (ell D : ℤ) - (ell (canonicalDivisor k - D) : ℤ) = degDiv D + 1 - (genus k : ℤ) := by
  rw [ell_eq, ell_eq, genus_eq_zero, degDiv_sub, degDiv_canonical]
  push_cast
  omega

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

