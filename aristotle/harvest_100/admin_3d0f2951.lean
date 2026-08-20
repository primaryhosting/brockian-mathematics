/-
# Riemann Roch Curve
Category: Frontier Math
Target: Math2.riemann_roch_curve
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/
-- (Lean 4 requires `import` lines to precede any module docstring `/-! ... -/`,
-- so the header above is a plain comment and is repeated as a docstring below.)

import Mathlib

/-!
# Riemann Roch Curve
Category: Frontier Math
Target: Math2.riemann_roch_curve
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)

## Scope

Mathlib (as of this version) contains no Riemann–Roch theorem for curves, no divisors on
curves, and no genus, so everything used here is developed from scratch in this file.

We formalize the smooth projective curve `ℙ¹_k` over an arbitrary field `k` through its
function field `k(X)`: its closed points are the monic irreducible polynomials (the closed
points of `𝔸¹ = Spec k[X]`) together with the point at infinity, each equipped with its
normalized valuation `ord P` and its residue degree `deg P`.  Divisors, the degree of a
divisor, the Riemann–Roch space `L(D)`, its dimension `ℓ(D)`, the canonical divisor `K` and
the genus `g = ℓ(K)` are all defined here, and the main theorem
`Math2.riemann_roch_curve` proves

  `ℓ(D) - ℓ(K - D) = deg D + 1 - g`

for every divisor `D` on this curve.  The genus is *computed* (`Math2.genus_eq_zero`), not
assumed, and `Math2.riemann_roch_of_degree_eq_neg_two` shows the identity holds with `K`
replaced by any divisor of degree `2g - 2 = -2`.

The key input is the computation `ℓ(D) = max (deg D + 1) 0` (`Math2.ell_eq_max`), obtained
from an explicit `k`-linear isomorphism between `L(D)` and the space of polynomials of
degree `< deg D + 1`.
-/

open scoped BigOperators
open scoped Classical

open Polynomial

set_option maxHeartbeats 1000000
set_option relaxedAutoImplicit false
set_option autoImplicit false

namespace Math2

variable {k : Type*} [Field k]

/-! ## Closed points of the projective line -/

/-- A finite closed point of the projective line `ℙ¹_k`, i.e. a closed point of the affine
line `𝔸¹_k = Spec k[X]`: a monic irreducible polynomial. -/
abbrev FinitePlace (k : Type*) [Field k] := {p : k[X] // p.Monic ∧ Irreducible p}

/-- The closed points of the smooth projective curve `ℙ¹_k`: the closed points of the affine
line, together with the point at infinity (`none`). -/
abbrev Place (k : Type*) [Field k] := Option (FinitePlace k)

/-- The degree `[k(P) : k]` of a closed point of `ℙ¹_k`. -/
def placeDeg : Place k → ℕ
  | none => 1
  | some p => p.1.natDegree

/-- The order of vanishing of a rational function at a finite place, i.e. the normalized
discrete valuation `v_p` of the local ring at `p`. -/
noncomputable def ordP (p : k[X]) (f : RatFunc k) : ℤ :=
  (multiplicity p f.num : ℤ) - (multiplicity p f.denom : ℤ)

/-- The order of vanishing of a rational function at a closed point of `ℙ¹_k`.  At a finite
place this is the valuation `v_p`; at infinity it is `-deg f`, the valuation attached to the
uniformizer `1/X`. -/
noncomputable def ord : Place k → RatFunc k → ℤ
  | none, f => -f.intDegree
  | some p, f => ordP p.1 f

/-! ## Basic properties of the valuations `ord P` -/

lemma mult_mul {p a b : k[X]} (hp : Prime p) (ha : a ≠ 0) (hb : b ≠ 0) :
    multiplicity p (a * b) = multiplicity p a + multiplicity p b :=
  multiplicity_mul hp (FiniteMultiplicity.of_prime_left hp (mul_ne_zero ha hb))

lemma mult_add_ge {p x y : k[X]} (hp : Prime p) (hx : x ≠ 0) (hy : y ≠ 0) (hxy : x + y ≠ 0) :
    min (multiplicity p x) (multiplicity p y) ≤ multiplicity p (x + y) := by
  have hfx : FiniteMultiplicity p x := FiniteMultiplicity.of_prime_left hp hx
  have hfy : FiniteMultiplicity p y := FiniteMultiplicity.of_prime_left hp hy
  have hfxy : FiniteMultiplicity p (x + y) := FiniteMultiplicity.of_prime_left hp hxy
  have h := min_le_emultiplicity_add (p := p) (a := x) (b := y)
  rw [hfx.emultiplicity_eq_multiplicity, hfy.emultiplicity_eq_multiplicity,
    hfxy.emultiplicity_eq_multiplicity] at h
  exact_mod_cast (by simpa [← Nat.cast_min] using h)

lemma ordP_div {p : k[X]} (hp : Prime p) {a b : k[X]} (ha : a ≠ 0) (hb : b ≠ 0) :
    ordP p (algebraMap k[X] (RatFunc k) a / algebraMap k[X] (RatFunc k) b)
      = (multiplicity p a : ℤ) - (multiplicity p b : ℤ) := by
  set f : RatFunc k := algebraMap k[X] (RatFunc k) a / algebraMap k[X] (RatFunc k) b with hf
  have hf0 : f ≠ 0 := div_ne_zero (RatFunc.algebraMap_ne_zero ha) (RatFunc.algebraMap_ne_zero hb)
  have hnum : f.num ≠ 0 := RatFunc.num_ne_zero hf0
  have hden : f.denom ≠ 0 := RatFunc.denom_ne_zero f
  have key : f.num * b = a * f.denom := by
    have h1 : (algebraMap k[X] (RatFunc k)) f.num / (algebraMap k[X] (RatFunc k)) f.denom
        = (algebraMap k[X] (RatFunc k)) a / (algebraMap k[X] (RatFunc k)) b := by
      rw [RatFunc.num_div_denom f, hf]
    rw [div_eq_div_iff (RatFunc.algebraMap_ne_zero hden) (RatFunc.algebraMap_ne_zero hb),
      ← map_mul, ← map_mul] at h1
    exact IsFractionRing.injective k[X] (RatFunc k) h1
  have h2 : multiplicity p (f.num * b) = multiplicity p (a * f.denom) := by rw [key]
  rw [mult_mul hp hnum hb, mult_mul hp ha hden] at h2
  simp only [ordP]
  omega

lemma ordP_algebraMap {p : k[X]} (hp : Prime p) {a : k[X]} (ha : a ≠ 0) :
    ordP p (algebraMap k[X] (RatFunc k) a) = (multiplicity p a : ℤ) := by
  have := ordP_div hp ha (one_ne_zero (α := k[X]))
  simpa [multiplicity_eq_zero.mpr hp.not_dvd_one] using this

lemma ordP_mul {p : k[X]} (hp : Prime p) {f g : RatFunc k} (hf : f ≠ 0) (hg : g ≠ 0) :
    ordP p (f * g) = ordP p f + ordP p g := by
  have h1 : f * g = (algebraMap k[X] (RatFunc k)) (f.num * g.num)
      / (algebraMap k[X] (RatFunc k)) (f.denom * g.denom) := by
    rw [map_mul, map_mul, ← div_mul_div_comm, RatFunc.num_div_denom, RatFunc.num_div_denom]
  rw [h1, ordP_div hp (mul_ne_zero (RatFunc.num_ne_zero hf) (RatFunc.num_ne_zero hg))
      (mul_ne_zero (RatFunc.denom_ne_zero f) (RatFunc.denom_ne_zero g)),
    mult_mul hp (RatFunc.num_ne_zero hf) (RatFunc.num_ne_zero hg),
    mult_mul hp (RatFunc.denom_ne_zero f) (RatFunc.denom_ne_zero g)]
  simp only [ordP]
  push_cast
  ring

lemma ordP_add {p : k[X]} (hp : Prime p) {f g : RatFunc k} (hf : f ≠ 0) (hg : g ≠ 0)
    (hfg : f + g ≠ 0) : min (ordP p f) (ordP p g) ≤ ordP p (f + g) := by
  set a := f.num with hha; set b := f.denom with hhb
  set c := g.num with hhc; set d := g.denom with hhd
  have ha : a ≠ 0 := RatFunc.num_ne_zero hf
  have hb : b ≠ 0 := RatFunc.denom_ne_zero f
  have hc : c ≠ 0 := RatFunc.num_ne_zero hg
  have hd : d ≠ 0 := RatFunc.denom_ne_zero g
  have h1 : f + g = (algebraMap k[X] (RatFunc k)) (a * d + b * c)
      / (algebraMap k[X] (RatFunc k)) (b * d) := by
    rw [map_add, map_mul, map_mul, map_mul, ← div_add_div _ _ (RatFunc.algebraMap_ne_zero hb)
      (RatFunc.algebraMap_ne_zero hd), hha, hhb, hhc, hhd, RatFunc.num_div_denom,
      RatFunc.num_div_denom]
  have hsum : a * d + b * c ≠ 0 := by
    intro h
    apply hfg
    rw [h1, h, map_zero, zero_div]
  rw [h1, ordP_div hp hsum (mul_ne_zero hb hd), mult_mul hp hb hd]
  have hkey := mult_add_ge hp (mul_ne_zero ha hd) (mul_ne_zero hb hc) hsum
  rw [mult_mul hp ha hd, mult_mul hp hb hc] at hkey
  simp only [ordP, ← hha, ← hhb, ← hhc, ← hhd]
  omega

lemma ordP_C {p : k[X]} (hp : Prime p) {c : k} (hc : c ≠ 0) : ordP p (RatFunc.C c) = 0 := by
  simp only [ordP, RatFunc.num_C, RatFunc.denom_C]
  rw [multiplicity_eq_zero.mpr, multiplicity_eq_zero.mpr hp.not_dvd_one]
  · simp
  · intro h
    exact hp.not_unit (isUnit_of_dvd_unit h (Polynomial.isUnit_C.mpr hc.isUnit))

/-- A rational function with no poles at any finite place is a polynomial. -/
lemma exists_polynomial_of_ordP_nonneg {f : RatFunc k}
    (h : ∀ p : k[X], p.Monic → Irreducible p → 0 ≤ ordP p f) :
    ∃ u : k[X], f = algebraMap k[X] (RatFunc k) u := by
  have hden : f.denom ≠ 0 := RatFunc.denom_ne_zero f
  have hunit : IsUnit f.denom := by
    by_contra hnu
    obtain ⟨q, hq, hqd⟩ := WfDvdMonoid.exists_irreducible_factor hnu hden
    have hlc : q.leadingCoeff ≠ 0 := Polynomial.leadingCoeff_ne_zero.mpr hq.ne_zero
    have hcu : IsUnit (Polynomial.C (q.leadingCoeff)⁻¹) :=
      Polynomial.isUnit_C.mpr (IsUnit.mk0 _ (inv_ne_zero hlc))
    set q' : k[X] := q * Polynomial.C (q.leadingCoeff)⁻¹ with hq'
    have hassoc : Associated q q' := ⟨hcu.unit, by rw [hq']; congr⟩
    have hq'm : q'.Monic := Polynomial.monic_mul_leadingCoeff_inv hq.ne_zero
    have hq'i : Irreducible q' := hassoc.irreducible hq
    have hq'd : q' ∣ f.denom := hassoc.symm.dvd.trans hqd
    have hprime : Prime q' := hq'i.prime
    have hnumdvd : ¬ q' ∣ f.num := fun hdn =>
      hprime.not_unit ((RatFunc.isCoprime_num_denom f).isUnit_of_dvd' hdn hq'd)
    have h1 : multiplicity q' f.num = 0 := multiplicity_eq_zero.mpr hnumdvd
    have h2 : 1 ≤ multiplicity q' f.denom :=
      (FiniteMultiplicity.of_prime_left hprime hden).le_multiplicity_of_pow_dvd
        (by simpa using hq'd)
    have h3 := h q' hq'm hq'i
    simp only [ordP, h1] at h3
    omega
  have hd1 : f.denom = 1 := (RatFunc.monic_denom f).eq_one_of_isUnit hunit
  refine ⟨f.num, ?_⟩
  rw [← RatFunc.num_div_denom f, hd1]
  simp

/-- The prime associated with a finite place. -/
lemma FinitePlace.prime (p : FinitePlace k) : Prime p.1 := p.2.2.prime

lemma ord_mul (P : Place k) {f g : RatFunc k} (hf : f ≠ 0) (hg : g ≠ 0) :
    ord P (f * g) = ord P f + ord P g := by
  cases P with
  | none => simp [ord, RatFunc.intDegree_mul hf hg]; ring
  | some p => exact ordP_mul p.prime hf hg

lemma ord_add (P : Place k) {f g : RatFunc k} (hf : f ≠ 0) (hg : g ≠ 0) (hfg : f + g ≠ 0) :
    min (ord P f) (ord P g) ≤ ord P (f + g) := by
  cases P with
  | none =>
    have := RatFunc.intDegree_add_le hg hfg
    simp only [ord]
    omega
  | some p => exact ordP_add p.prime hf hg hfg

lemma ord_C (P : Place k) {c : k} (hc : c ≠ 0) : ord P (RatFunc.C c) = 0 := by
  cases P with
  | none => simp [ord]
  | some p => exact ordP_C p.prime hc

lemma ord_one (P : Place k) : ord P 1 = 0 := by
  have := ord_C P (one_ne_zero (α := k))
  simpa using this

lemma ord_inv (P : Place k) {f : RatFunc k} (hf : f ≠ 0) : ord P f⁻¹ = -ord P f := by
  have h := ord_mul P (inv_ne_zero hf) hf
  rw [inv_mul_cancel₀ hf, ord_one] at h
  omega

lemma ord_zpow (P : Place k) {f : RatFunc k} (hf : f ≠ 0) (n : ℤ) :
    ord P (f ^ n) = n * ord P f := by
  induction n using Int.induction_on with
  | zero => simp [ord_one]
  | succ i ih =>
    rw [zpow_add₀ hf, zpow_one, ord_mul P (zpow_ne_zero _ hf) hf, ih]
    ring
  | pred i ih =>
    rw [zpow_sub₀ hf, zpow_one, div_eq_mul_inv, ord_mul P (zpow_ne_zero _ hf) (inv_ne_zero hf),
      ih, ord_inv P hf]
    ring

lemma ord_prod {ι : Type*} (P : Place k) (s : Finset ι) (F : ι → RatFunc k)
    (h : ∀ i ∈ s, F i ≠ 0) : ord P (∏ i ∈ s, F i) = ∑ i ∈ s, ord P (F i) := by
  classical
  induction s using Finset.induction with
  | empty => simp [ord_one]
  | insert a s ha ih =>
    rw [Finset.prod_insert ha, Finset.sum_insert ha,
      ord_mul P (h a (Finset.mem_insert_self a s))
        (Finset.prod_ne_zero_iff.mpr fun i hi => h i (Finset.mem_insert_of_mem hi)),
      ih fun i hi => h i (Finset.mem_insert_of_mem hi)]

/-! ## Divisors -/

/-- A divisor on `ℙ¹_k`: a finitely supported formal `ℤ`-combination of closed points. -/
abbrev Divisor (k : Type*) [Field k] := Place k →₀ ℤ

/-- The degree homomorphism on divisors. -/
noncomputable def degreeHom : Divisor k →ₗ[ℤ] ℤ :=
  Finsupp.linearCombination ℤ fun P : Place k => (placeDeg P : ℤ)

/-- The degree of a divisor, `deg (∑ n_P · P) = ∑ n_P · deg P`. -/
noncomputable def degree (D : Divisor k) : ℤ := degreeHom D

/-- The Riemann–Roch space `L(D) = {f : div f + D ≥ 0} ∪ {0}`. -/
def LSpace (D : Divisor k) : Submodule k (RatFunc k) where
  carrier := {f | f = 0 ∨ ∀ P : Place k, -D P ≤ ord P f}
  zero_mem' := Or.inl rfl
  add_mem' := by
    intro f g hf hg
    by_cases hfz : f = 0
    · simpa [hfz] using hg
    by_cases hgz : g = 0
    · simpa [hgz] using hf
    by_cases hsum : f + g = 0
    · exact Or.inl hsum
    refine Or.inr fun P => ?_
    have hf' := hf.resolve_left hfz P
    have hg' := hg.resolve_left hgz P
    have := ord_add P hfz hgz hsum
    omega
  smul_mem' := by
    intro c f hf
    by_cases hc : c = 0
    · simp [hc]
    by_cases hfz : f = 0
    · simp [hfz]
    refine Or.inr fun P => ?_
    have hf' := hf.resolve_left hfz P
    rw [RatFunc.smul_eq_C_mul, ord_mul P (by simpa using hc) hfz, ord_C P hc]
    omega

lemma mem_LSpace_iff {D : Divisor k} {f : RatFunc k} (hf : f ≠ 0) :
    f ∈ LSpace D ↔ ∀ P : Place k, -D P ≤ ord P f :=
  ⟨fun h => h.resolve_left hf, fun h => Or.inr h⟩

/-- `ℓ(D) = dim_k L(D)`. -/
noncomputable def ell (D : Divisor k) : ℕ := Module.finrank k (LSpace D)

/-- The canonical divisor of `ℙ¹_k`: the divisor of the global differential `dX`, which is
`-2 · [∞]`. -/
noncomputable def canonicalDivisor (k : Type*) [Field k] : Divisor k := Finsupp.single none (-2)

/-- The genus of the curve, defined intrinsically as `g = ℓ(K) = dim_k H⁰(K)`. -/
noncomputable def genus (k : Type*) [Field k] : ℕ := ell (canonicalDivisor k)

/-! ## Computation of `ℓ(D)` -/

/-- The rational function attached to a closed point: the monic irreducible polynomial at a
finite place, and `1` at infinity. -/
noncomputable def placeElt : Place k → RatFunc k
  | none => 1
  | some p => algebraMap k[X] (RatFunc k) p.1

/-- The degree of the polynomial attached to a closed point (`0` at infinity). -/
def polyDeg : Place k → ℤ
  | none => 0
  | some p => p.1.natDegree

lemma placeElt_ne_zero (P : Place k) : placeElt P ≠ 0 := by
  cases P with
  | none => simp [placeElt]
  | some p => exact RatFunc.algebraMap_ne_zero p.2.2.ne_zero

lemma ord_none_placeElt (P : Place k) : ord none (placeElt P) = -polyDeg P := by
  cases P with
  | none => simp [placeElt, polyDeg, ord]
  | some p => simp [placeElt, polyDeg, ord]

lemma ord_some_placeElt (q : FinitePlace k) (P : Place k) :
    ord (some q) (placeElt P) = if P = some q then 1 else 0 := by
  cases P with
  | none => simp [placeElt, ord, ordP]
  | some p =>
    rw [show placeElt (some p) = algebraMap k[X] (RatFunc k) p.1 from rfl]
    have : ord (some q) (algebraMap k[X] (RatFunc k) p.1)
        = (multiplicity q.1 p.1 : ℤ) := ordP_algebraMap q.prime p.2.2.ne_zero
    rw [this]
    by_cases h : p = q
    · subst h
      simp [multiplicity_self]
    · have hnd : ¬ (q.1 ∣ p.1) := by
        rintro ⟨c, hc⟩
        rcases p.2.2.isUnit_or_isUnit hc with h1 | h1
        · exact q.2.2.not_isUnit h1
        · exact h (Subtype.ext (Polynomial.eq_of_monic_of_associated q.2.1 p.2.1
            ⟨h1.unit, hc.symm⟩).symm)
      simp [multiplicity_eq_zero.mpr hnd, h]

/-- The rational function `∏ p ^ n_p` attached to a divisor `D = ∑ n_P · P` (the factor at
infinity is `1`). -/
noncomputable def hDiv (D : Divisor k) : RatFunc k := D.prod fun P n => placeElt P ^ n

lemma hDiv_ne_zero (D : Divisor k) : hDiv D ≠ 0 :=
  Finset.prod_ne_zero_iff.mpr fun P _ => zpow_ne_zero _ (placeElt_ne_zero P)

lemma ord_hDiv (D : Divisor k) (Q : Place k) :
    ord Q (hDiv D) = ∑ P ∈ D.support, D P * ord Q (placeElt P) := by
  rw [hDiv, Finsupp.prod, ord_prod Q _ _ fun P _ => zpow_ne_zero _ (placeElt_ne_zero P)]
  exact Finset.sum_congr rfl fun P _ => ord_zpow Q (placeElt_ne_zero P) (D P)

lemma ord_hDiv_some (D : Divisor k) (q : FinitePlace k) :
    ord (some q) (hDiv D) = D (some q) := by
  classical
  rw [ord_hDiv]
  simp only [ord_some_placeElt, mul_ite, mul_one, mul_zero]
  rw [Finset.sum_ite_eq' D.support (some q) (fun P => D P)]
  by_cases h : some q ∈ D.support
  · simp [h]
  · simp [h, Finsupp.notMem_support_iff.mp h]

lemma degree_eq_sum (D : Divisor k) : degree D = ∑ P ∈ D.support, D P * placeDeg P := by
  simp [degree, degreeHom, Finsupp.linearCombination_apply, Finsupp.sum]

lemma sum_polyDeg (D : Divisor k) :
    ∑ P ∈ D.support, D P * polyDeg P = degree D - D none := by
  classical
  have hsplit : ∑ P ∈ D.support, D P * placeDeg P - ∑ P ∈ D.support, D P * polyDeg P
      = ∑ P ∈ D.support, (if P = none then D P else 0) := by
    rw [← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun P _ => ?_
    cases P with
    | none => simp [placeDeg, polyDeg]
    | some p => simp [placeDeg, polyDeg]
  rw [Finset.sum_ite_eq' D.support none (fun P => D P)] at hsplit
  rw [degree_eq_sum]
  by_cases h : (none : Place k) ∈ D.support
  · rw [if_pos h] at hsplit; omega
  · rw [if_neg h] at hsplit
    have : D none = 0 := Finsupp.notMem_support_iff.mp h
    omega

lemma ord_hDiv_none (D : Divisor k) : ord none (hDiv D) = D none - degree D := by
  rw [ord_hDiv]
  simp only [ord_none_placeElt, mul_neg]
  rw [Finset.sum_neg_distrib, sum_polyDeg]
  ring

/-- Every element of `L(D)` is of the form `u / h_D` with `u` a polynomial. -/
lemma exists_poly_of_mem_LSpace {D : Divisor k} {f : RatFunc k} (hf : f ≠ 0)
    (hmem : f ∈ LSpace D) :
    ∃ u : k[X], u ≠ 0 ∧ f = algebraMap k[X] (RatFunc k) u * (hDiv D)⁻¹ := by
  have hord := (mem_LSpace_iff hf).mp hmem
  have hg0 : f * hDiv D ≠ 0 := mul_ne_zero hf (hDiv_ne_zero D)
  have hpos : ∀ p : k[X], p.Monic → Irreducible p → 0 ≤ ordP p (f * hDiv D) := by
    intro p hm hi
    have hq : ord (some ⟨p, hm, hi⟩) (f * hDiv D)
        = ord (some ⟨p, hm, hi⟩) f + ord (some ⟨p, hm, hi⟩) (hDiv D) :=
      ord_mul _ hf (hDiv_ne_zero D)
    rw [ord_hDiv_some] at hq
    have := hord (some ⟨p, hm, hi⟩)
    have hq' : ordP p (f * hDiv D) = ord (some ⟨p, hm, hi⟩) (f * hDiv D) := rfl
    omega
  obtain ⟨u, hu⟩ := exists_polynomial_of_ordP_nonneg hpos
  have hune : u ≠ 0 := by
    intro h
    rw [h, map_zero] at hu
    exact hg0 hu
  refine ⟨u, hune, ?_⟩
  rw [← hu, mul_inv_cancel_right₀ (hDiv_ne_zero D)]

/-- Membership criterion in `L(D)` for functions of the form `u / h_D`. -/
lemma mem_LSpace_poly {D : Divisor k} {u : k[X]} (hu : u ≠ 0) :
    algebraMap k[X] (RatFunc k) u * (hDiv D)⁻¹ ∈ LSpace D ↔ (u.natDegree : ℤ) ≤ degree D := by
  have hune : algebraMap k[X] (RatFunc k) u ≠ 0 := RatFunc.algebraMap_ne_zero hu
  have hfne : algebraMap k[X] (RatFunc k) u * (hDiv D)⁻¹ ≠ 0 :=
    mul_ne_zero hune (inv_ne_zero (hDiv_ne_zero D))
  have hord : ∀ P : Place k, ord P (algebraMap k[X] (RatFunc k) u * (hDiv D)⁻¹)
      = ord P (algebraMap k[X] (RatFunc k) u) - ord P (hDiv D) := by
    intro P
    rw [ord_mul P hune (inv_ne_zero (hDiv_ne_zero D)), ord_inv P (hDiv_ne_zero D)]
    ring
  rw [mem_LSpace_iff hfne]
  constructor
  · intro h
    have hnone := h none
    rw [hord none, ord_hDiv_none] at hnone
    have : ord (none : Place k) (algebraMap k[X] (RatFunc k) u) = -(u.natDegree : ℤ) := by
      simp [ord]
    omega
  · intro h P
    cases P with
    | none =>
      rw [hord none, ord_hDiv_none]
      have : ord (none : Place k) (algebraMap k[X] (RatFunc k) u) = -(u.natDegree : ℤ) := by
        simp [ord]
      omega
    | some q =>
      rw [hord (some q), ord_hDiv_some]
      have h0 : 0 ≤ ord (some q) (algebraMap k[X] (RatFunc k) u) := by
        rw [show ord (some q) (algebraMap k[X] (RatFunc k) u) = ordP q.1 _ from rfl,
          ordP_algebraMap q.prime hu]
        positivity
      omega

lemma mem_degreeLT_iff {u : k[X]} {N : ℤ} :
    u ∈ Polynomial.degreeLT k (N + 1).toNat ↔ (u = 0 ∨ (u.natDegree : ℤ) ≤ N) := by
  rw [Polynomial.mem_degreeLT]
  constructor
  · intro h
    by_cases hu : u = 0
    · exact Or.inl hu
    refine Or.inr ?_
    rw [Polynomial.degree_eq_natDegree hu, Nat.cast_lt] at h
    omega
  · rintro (rfl | h)
    · simp [Polynomial.degree_zero]
    · by_cases hu : u = 0
      · simp [hu, Polynomial.degree_zero]
      rw [Polynomial.degree_eq_natDegree hu, Nat.cast_lt]
      omega

/-- The `k`-linear map `u ↦ u / h_D` from polynomials to rational functions. -/
noncomputable def polyToL (D : Divisor k) : k[X] →ₗ[k] RatFunc k :=
  (LinearMap.mulRight k (hDiv D)⁻¹).comp
    ((IsScalarTower.toAlgHom k k[X] (RatFunc k)).toLinearMap)

lemma polyToL_apply (D : Divisor k) (u : k[X]) :
    polyToL D u = algebraMap k[X] (RatFunc k) u * (hDiv D)⁻¹ := rfl

/-- `L(D)` is isomorphic, as a `k`-vector space, to the space of polynomials of degree
`< deg D + 1`. -/
noncomputable def LSpaceEquiv (D : Divisor k) :
    (Polynomial.degreeLT k (degree D + 1).toNat) ≃ₗ[k] LSpace D := by
  refine LinearEquiv.ofBijective
    (LinearMap.codRestrict (LSpace D) ((polyToL D).comp (Submodule.subtype _)) ?_) ⟨?_, ?_⟩
  · rintro ⟨u, hu⟩
    rcases mem_degreeLT_iff.mp hu with rfl | h
    · simp [polyToL_apply]
    · by_cases hu0 : u = 0
      · simp [hu0, polyToL_apply]
      · exact (mem_LSpace_poly hu0).mpr h
  · intro u v huv
    have h : polyToL D u.1 = polyToL D v.1 := congrArg Subtype.val huv
    simp only [polyToL_apply] at h
    have := mul_right_cancel₀ (inv_ne_zero (hDiv_ne_zero D)) h
    exact Subtype.ext (IsFractionRing.injective k[X] (RatFunc k) this)
  · rintro ⟨f, hf⟩
    by_cases hf0 : f = 0
    · refine ⟨⟨0, Submodule.zero_mem _⟩, ?_⟩
      simp [hf0, polyToL_apply, Subtype.ext_iff]
    obtain ⟨u, hu0, hu⟩ := exists_poly_of_mem_LSpace hf0 hf
    have hdeg : (u.natDegree : ℤ) ≤ degree D := (mem_LSpace_poly hu0).mp (hu ▸ hf)
    exact ⟨⟨u, mem_degreeLT_iff.mpr (Or.inr hdeg)⟩, Subtype.ext (by simpa [polyToL_apply] using hu.symm)⟩

/-- The dimension of the Riemann–Roch space of a divisor on `ℙ¹_k`. -/
theorem ell_eq_max (D : Divisor k) : (ell D : ℤ) = max (degree D + 1) 0 := by
  have h : Module.finrank k (LSpace D) = (degree D + 1).toNat := by
    rw [← (LSpaceEquiv D).finrank_eq, (Polynomial.degreeLTEquiv k _).finrank_eq,
      Module.finrank_fin_fun]
  rw [ell, h]
  omega

/-! ## The Riemann–Roch theorem -/

theorem degree_sub (D E : Divisor k) : degree (D - E) = degree D - degree E :=
  map_sub degreeHom D E

theorem degree_canonicalDivisor : degree (canonicalDivisor k) = -2 := by
  simp [degree, degreeHom, canonicalDivisor, Finsupp.linearCombination_single, placeDeg]

/-- The genus of `ℙ¹` is zero. -/
theorem genus_eq_zero : genus k = 0 := by
  have h := ell_eq_max (canonicalDivisor k)
  rw [degree_canonicalDivisor] at h
  simpa [genus] using h

/-- **Riemann–Roch**, stated for an arbitrary canonical divisor, i.e. for an arbitrary divisor
`K` of degree `2g - 2 = -2`.  (On `ℙ¹` all divisors of a given degree are linearly equivalent,
so this is exactly the class of canonical divisors.) -/
theorem riemann_roch_of_degree_eq_neg_two (K D : Divisor k) (hK : degree K = -2) :
    (ell D : ℤ) - (ell (K - D) : ℤ) = degree D + 1 - genus k := by
  have hd : degree (K - D) = -2 - degree D := by rw [degree_sub, hK]
  rw [ell_eq_max, ell_eq_max, hd, genus_eq_zero]
  rcases le_or_gt (-1) (degree D) with h | h
  · rw [max_eq_left (by omega), max_eq_right (by omega)]; omega
  · rw [max_eq_right (by omega), max_eq_left (by omega)]; omega

/-- **Riemann–Roch** for the smooth projective curve `ℙ¹_k` over an arbitrary field `k`:
for every divisor `D`,
`ℓ(D) - ℓ(K - D) = deg D + 1 - g`,
where `K` is the canonical divisor `-2 · [∞]` (the divisor of the differential `dX`),
`ℓ(D) = dim_k L(D)` is the dimension of the Riemann–Roch space of `D`, `deg D` is the degree
of `D` (points being counted with their residue degrees), and `g = ℓ(K)` is the genus. -/
theorem riemann_roch_curve (D : Divisor k) :
    (ell D : ℤ) - (ell (canonicalDivisor k - D) : ℤ) = degree D + 1 - genus k :=
  riemann_roch_of_degree_eq_neg_two _ D degree_canonicalDivisor

/-! ## Sanity checks -/

/-- The only functions regular everywhere on a projective curve are the constants:
`ℓ(0) = 1`. -/
theorem ell_zero : ell (0 : Divisor k) = 1 := by
  have h := ell_eq_max (0 : Divisor k)
  simp only [degree, map_zero] at h
  omega

/-- For a divisor of nonnegative degree on `ℙ¹`, `ℓ(D) = deg D + 1`. -/
theorem ell_of_degree_nonneg {D : Divisor k} (h : 0 ≤ degree D) :
    (ell D : ℤ) = degree D + 1 := by
  rw [ell_eq_max, max_eq_left (by omega)]

/-- A divisor of negative degree has no nonzero global sections. -/
theorem ell_eq_zero_of_degree_neg {D : Divisor k} (h : degree D < 0) : ell D = 0 := by
  have := ell_eq_max D
  omega

end Math2

