/-
# Riemann Roch Curve
Category: Frontier Math
Target: Math2.riemann_roch_curve
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

open scoped BigOperators
open scoped Classical

set_option maxHeartbeats 1000000
set_option synthInstance.maxHeartbeats 400000
set_option maxRecDepth 4000

open Polynomial

/-!
# Riemann–Roch for a smooth projective curve

Mathlib (as of this development) contains no Riemann–Roch theorem, no theory of divisors on
curves, no sheaf cohomology of curves and no Serre duality, so the whole set-up below is built
from scratch on top of Mathlib's theory of the rational function field `RatFunc k` and of
polynomials.

We work with the smooth projective curve `ℙ¹_k` over an arbitrary field `k`, described through
its function field `k(X) = RatFunc k`:

* its closed points (`Math2.Place`) are the monic irreducible polynomials together with the
  point at infinity;
* `Math2.ord` is the normalized valuation (order of vanishing) at a closed point;
* `Math2.Divisor` is the group of divisors, `Math2.degDiv` the degree of a divisor
  (each point counted with the degree of its residue field);
* `Math2.RRSpace D` is the Riemann–Roch space `L(D) = {f ≠ 0 : div f + D ≥ 0} ∪ {0}` and
  `Math2.ell D = ℓ(D)` its dimension over `k`;
* `Math2.canonicalDivisor` is the canonical divisor `-2·∞` and `Math2.genus` the genus `0`.

The main result `Math2.riemann_roch_curve` is the Riemann–Roch formula
`ℓ(D) - ℓ(K - D) = deg D + 1 - g`, valid for every divisor `D`.
-/

namespace Math2

/-!
## The smooth projective curve

We work with the projective line `ℙ¹_k` over an arbitrary field `k`, presented through its
function field `k(X) = RatFunc k`.  Its closed points (places of the function field) are the
monic irreducible polynomials (the finite closed points) together with the point at infinity.
-/

variable {k : Type*} [Field k]

/-- A closed point of the projective line `ℙ¹_k`: either a monic irreducible polynomial
(a finite closed point) or `none`, the point at infinity. -/
abbrev Place (k : Type*) [Field k] := Option {p : k[X] // p.Monic ∧ Irreducible p}

/-- A divisor on `ℙ¹_k`: a finitely supported formal `ℤ`-combination of closed points. -/
abbrev Divisor (k : Type*) [Field k] := Place k →₀ ℤ

/-! ### Order functions (normalized valuations) at the closed points -/

lemma algMap_inj (a b : k[X]) (h : algebraMap k[X] (RatFunc k) a = algebraMap k[X] (RatFunc k) b) :
    a = b := IsFractionRing.injective k[X] (RatFunc k) h

lemma algMap_ne_zero {a : k[X]} (ha : a ≠ 0) : algebraMap k[X] (RatFunc k) a ≠ 0 := fun hc =>
  ha (algMap_inj a 0 (by simpa using hc))

/-- The order of vanishing of a rational function at the finite closed point `p`. -/
noncomputable def ordFin (p : k[X]) (f : RatFunc k) : ℤ :=
  (multiplicity p f.num : ℤ) - (multiplicity p f.denom : ℤ)

lemma algebraMap_num_eq (f : RatFunc k) :
    algebraMap k[X] (RatFunc k) f.num = f * algebraMap k[X] (RatFunc k) f.denom := by
  have h := RatFunc.num_div_denom f
  have hd : algebraMap k[X] (RatFunc k) f.denom ≠ 0 := algMap_ne_zero (RatFunc.denom_ne_zero f)
  field_simp at h
  linear_combination h

lemma ordFin_eq {p : k[X]} (hp : Prime p) {f : RatFunc k} {a b : k[X]} (ha : a ≠ 0) (hb : b ≠ 0)
    (h : f * algebraMap k[X] (RatFunc k) b = algebraMap k[X] (RatFunc k) a) :
    ordFin p f = (multiplicity p a : ℤ) - (multiplicity p b : ℤ) := by
  have hf : f ≠ 0 := by
    rintro rfl
    simp only [zero_mul] at h
    exact ha (algMap_inj a 0 (by simpa using h.symm))
  have hnum : f.num ≠ 0 := RatFunc.num_ne_zero hf
  have hden : f.denom ≠ 0 := RatFunc.denom_ne_zero f
  have key : f.num * b = a * f.denom := by
    apply algMap_inj
    rw [map_mul, map_mul, algebraMap_num_eq f, mul_right_comm, h]
  have hmul := congrArg (fun m => multiplicity p m) key
  simp only at hmul
  rw [multiplicity_mul hp (FiniteMultiplicity.of_prime_left hp (mul_ne_zero hnum hb)),
      multiplicity_mul hp (FiniteMultiplicity.of_prime_left hp (mul_ne_zero ha hden))] at hmul
  unfold ordFin
  omega

lemma ordFin_algebraMap {p : k[X]} (hp : Prime p) {a : k[X]} (ha : a ≠ 0) :
    ordFin p (algebraMap k[X] (RatFunc k) a) = multiplicity p a := by
  rw [ordFin_eq hp ha one_ne_zero (by simp)]
  simp [multiplicity_eq_zero.2 (fun hd => hp.not_unit (isUnit_of_dvd_one hd))]

lemma ordFin_mul {p : k[X]} (hp : Prime p) {f g : RatFunc k} (hf : f ≠ 0) (hg : g ≠ 0) :
    ordFin p (f * g) = ordFin p f + ordFin p g := by
  have hnf := RatFunc.num_ne_zero hf
  have hng := RatFunc.num_ne_zero hg
  have hdf := RatFunc.denom_ne_zero f
  have hdg := RatFunc.denom_ne_zero g
  have h : (f * g) * algebraMap k[X] (RatFunc k) (f.denom * g.denom)
      = algebraMap k[X] (RatFunc k) (f.num * g.num) := by
    rw [map_mul, map_mul, algebraMap_num_eq f, algebraMap_num_eq g]; ring
  rw [ordFin_eq hp (mul_ne_zero hnf hng) (mul_ne_zero hdf hdg) h,
    multiplicity_mul hp (FiniteMultiplicity.of_prime_left hp (mul_ne_zero hnf hng)),
    multiplicity_mul hp (FiniteMultiplicity.of_prime_left hp (mul_ne_zero hdf hdg))]
  unfold ordFin
  push_cast
  ring

/-- The order of vanishing of a rational function at a closed point of `ℙ¹_k`. -/
noncomputable def ord : Place k → RatFunc k → ℤ
  | none => fun f => -f.intDegree
  | some p => fun f => ordFin p.1 f

/-- The degree of a closed point of `ℙ¹_k` (the degree of its residue field over `k`). -/
def degPlace : Place k → ℤ
  | none => 1
  | some p => (p.1.natDegree : ℤ)

/-- The degree of a divisor. -/
noncomputable def degDiv (D : Divisor k) : ℤ := D.sum fun P n => n * degPlace P

lemma ord_mul (P : Place k) {f g : RatFunc k} (hf : f ≠ 0) (hg : g ≠ 0) :
    ord P (f * g) = ord P f + ord P g := by
  cases P with
  | none => simp [ord, RatFunc.intDegree_mul hf hg]; ring
  | some p => exact ordFin_mul (p.2.2.prime) hf hg

lemma ord_one (P : Place k) : ord P (1 : RatFunc k) = 0 := by
  cases P with
  | none => simp [ord, RatFunc.intDegree_one]
  | some p =>
      have hp : Prime p.1 := p.2.2.prime
      simpa using (ordFin_algebraMap hp (a := (1 : k[X])) one_ne_zero).trans
        (by simp [multiplicity_eq_zero.2 (fun hd => hp.not_unit (isUnit_of_dvd_one hd))])

lemma ord_inv (P : Place k) {f : RatFunc k} (hf : f ≠ 0) : ord P f⁻¹ = -ord P f := by
  have h := ord_mul P hf (inv_ne_zero hf)
  rw [mul_inv_cancel₀ hf, ord_one] at h
  omega

lemma ord_zpow (P : Place k) {f : RatFunc k} (hf : f ≠ 0) (n : ℤ) :
    ord P (f ^ n) = n * ord P f := by
  induction n using Int.induction_on with
  | zero => simp [ord_one]
  | succ i ih =>
      have : f ^ ((i : ℤ) + 1) = f ^ (i : ℤ) * f := by rw [zpow_add₀ hf]; simp
      rw [this, ord_mul P (zpow_ne_zero _ hf) hf, ih]; ring
  | pred i ih =>
      have : f ^ (-(i : ℤ) - 1) = f ^ (-(i : ℤ)) * f⁻¹ := by
        rw [sub_eq_add_neg, zpow_add₀ hf]; simp
      rw [this, ord_mul P (zpow_ne_zero _ hf) (inv_ne_zero hf), ih, ord_inv P hf]; ring

lemma ord_prod {ι : Type*} (P : Place k) (s : Finset ι) (F : ι → RatFunc k)
    (h : ∀ i ∈ s, F i ≠ 0) : ord P (∏ i ∈ s, F i) = ∑ i ∈ s, ord P (F i) := by
  classical
  induction s using Finset.induction with
  | empty => simp [ord_one]
  | insert a s ha ih =>
      rw [Finset.prod_insert ha, Finset.sum_insert ha,
        ord_mul P (h a (Finset.mem_insert_self a s))
          (Finset.prod_ne_zero_iff.2 fun i hi => h i (Finset.mem_insert_of_mem hi)),
        ih fun i hi => h i (Finset.mem_insert_of_mem hi)]

/-! ### The Riemann–Roch space -/

/-- The rational function attached to a closed point: the monic irreducible polynomial at a
finite point, and `1` at infinity. -/
noncomputable def placeElt : Place k → RatFunc k
  | none => 1
  | some p => algebraMap k[X] (RatFunc k) p.1

lemma placeElt_ne_zero (P : Place k) : placeElt P ≠ 0 := by
  cases P with
  | none => simp [placeElt]
  | some p => exact algMap_ne_zero p.2.2.ne_zero

/-- The rational function `∏ p ^ D p` attached to a divisor `D` (its finite part). -/
noncomputable def divElt (D : Divisor k) : RatFunc k := ∏ P ∈ D.support, placeElt P ^ D P

lemma divElt_ne_zero (D : Divisor k) : divElt D ≠ 0 :=
  Finset.prod_ne_zero_iff.2 fun P _ => zpow_ne_zero _ (placeElt_ne_zero P)

lemma ord_placeElt_finite (q : {p : k[X] // p.Monic ∧ Irreducible p}) (P : Place k) :
    ord (some q) (placeElt P) = if P = some q then 1 else 0 := by
  cases P with
  | none => simpa [placeElt] using ord_one (some q)
  | some p =>
      have hq : Prime q.1 := q.2.2.prime
      have h : ord (some q) (placeElt (some p)) = multiplicity q.1 p.1 := by
        simpa [ord, placeElt] using ordFin_algebraMap hq p.2.2.ne_zero
      by_cases hpq : p = q
      · subst hpq
        simp [h, multiplicity_self]
      · have hnd : ¬ q.1 ∣ p.1 := by
          intro hdvd
          exact hpq (Subtype.ext (eq_of_monic_of_associated p.2.1 q.2.1
            (q.2.2.associated_of_dvd p.2.2 hdvd).symm))
        simp [h, multiplicity_eq_zero.2 hnd, hpq]

lemma ord_placeElt_infty (P : Place k) :
    ord none (placeElt P) = -degPlace P + (if P = none then 1 else 0) := by
  cases P with
  | none => simp [placeElt, ord, degPlace, RatFunc.intDegree_one]
  | some p => simp [placeElt, ord, degPlace, RatFunc.intDegree_polynomial]

lemma ord_divElt_finite (D : Divisor k) (q : {p : k[X] // p.Monic ∧ Irreducible p}) :
    ord (some q) (divElt D) = D (some q) := by
  classical
  rw [divElt, ord_prod _ _ _ fun P _ => zpow_ne_zero _ (placeElt_ne_zero P)]
  have : ∀ P ∈ D.support, ord (some q) (placeElt P ^ D P) = if P = some q then D P else 0 := by
    intro P _
    rw [ord_zpow _ (placeElt_ne_zero P), ord_placeElt_finite]
    by_cases h : P = some q <;> simp [h]
  rw [Finset.sum_congr rfl this, Finset.sum_ite_eq' D.support (some q) (fun P => D P)]
  by_cases h : (some q : Place k) ∈ D.support
  · simp [h]
  · simp [h, Finsupp.notMem_support_iff.1 h]

lemma ord_divElt_infty (D : Divisor k) :
    ord none (divElt D) = D none - degDiv D := by
  classical
  rw [divElt, ord_prod _ _ _ fun P _ => zpow_ne_zero _ (placeElt_ne_zero P)]
  have h1 : ∀ P ∈ D.support, ord none (placeElt P ^ D P)
      = (if P = none then D P else 0) - D P * degPlace P := by
    intro P _
    rw [ord_zpow _ (placeElt_ne_zero P), ord_placeElt_infty]
    by_cases h : P = none
    · simp [h]
      ring
    · simp [h]
  rw [Finset.sum_congr rfl h1, Finset.sum_sub_distrib,
    Finset.sum_ite_eq' D.support (none : Place k) (fun P => D P)]
  have h2 : degDiv D = ∑ P ∈ D.support, D P * degPlace P := rfl
  rw [h2]
  by_cases h : (none : Place k) ∈ D.support
  · simp [h]
  · simp [h, Finsupp.notMem_support_iff.1 h]

/-- The Riemann–Roch space `L(D) = {f : div f ≥ -D} ∪ {0}` of a divisor `D`, as a set. -/
def RRSet (D : Divisor k) : Set (RatFunc k) := {f | f = 0 ∨ ∀ P : Place k, -D P ≤ ord P f}

/-- The `k`-subspace of `RatFunc k` consisting of the polynomials of degree `< n`. -/
noncomputable def polySub (n : ℕ) : Submodule k (RatFunc k) :=
  (Polynomial.degreeLT k n).map (IsScalarTower.toAlgHom k k[X] (RatFunc k)).toLinearMap

/-- Multiplication by a nonzero rational function, as a `k`-linear automorphism. -/
noncomputable def mulEquiv {a : RatFunc k} (ha : a ≠ 0) : RatFunc k ≃ₗ[k] RatFunc k where
  toFun f := f * a
  map_add' f g := by ring
  map_smul' c f := by simp
  invFun f := f * a⁻¹
  left_inv f := by field_simp
  right_inv f := by field_simp

/-- An auxiliary description of the Riemann–Roch space: `f ∈ L(D)` iff `f · ∏ p ^ D p` is a
polynomial of degree at most `deg D`. -/
noncomputable def RRAux (D : Divisor k) : Submodule k (RatFunc k) :=
  (polySub (degDiv D + 1).toNat).comap (mulEquiv (divElt_ne_zero D)).toLinearMap

lemma ord_infty_algebraMap (g : k[X]) :
    ord none (algebraMap k[X] (RatFunc k) g) = -(g.natDegree : ℤ) := by
  simp [ord, RatFunc.intDegree_polynomial]

/-- A nonzero rational function whose order is nonnegative at every finite closed point is a
polynomial. -/
lemma isPoly_of_ordFin_nonneg {h : RatFunc k} (hh : h ≠ 0)
    (H : ∀ q : k[X], q.Monic → Irreducible q → 0 ≤ ordFin q h) :
    ∃ g : k[X], g ≠ 0 ∧ algebraMap k[X] (RatFunc k) g = h := by
  have hden : h.denom ≠ 0 := RatFunc.denom_ne_zero h
  have hunit : IsUnit h.denom := by
    by_contra hu
    obtain ⟨q, hqm, hqi, hqd⟩ := Polynomial.exists_monic_irreducible_factor h.denom hu
    have hq : Prime q := hqi.prime
    have h1 : multiplicity q h.denom ≠ 0 := fun hc => (multiplicity_eq_zero.1 hc) hqd
    have h2 : multiplicity q h.num = 0 :=
      multiplicity_eq_zero.2 fun hdvd =>
        hq.not_unit ((RatFunc.isCoprime_num_denom h).isUnit_of_dvd' hdvd hqd)
    have h3 := H q hqm hqi
    rw [ordFin, h2] at h3
    omega
  have hd1 : h.denom = 1 := (RatFunc.monic_denom h).eq_one_of_isUnit hunit
  exact ⟨h.num, RatFunc.num_ne_zero hh, by rw [algebraMap_num_eq h, hd1]; simp⟩

lemma mem_polySub_iff (n : ℕ) (x : RatFunc k) :
    x ∈ polySub n ↔ ∃ g : k[X], g.degree < (n : WithBot ℕ) ∧
      algebraMap k[X] (RatFunc k) g = x := by
  constructor
  · rintro ⟨g, hg, rfl⟩
    exact ⟨g, (Polynomial.mem_degreeLT).1 hg, rfl⟩
  · rintro ⟨g, hg, rfl⟩
    exact ⟨g, (Polynomial.mem_degreeLT).2 hg, rfl⟩

lemma mem_RRAux_iff (D : Divisor k) (f : RatFunc k) :
    f ∈ RRAux D ↔ f ∈ RRSet D := by
  have hA : divElt D ≠ 0 := divElt_ne_zero D
  have hmem : f ∈ RRAux D ↔ ∃ g : k[X], g.degree < (((degDiv D + 1).toNat : ℕ) : WithBot ℕ) ∧
      algebraMap k[X] (RatFunc k) g = f * divElt D := by
    rw [RRAux, Submodule.mem_comap, mem_polySub_iff]
    rfl
  rw [hmem, RRSet, Set.mem_setOf_eq]
  by_cases hf : f = 0
  · subst hf
    exact ⟨fun _ => Or.inl rfl, fun _ => ⟨0, by simp, by simp⟩⟩
  constructor
  · rintro ⟨g, hdeg, hg⟩
    right
    have hgne : g ≠ 0 := by
      intro hc
      rw [hc, map_zero] at hg
      exact (mul_ne_zero hf hA) hg.symm
    have hnat : (g.natDegree : ℤ) ≤ degDiv D := by
      have : g.natDegree < (degDiv D + 1).toNat := by
        have := hdeg
        rw [Polynomial.degree_eq_natDegree hgne] at this
        exact_mod_cast this
      omega
    intro P
    cases P with
    | none =>
        have h1 : ord none (f * divElt D) = -(g.natDegree : ℤ) := by
          rw [← hg, ord_infty_algebraMap]
        rw [ord_mul none hf hA, ord_divElt_infty] at h1
        omega
    | some q =>
        have h1 : ord (some q) (f * divElt D) = (multiplicity q.1 g : ℤ) := by
          rw [← hg]
          exact ordFin_algebraMap q.2.2.prime hgne
        rw [ord_mul (some q) hf hA, ord_divElt_finite] at h1
        have : (0 : ℤ) ≤ (multiplicity q.1 g : ℤ) := Int.natCast_nonneg _
        omega
  · rintro (h | h)
    · exact absurd h hf
    · have hfin : ∀ q : k[X], q.Monic → Irreducible q → 0 ≤ ordFin q (f * divElt D) := by
        intro q hqm hqi
        have h1 : ord (some ⟨q, hqm, hqi⟩ : Place k) (f * divElt D) = ordFin q (f * divElt D) := rfl
        have h2 := h (some ⟨q, hqm, hqi⟩)
        have h3 : ord (some ⟨q, hqm, hqi⟩ : Place k) (f * divElt D)
            = ord (some ⟨q, hqm, hqi⟩ : Place k) f + D (some ⟨q, hqm, hqi⟩) := by
          rw [ord_mul _ hf hA, ord_divElt_finite]
        rw [← h1, h3]
        omega
      obtain ⟨g, hgne, hg⟩ := isPoly_of_ordFin_nonneg (mul_ne_zero hf hA) hfin
      refine ⟨g, ?_, hg⟩
      have h1 : ord none (f * divElt D) = -(g.natDegree : ℤ) := by
        rw [← hg, ord_infty_algebraMap]
      rw [ord_mul none hf hA, ord_divElt_infty] at h1
      have h3 := h none
      have hnat : (g.natDegree : ℤ) ≤ degDiv D := by omega
      rw [Polynomial.degree_eq_natDegree hgne]
      have : g.natDegree < (degDiv D + 1).toNat := by omega
      exact_mod_cast this

/-- The Riemann–Roch space `L(D)` of a divisor `D`, as a `k`-subspace of the function field. -/
noncomputable def RRSpace (D : Divisor k) : Submodule k (RatFunc k) :=
  (RRAux D).copy (RRSet D) (by ext f; simpa using (mem_RRAux_iff D f).symm)

/-- `ℓ(D)`, the dimension of the Riemann–Roch space of `D`. -/
noncomputable def ell (D : Divisor k) : ℕ := Module.finrank k (RRSpace D)

/-- The canonical divisor of `ℙ¹_k`: `-2` times the point at infinity. -/
noncomputable def canonicalDivisor (k : Type*) [Field k] : Divisor k := Finsupp.single none (-2)

/-- The genus of `ℙ¹_k`. -/
def genus (k : Type*) [Field k] : ℤ := 0

lemma finrank_polySub (n : ℕ) : Module.finrank k (polySub (k := k) n) = n := by
  have hinj : Function.Injective
      ⇑((IsScalarTower.toAlgHom k k[X] (RatFunc k)).toLinearMap) := fun a b h => algMap_inj a b h
  rw [polySub, ← (Submodule.equivMapOfInjective _ hinj (Polynomial.degreeLT k n)).finrank_eq,
    (Polynomial.degreeLTEquiv k n).finrank_eq]
  simp

/-- Riemann–Roch spaces are finite dimensional, so `ell` really is their dimension. -/
instance finiteDimensional_RRSpace (D : Divisor k) : FiniteDimensional k (RRSpace D) := by
  have h1 : FiniteDimensional k (polySub (k := k) (degDiv D + 1).toNat) :=
    Module.Finite.map _ _
  rw [RRSpace, Submodule.copy_eq, RRAux, Submodule.comap_equiv_eq_map_symm]
  exact Module.Finite.map _ _

lemma ell_eq (D : Divisor k) : (ell D : ℤ) = max (degDiv D + 1) 0 := by
  have h : ell D = (degDiv D + 1).toNat := by
    rw [ell, RRSpace, Submodule.copy_eq, RRAux, Submodule.comap_equiv_eq_map_symm,
      LinearEquiv.finrank_map_eq, finrank_polySub]
  rw [h]
  omega

lemma degDiv_sub (D E : Divisor k) : degDiv (D - E) = degDiv D - degDiv E := by
  simpa [degDiv] using
    Finsupp.sum_sub_index (f := D) (g := E) (h := fun P n => n * degPlace P)
      (fun a b₁ b₂ => by ring)

lemma degDiv_canonical : degDiv (canonicalDivisor k) = 2 * genus k - 2 := by
  rw [canonicalDivisor, degDiv, Finsupp.sum_single_index (by simp)]
  simp [genus, degPlace]

lemma degDiv_zero : degDiv (0 : Divisor k) = 0 := by simp [degDiv]

/-- Sanity check: the only rational functions without poles on `ℙ¹_k` are the constants,
so `ℓ(0) = 1`. -/
lemma ell_zero : ell (0 : Divisor k) = 1 := by
  have h := ell_eq (0 : Divisor k)
  rw [degDiv_zero] at h
  omega

/-- **Riemann–Roch for the smooth projective curve `ℙ¹_k`**:
`ℓ(D) - ℓ(K - D) = deg D + 1 - g`, where `K` is the canonical divisor and `g` the genus. -/
theorem riemann_roch_curve (D : Divisor k) :
    (ell D : ℤ) - (ell (canonicalDivisor k - D) : ℤ) = degDiv D + 1 - genus k := by
  rw [ell_eq, ell_eq, degDiv_sub, degDiv_canonical]
  simp only [genus]
  omega

lemma degDiv_single_infty (n : ℤ) : degDiv (Finsupp.single (none : Place k) n) = n := by
  rw [degDiv, Finsupp.sum_single_index (by simp)]
  simp [degPlace]

/-- Sanity check: `ℓ(n·∞) = n + 1` for `n ≥ 0`: the functions with a pole of order at most `n`
at infinity and no other pole are the polynomials of degree at most `n`. -/
lemma ell_single_infty (n : ℤ) :
    (ell (Finsupp.single (none : Place k) n) : ℤ) = max (n + 1) 0 := by
  rw [ell_eq, degDiv_single_infty]

/-- Riemann's inequality `ℓ(D) ≥ deg D + 1 - g`, a consequence of Riemann–Roch. -/
theorem riemann_inequality (D : Divisor k) : degDiv D + 1 - genus k ≤ (ell D : ℤ) := by
  rw [ell_eq]
  simp [genus]

end Math2

