/-
# Riemann Roch Curve
Category: Frontier Math
Target: Math2.riemann_roch_curve
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/
-- (Lean 4 does not allow a module doc-comment `/-! ... -/` before `import`, so the header
-- above is a plain block comment; it is repeated verbatim as a module docstring below.)

import Mathlib

/-!
# Riemann Roch Curve
Category: Frontier Math
Target: Math2.riemann_roch_curve
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open Polynomial UniqueFactorizationMonoid

namespace Math2

/-!
## The Riemann–Roch theorem, cohomological form

`CurveData Point` bundles the standard cohomological data of a smooth projective curve
whose closed points are indexed by `Point`:

* `ptDeg P` is the degree of the closed point `P`;
* `h0 D` and `h1 D` are `dim H⁰(X, 𝒪(D))` and `dim H¹(X, 𝒪(D))`;
* `canonical` is a canonical divisor `K` and `genus` is the genus `g = dim H¹(X, 𝒪)`;
* `chi_step` is additivity of the Euler characteristic along the exact sequence
  `0 → 𝒪(D) → 𝒪(D+P) → k(P) → 0`;
* `serre_duality` is Serre duality `H¹(D)^∨ ≅ H⁰(K - D)`.
-/

/-- Cohomological data of divisors on a smooth projective curve. -/
structure CurveData (Point : Type*) where
  /-- The degree of a closed point. -/
  ptDeg : Point → ℤ
  /-- `h0 D = dim H⁰(X, 𝒪(D)) = ℓ(D)`. -/
  h0 : (Point →₀ ℤ) → ℤ
  /-- `h1 D = dim H¹(X, 𝒪(D))`. -/
  h1 : (Point →₀ ℤ) → ℤ
  /-- A canonical divisor of the curve. -/
  canonical : Point →₀ ℤ
  /-- The genus of the curve. -/
  genus : ℤ
  /-- `ℓ(0) = 1`: the global regular functions are the constants. -/
  h0_zero : h0 0 = 1
  /-- `dim H¹(X, 𝒪) = g`. -/
  h1_zero : h1 0 = genus
  /-- Additivity of the Euler characteristic along `0 → 𝒪(D) → 𝒪(D+P) → k(P) → 0`. -/
  chi_step : ∀ (D : Point →₀ ℤ) (P : Point),
    h0 (D + Finsupp.single P 1) - h1 (D + Finsupp.single P 1) = (h0 D - h1 D) + ptDeg P
  /-- Serre duality. -/
  serre_duality : ∀ D, h1 D = h0 (canonical - D)

namespace CurveData

variable {Point : Type*} (C : CurveData Point)

/-- The degree of a divisor. -/
def deg (D : Point →₀ ℤ) : ℤ := D.sum fun P n => n * C.ptDeg P

/-- The Euler characteristic `χ(D) = h⁰(D) - h¹(D)`. -/
def chi (D : Point →₀ ℤ) : ℤ := C.h0 D - C.h1 D

@[simp] lemma deg_zero : C.deg 0 = 0 := by simp [deg]

lemma deg_add_single (D : Point →₀ ℤ) (P : Point) (n : ℤ) :
    C.deg (D + Finsupp.single P n) = C.deg D + n * C.ptDeg P := by
  classical
  simp only [deg]
  rw [Finsupp.sum_add_index' (by intro a; simp) (by intro a b₁ b₂; ring)]
  simp [Finsupp.sum_single_index]

lemma chi_add_single (D : Point →₀ ℤ) (P : Point) (n : ℤ) :
    C.chi (D + Finsupp.single P n) = C.chi D + n * C.ptDeg P := by
  have step : ∀ (E : Point →₀ ℤ), C.chi (E + Finsupp.single P 1) = C.chi E + C.ptDeg P := by
    intro E
    have := C.chi_step E P
    simpa [chi] using this
  induction n using Int.induction_on with
  | zero => simp
  | succ m ih =>
      have : D + Finsupp.single P ((m : ℤ) + 1)
          = (D + Finsupp.single P (m : ℤ)) + Finsupp.single P 1 := by
        rw [add_assoc, ← Finsupp.single_add]
      rw [this, step, ih]; ring
  | pred m ih =>
      have h1 : (D + Finsupp.single P (-(m : ℤ) - 1)) + Finsupp.single P 1
          = D + Finsupp.single P (-(m : ℤ)) := by
        rw [add_assoc, ← Finsupp.single_add]; ring_nf
      have := step (D + Finsupp.single P (-(m : ℤ) - 1))
      rw [h1, ih] at this
      have hexp : (-(m : ℤ) - 1) * C.ptDeg P = -(m : ℤ) * C.ptDeg P - C.ptDeg P := by ring
      rw [hexp]
      omega

lemma chi_eq (D : Point →₀ ℤ) : C.chi D = C.deg D + 1 - C.genus := by
  classical
  induction D using Finsupp.induction with
  | zero => simp [chi, C.h0_zero, C.h1_zero]
  | single_add P n E hP hn ih =>
      rw [add_comm (Finsupp.single P n) E, C.chi_add_single, C.deg_add_single, ih]; ring

end CurveData

/-- **Riemann–Roch for a smooth projective curve** (cohomological form):
`ℓ(D) - ℓ(K - D) = deg D + 1 - g`. -/
theorem riemann_roch_curve {Point : Type*} (C : CurveData Point) (D : Point →₀ ℤ) :
    C.h0 D - C.h0 (C.canonical - D) = C.deg D + 1 - C.genus := by
  have h := C.chi_eq D
  rw [CurveData.chi, C.serre_duality D] at h
  exact h

/-- The degree of a canonical divisor is `2g - 2`; a consequence of Riemann–Roch applied to
`D = K`. -/
theorem CurveData.deg_canonical {Point : Type*} (C : CurveData Point) :
    C.deg C.canonical = 2 * C.genus - 2 := by
  have h := riemann_roch_curve C C.canonical
  rw [sub_self, C.h0_zero] at h
  have hK : C.h0 C.canonical = C.genus := by
    have := C.serre_duality 0
    rw [C.h1_zero, sub_zero] at this
    exact this.symm
  rw [hK] at h
  omega

end Math2

import RequestProject.RiemannRochCurve

/-!
# The projective line and its Riemann–Roch theorem

We realise the smooth projective curve `ℙ¹` over an arbitrary field `k` through its function
field `k(t) = RatFunc k`.  Its closed points are the monic irreducible polynomials
(the finite points) together with the point at infinity.  We define the order of vanishing
`ord P f` of a rational function at a place, the Riemann–Roch space
`L(D) = {f | f = 0 ∨ ∀ P, ord P f ≥ -D P}`, and prove `ℓ(D) = max (deg D + 1) 0`.
-/

open Polynomial
open scoped Classical

namespace Math2
namespace P1

variable (k : Type*) [Field k]

/-- Monic irreducible polynomials: the finite closed points of `ℙ¹`. -/
abbrev MonicIrr := {p : k[X] // p.Monic ∧ Irreducible p}

/-- Closed points of `ℙ¹` over `k`: a monic irreducible polynomial, or the point at
infinity (`none`). -/
abbrev Place := Option (MonicIrr k)

/-- Divisors on `ℙ¹`. -/
abbrev Divisor := Place k →₀ ℤ

variable {k}

lemma MonicIrr.prime (p : MonicIrr k) : Prime p.1 := p.2.2.prime

lemma MonicIrr.ne_zero (p : MonicIrr k) : p.1 ≠ 0 := p.2.2.ne_zero

/-- The degree of a closed point. -/
def placeDeg : Place k → ℤ
  | none => 1
  | some p => (p.1.natDegree : ℤ)

/-- The rational function attached to a finite place (and `1` at infinity). -/
noncomputable def placeElt : Place k → RatFunc k
  | none => 1
  | some p => algebraMap k[X] (RatFunc k) p.1

/-- The multiplicity of a monic irreducible polynomial in a polynomial. -/
noncomputable def cnt (p : MonicIrr k) (q : k[X]) : ℤ := (multiplicity p.1 q : ℤ)

/-- The order of vanishing of a rational function at a place of `ℙ¹`. -/
noncomputable def ord : Place k → RatFunc k → ℤ
  | none, f => - f.intDegree
  | some p, f => cnt p f.num - cnt p f.denom

/-- The degree of a divisor. -/
noncomputable def degDiv (D : Divisor k) : ℤ := D.sum fun P n => n * placeDeg P

/-! ### Basic properties of `cnt` -/

lemma finiteMultiplicity_of_ne_zero (p : MonicIrr k) {q : k[X]} (hq : q ≠ 0) :
    FiniteMultiplicity p.1 q :=
  FiniteMultiplicity.of_prime_left p.prime hq

lemma cnt_nonneg (p : MonicIrr k) (q : k[X]) : 0 ≤ cnt p q := Int.natCast_nonneg _

lemma cnt_mul (p : MonicIrr k) {q r : k[X]} (hq : q ≠ 0) (hr : r ≠ 0) :
    cnt p (q * r) = cnt p q + cnt p r := by
  simp only [cnt]
  rw [multiplicity_mul p.prime (finiteMultiplicity_of_ne_zero p (mul_ne_zero hq hr))]
  push_cast
  ring

@[simp] lemma cnt_one (p : MonicIrr k) : cnt p 1 = 0 := by
  simp only [cnt, Nat.cast_eq_zero]
  exact multiplicity_eq_zero.mpr fun h => p.2.2.not_isUnit (isUnit_of_dvd_one h)

lemma cnt_eq_zero_of_not_dvd (p : MonicIrr k) {q : k[X]} (h : ¬ p.1 ∣ q) : cnt p q = 0 := by
  simp only [cnt, Nat.cast_eq_zero]
  exact multiplicity_eq_zero.mpr h

lemma one_le_cnt_of_dvd (p : MonicIrr k) {q : k[X]} (h : p.1 ∣ q) : 1 ≤ cnt p q := by
  simp only [cnt]
  exact_mod_cast multiplicity_pos_of_dvd h

lemma cnt_self (p : MonicIrr k) : cnt p p.1 = 1 := by
  simp [cnt, multiplicity_self]

lemma cnt_of_ne (p q : MonicIrr k) (h : p ≠ q) : cnt p q.1 = 0 := by
  refine cnt_eq_zero_of_not_dvd p ?_
  intro hdvd
  refine h (Subtype.ext ?_)
  have hassoc : Associated (p.1) (q.1) :=
    ((q.2.2.dvd_iff.mp hdvd).resolve_left (fun hu => p.2.2.not_isUnit hu)).symm
  exact eq_of_monic_of_associated p.2.1 q.2.1 hassoc

/-! ### Basic properties of `ord` -/

@[simp] lemma ord_one (P : Place k) : ord P (1 : RatFunc k) = 0 := by
  cases P with
  | none => simp [ord]
  | some p => simp [ord]

lemma ord_mul (P : Place k) {f g : RatFunc k} (hf : f ≠ 0) (hg : g ≠ 0) :
    ord P (f * g) = ord P f + ord P g := by
  cases P with
  | none =>
      simp only [ord, RatFunc.intDegree_mul hf hg]; ring
  | some p =>
      have hfg : f * g ≠ 0 := mul_ne_zero hf hg
      have h := RatFunc.num_denom_mul f g
      have h1 : cnt p ((f * g).num * (f.denom * g.denom))
          = cnt p (f.num * g.num * (f * g).denom) := by rw [h]
      rw [cnt_mul p (RatFunc.num_ne_zero hfg)
            (mul_ne_zero (RatFunc.denom_ne_zero f) (RatFunc.denom_ne_zero g)),
          cnt_mul p (RatFunc.denom_ne_zero f) (RatFunc.denom_ne_zero g),
          cnt_mul p (mul_ne_zero (RatFunc.num_ne_zero hf) (RatFunc.num_ne_zero hg))
            (RatFunc.denom_ne_zero (f * g)),
          cnt_mul p (RatFunc.num_ne_zero hf) (RatFunc.num_ne_zero hg)] at h1
      simp only [ord]
      linarith

lemma ord_inv (P : Place k) {f : RatFunc k} (hf : f ≠ 0) : ord P f⁻¹ = - ord P f := by
  have h : ord P (f * f⁻¹) = ord P f + ord P f⁻¹ := ord_mul P hf (inv_ne_zero hf)
  rw [mul_inv_cancel₀ hf, ord_one] at h
  linarith

lemma ord_zpow (P : Place k) {f : RatFunc k} (hf : f ≠ 0) (n : ℤ) :
    ord P (f ^ n) = n * ord P f := by
  induction n using Int.induction_on with
  | zero => simp
  | succ m ih =>
      rw [zpow_add₀ hf, ord_mul P (zpow_ne_zero _ hf) (by simpa using hf), ih, zpow_one]
      ring
  | pred m ih =>
      have hsplit : ((-(m : ℤ) - 1)) = (-(m : ℤ)) + (-1) := by ring
      rw [hsplit, zpow_add₀ hf, ord_mul P (zpow_ne_zero _ hf) (zpow_ne_zero _ hf), ih,
        zpow_neg, zpow_one, ord_inv P hf]
      ring

lemma ord_prod {ι : Type*} (P : Place k) (s : Finset ι) (F : ι → RatFunc k)
    (h : ∀ i ∈ s, F i ≠ 0) : ord P (∏ i ∈ s, F i) = ∑ i ∈ s, ord P (F i) := by
  classical
  induction s using Finset.induction with
  | empty => simp
  | insert a s ha ih =>
      rw [Finset.prod_insert ha, Finset.sum_insert ha,
        ord_mul P (h a (Finset.mem_insert_self a s))
          (Finset.prod_ne_zero_iff.mpr fun i hi => h i (Finset.mem_insert_of_mem hi)),
        ih fun i hi => h i (Finset.mem_insert_of_mem hi)]

/-! ### Orders of the elements attached to places -/

lemma placeElt_ne_zero (P : Place k) : placeElt P ≠ 0 := by
  cases P with
  | none => simp [placeElt]
  | some p => exact RatFunc.algebraMap_ne_zero p.ne_zero

lemma ord_some_placeElt (q : MonicIrr k) (P : Place k) :
    ord (some q) (placeElt P) = if P = some q then 1 else 0 := by
  cases P with
  | none => simp [placeElt]
  | some p =>
      simp only [placeElt, ord, RatFunc.num_algebraMap, RatFunc.denom_algebraMap, cnt_one, sub_zero]
      by_cases h : p = q
      · subst h; simp [cnt_self]
      · simp [cnt_of_ne q p (Ne.symm h), h]

lemma ord_none_placeElt (P : Place k) :
    ord none (placeElt P) = if P = none then 0 else - placeDeg P := by
  cases P with
  | none => simp [placeElt]
  | some p => simp [placeElt, ord, placeDeg, RatFunc.intDegree_polynomial]

/-- The rational function `∏ p ^ D p` attached to a divisor (finite places only). -/
noncomputable def aDiv (D : Divisor k) : RatFunc k := D.prod fun P n => (placeElt P) ^ n

lemma aDiv_ne_zero (D : Divisor k) : aDiv D ≠ 0 := by
  refine Finset.prod_ne_zero_iff.mpr fun P _ => zpow_ne_zero _ (placeElt_ne_zero P)

lemma ord_aDiv (Q : Place k) (D : Divisor k) :
    ord Q (aDiv D) = ∑ P ∈ D.support, D P * ord Q (placeElt P) := by
  rw [aDiv, Finsupp.prod,
    ord_prod Q _ _ fun P _ => zpow_ne_zero _ (placeElt_ne_zero P)]
  exact Finset.sum_congr rfl fun P _ => ord_zpow Q (placeElt_ne_zero P) _

lemma ord_some_aDiv (q : MonicIrr k) (D : Divisor k) :
    ord (some q) (aDiv D) = D (some q) := by
  classical
  rw [ord_aDiv]
  have : ∀ P ∈ D.support, D P * ord (some q) (placeElt P) = if P = some q then D P else 0 := by
    intro P _
    rw [ord_some_placeElt]
    by_cases h : P = some q <;> simp [h]
  rw [Finset.sum_congr rfl this, Finset.sum_ite_eq' D.support (some q) (fun P => D P)]
  by_cases h : (some q : Place k) ∈ D.support
  · simp [h]
  · simp [h, Finsupp.notMem_support_iff.mp h]

lemma ord_none_aDiv (D : Divisor k) : ord none (aDiv D) = D none - degDiv D := by
  classical
  have key : ord none (aDiv D) + degDiv D = D none := by
    rw [ord_aDiv, degDiv, Finsupp.sum, ← Finset.sum_add_distrib]
    have : ∀ P ∈ D.support,
        D P * ord none (placeElt P) + D P * placeDeg P = if P = none then D P else 0 := by
      intro P _
      rw [ord_none_placeElt]
      by_cases h : P = none <;> simp [h, placeDeg]
    rw [Finset.sum_congr rfl this, Finset.sum_ite_eq' D.support (none : Place k) (fun P => D P)]
    by_cases h : (none : Place k) ∈ D.support
    · simp [h]
    · simp [h, Finsupp.notMem_support_iff.mp h]
  linarith

/-! ### Rational functions that are polynomials -/

lemma exists_monicIrr_dvd {d : k[X]} (hd0 : d ≠ 0) (hdu : ¬ IsUnit d) :
    ∃ p : MonicIrr k, p.1 ∣ d := by
  obtain ⟨i, hi, hid⟩ := WfDvdMonoid.exists_irreducible_factor hdu hd0
  have hu : IsUnit (C (i.leadingCoeff)⁻¹) :=
    isUnit_C.mpr (IsUnit.mk0 _ (inv_ne_zero (leadingCoeff_ne_zero.mpr hi.ne_zero)))
  exact ⟨⟨i * C (i.leadingCoeff)⁻¹, monic_mul_leadingCoeff_inv hi.ne_zero,
    irreducible_mul_leadingCoeff_inv.mpr hi⟩, (hu.mul_right_dvd).mpr hid⟩

lemma isPoly_iff {f : RatFunc k} (hf : f ≠ 0) :
    (∀ q : MonicIrr k, 0 ≤ ord (some q) f) ↔ ∃ g : k[X], f = algebraMap k[X] (RatFunc k) g := by
  constructor
  · intro h
    have hden : f.denom = 1 := by
      by_contra hne
      have hdu : ¬ IsUnit f.denom := fun hu => hne (f.monic_denom.eq_one_of_isUnit hu)
      obtain ⟨p, hp⟩ := exists_monicIrr_dvd (RatFunc.denom_ne_zero f) hdu
      have h1 : 1 ≤ cnt p f.denom := one_le_cnt_of_dvd p hp
      have h2 : cnt p f.num = 0 := by
        refine cnt_eq_zero_of_not_dvd p fun hdvd => ?_
        exact p.2.2.not_isUnit ((RatFunc.isCoprime_num_denom f).isUnit_of_dvd' hdvd hp)
      have := h p
      simp only [ord, h2] at this
      linarith
    refine ⟨f.num, ?_⟩
    have := RatFunc.num_div_denom f
    rw [hden] at this
    simpa using this.symm
  · rintro ⟨g, rfl⟩ q
    simp only [ord, RatFunc.num_algebraMap, RatFunc.denom_algebraMap, cnt_one, sub_zero]
    exact cnt_nonneg q g

/-! ### Spaces of polynomials of bounded degree -/

variable (k) in
/-- Polynomials of degree at most `m` (the zero submodule when `m < 0`). -/
noncomputable def polyLE (m : ℤ) : Submodule k k[X] :=
  if 0 ≤ m then degreeLT k (m.toNat + 1) else ⊥

lemma mem_polyLE {m : ℤ} {g : k[X]} :
    g ∈ polyLE k m ↔ (g = 0 ∨ (g.natDegree : ℤ) ≤ m) := by
  unfold polyLE
  split_ifs with hm
  · rcases eq_or_ne g 0 with rfl | hg
    · simp
    · rw [mem_degreeLT, degree_eq_natDegree hg]
      constructor
      · intro h
        have h' : g.natDegree < m.toNat + 1 := by exact_mod_cast h
        right; omega
      · rintro (rfl | h)
        · exact absurd rfl hg
        · have h' : g.natDegree < m.toNat + 1 := by omega
          exact_mod_cast h'
  · simp only [Submodule.mem_bot]
    constructor
    · intro h; exact Or.inl h
    · rintro (rfl | h)
      · rfl
      · have : (0 : ℤ) ≤ (g.natDegree : ℤ) := Int.natCast_nonneg _
        omega

lemma finrank_polyLE (m : ℤ) : Module.finrank k (polyLE k m) = (max (m + 1) 0).toNat := by
  by_cases hm : 0 ≤ m
  · have h : Module.finrank k (degreeLT k (m.toNat + 1)) = m.toNat + 1 := by
      simpa using (degreeLTEquiv k (m.toNat + 1)).finrank_eq
    rw [polyLE, if_pos hm, h]
    omega
  · rw [polyLE, if_neg hm, finrank_bot]
    omega

/-! ### The Riemann–Roch space -/

/-- Multiplication by `c`, viewed as a `k`-linear map from polynomials to rational
functions. -/
noncomputable def emb (c : RatFunc k) : k[X] →ₗ[k] RatFunc k :=
  (LinearMap.mulLeft k c).comp (IsScalarTower.toAlgHom k k[X] (RatFunc k)).toLinearMap

@[simp] lemma emb_apply (c : RatFunc k) (g : k[X]) :
    emb c g = c * algebraMap k[X] (RatFunc k) g := rfl

lemma emb_injective {c : RatFunc k} (hc : c ≠ 0) : Function.Injective (emb c) := by
  intro g h hgh
  simp only [emb_apply] at hgh
  exact RatFunc.algebraMap_injective k (mul_left_cancel₀ hc hgh)

/-- The Riemann–Roch space `L(D) = {f | f = 0 ∨ ∀ P, ord P f ≥ -D P}`, as a `k`-subspace of
the function field. -/
noncomputable def RRspace (D : Divisor k) : Submodule k (RatFunc k) :=
  (polyLE k (degDiv D)).map (emb (aDiv D)⁻¹)

/-- The defining property of the Riemann–Roch space: `f ∈ L(D)` iff `div f + D ≥ 0`. -/
theorem mem_RRspace_iff (D : Divisor k) (f : RatFunc k) :
    f ∈ RRspace D ↔ (f = 0 ∨ ∀ P : Place k, - D P ≤ ord P f) := by
  have ha : aDiv D ≠ 0 := aDiv_ne_zero D
  have hainv : (aDiv D)⁻¹ ≠ 0 := inv_ne_zero ha
  constructor
  · rintro ⟨g, hg, rfl⟩
    rcases eq_or_ne g 0 with rfl | hg0
    · left; simp
    right
    intro P
    have hgne : algebraMap k[X] (RatFunc k) g ≠ 0 := RatFunc.algebraMap_ne_zero hg0
    have hord : ord P (emb (aDiv D)⁻¹ g)
        = ord P (algebraMap k[X] (RatFunc k) g) - ord P (aDiv D) := by
      rw [emb_apply, ord_mul P hainv hgne, ord_inv P ha]; ring
    have hdeg : (g.natDegree : ℤ) ≤ degDiv D := (mem_polyLE.mp hg).resolve_left hg0
    cases P with
    | none =>
        rw [hord, ord_none_aDiv]
        have : ord none (algebraMap k[X] (RatFunc k) g) = - (g.natDegree : ℤ) := by
          simp [ord, RatFunc.intDegree_polynomial]
        rw [this]
        omega
    | some q =>
        rw [hord, ord_some_aDiv]
        have : ord (some q) (algebraMap k[X] (RatFunc k) g) = cnt q g := by
          simp [ord]
        rw [this]
        have := cnt_nonneg q g
        omega
  · rintro (rfl | h)
    · exact Submodule.zero_mem _
    by_cases hf : f = 0
    · subst hf; exact Submodule.zero_mem _
    have hprod : aDiv D * f ≠ 0 := mul_ne_zero ha hf
    have hordprod : ∀ P : Place k, ord P (aDiv D * f) = ord P (aDiv D) + ord P f :=
      fun P => ord_mul P ha hf
    obtain ⟨g, hg⟩ : ∃ g : k[X], aDiv D * f = algebraMap k[X] (RatFunc k) g := by
      refine (isPoly_iff hprod).mp fun q => ?_
      rw [hordprod, ord_some_aDiv]
      have := h (some q)
      omega
    have hg0 : g ≠ 0 := by
      intro h0
      rw [h0] at hg
      simp only [map_zero] at hg
      exact hprod hg
    refine ⟨g, ?_, ?_⟩
    · refine mem_polyLE.mpr (Or.inr ?_)
      have h1 : ord none (algebraMap k[X] (RatFunc k) g) = - (g.natDegree : ℤ) := by
        simp [ord, RatFunc.intDegree_polynomial]
      have h2 := hordprod none
      rw [hg, h1, ord_none_aDiv] at h2
      have := h none
      omega
    · rw [emb_apply, ← hg, ← mul_assoc, inv_mul_cancel₀ ha, one_mul]

/-- `ℓ(D)`, the dimension of the Riemann–Roch space of `D`. -/
noncomputable def ell (D : Divisor k) : ℤ := (Module.finrank k (RRspace D) : ℤ)

/-- On `ℙ¹` one has `ℓ(D) = max (deg D + 1) 0`. -/
theorem ell_eq (D : Divisor k) : ell D = max (degDiv D + 1) 0 := by
  have hinj : Function.Injective (emb (aDiv D)⁻¹) := emb_injective (inv_ne_zero (aDiv_ne_zero D))
  have hequiv := Submodule.equivMapOfInjective (emb (aDiv D)⁻¹) hinj (polyLE k (degDiv D))
  have : Module.finrank k (RRspace D) = Module.finrank k (polyLE k (degDiv D)) :=
    (hequiv.finrank_eq).symm
  rw [ell, this, finrank_polyLE]
  omega

/-! ### Degrees of divisors -/

@[simp] lemma degDiv_zero : degDiv (0 : Divisor k) = 0 := by simp [degDiv]

lemma degDiv_add (D E : Divisor k) : degDiv (D + E) = degDiv D + degDiv E := by
  simp only [degDiv]
  exact Finsupp.sum_add_index' (by intro a; simp) (by intro a b₁ b₂; ring)

@[simp] lemma degDiv_single (P : Place k) (n : ℤ) :
    degDiv (Finsupp.single P n) = n * placeDeg P := by
  simp [degDiv, Finsupp.sum_single_index]

lemma degDiv_neg (D : Divisor k) : degDiv (-D) = - degDiv D := by
  have h := degDiv_add D (-D)
  rw [add_neg_cancel, degDiv_zero] at h
  linarith

lemma degDiv_sub (D E : Divisor k) : degDiv (D - E) = degDiv D - degDiv E := by
  rw [sub_eq_add_neg, degDiv_add, degDiv_neg, sub_eq_add_neg]

/-! ### The canonical divisor and Riemann–Roch for `ℙ¹` -/

variable (k) in
/-- The canonical divisor of `ℙ¹`, namely `-2` times the point at infinity;
it is the divisor of the rational differential `dt`. -/
noncomputable def canonicalDiv : Divisor k := Finsupp.single none (-2)

@[simp] lemma degDiv_canonicalDiv : degDiv (canonicalDiv k) = -2 := by
  rw [canonicalDiv, degDiv_single]
  norm_num [placeDeg]

/-- **Riemann–Roch for the projective line** (genus `0`, canonical divisor `-2·∞`):
`ℓ(D) - ℓ(K - D) = deg D + 1 - g`. -/
theorem riemann_roch_P1 (D : Divisor k) :
    ell D - ell (canonicalDiv k - D) = degDiv D + 1 - 0 := by
  rw [ell_eq, ell_eq, degDiv_sub, degDiv_canonicalDiv]
  omega

variable (k) in
/-- The projective line as an instance of the abstract cohomological curve data:
genus `0`, canonical divisor `-2·∞`, `h⁰(D) = ℓ(D)` and `h¹(D) = ℓ(K - D)`.
Every axiom is proved unconditionally, so the hypotheses of `Math2.riemann_roch_curve`
are consistent. -/
noncomputable def P1Curve : CurveData (Place k) where
  ptDeg := placeDeg
  h0 := ell
  h1 := fun D => ell (canonicalDiv k - D)
  canonical := canonicalDiv k
  genus := 0
  h0_zero := by rw [ell_eq, degDiv_zero]; rfl
  h1_zero := by rw [sub_zero, ell_eq, degDiv_canonicalDiv]; rfl
  chi_step := by
    intro D P
    have h1 := riemann_roch_P1 (D + Finsupp.single P 1)
    have h2 := riemann_roch_P1 D
    rw [degDiv_add, degDiv_single] at h1
    omega
  serre_duality := fun _ => rfl

@[simp] lemma P1Curve_deg (D : Divisor k) : (P1Curve k).deg D = degDiv D := rfl

/-- The Riemann–Roch theorem for `ℙ¹`, obtained from the general theorem
`Math2.riemann_roch_curve` applied to the (unconditionally constructed) curve data of the
projective line. -/
theorem riemann_roch_P1' (D : Divisor k) :
    (P1Curve k).h0 D - (P1Curve k).h0 ((P1Curve k).canonical - D)
      = (P1Curve k).deg D + 1 - (P1Curve k).genus :=
  riemann_roch_curve (P1Curve k) D

end P1
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

