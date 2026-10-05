import Mathlib

/-!
# Riemann Roch Curve
Category: Frontier Math
Target: Math2.riemann_roch_curve
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

/-!
## Riemann–Roch for the smooth projective curve `ℙ¹`

We develop, from scratch, the divisor theory of the smooth projective curve `ℙ¹` over an
algebraically closed field `k`, whose function field is `RatFunc k`.

* The closed points (places) of `ℙ¹` are the elements of `k` together with the point at
  infinity; this is modelled by `Math2.Place k := Option k` (`none` is the point at infinity).
  Algebraic closedness of `k` is what makes this list of places complete.
* For every place `P` we have the normalized order (valuation) function `Math2.ord P`.
* Divisors are finitely supported `ℤ`-valued functions on places, of degree the sum of their
  coefficients (every closed point of `ℙ¹` over an algebraically closed field has degree one).
* `Math2.LSpace D` is the Riemann–Roch space `L(D) = {f | div f + D ≥ 0} ∪ {0}` and
  `Math2.ell D = ℓ(D)` is its dimension over `k`.
* `Math2.canonical k = -2 ⬝ ∞` is the canonical divisor (the divisor of the differential `dX`)
  and the genus is `g = ℓ(K)`.

The main theorem `Math2.riemann_roch_curve` is `ℓ(D) - ℓ(K - D) = deg D + 1 - g`.
-/

namespace Math2

open Polynomial RatFunc

variable {k : Type*} [Field k]

/-- The closed points of `ℙ¹` over an algebraically closed field `k`: the elements of `k`,
together with the point at infinity `none`. -/
abbrev Place (k : Type*) : Type _ := Option k

/-- The normalized valuation of a rational function at a place of `ℙ¹`:
at a point `a ∈ k` it is the order of vanishing at `a`, at `∞` it is minus the degree. -/
noncomputable def ord : Place k → RatFunc k → ℤ
  | none, f => -f.intDegree
  | some a, f => (f.num.rootMultiplicity a : ℤ) - (f.denom.rootMultiplicity a : ℤ)

@[simp] lemma ord_none (f : RatFunc k) : ord none f = -f.intDegree := rfl

@[simp] lemma ord_some (a : k) (f : RatFunc k) :
    ord (some a) f = (f.num.rootMultiplicity a : ℤ) - (f.denom.rootMultiplicity a : ℤ) := rfl

@[simp] lemma ord_zero (P : Place k) : ord P (0 : RatFunc k) = 0 := by
  cases P <;> simp [ord]

lemma algebraMap_ne_zero_iff {p : k[X]} :
    algebraMap k[X] (RatFunc k) p = 0 ↔ p = 0 := by
  constructor
  · intro h
    exact (RatFunc.algebraMap_injective k) (by simpa using h)
  · rintro rfl; simp

/-- Order at a finite place, computed from an arbitrary representation as a quotient. -/
lemma ord_some_div (a : k) {p q : k[X]} (hp : p ≠ 0) (hq : q ≠ 0) :
    ord (some a)
        (algebraMap k[X] (RatFunc k) p / algebraMap k[X] (RatFunc k) q)
      = (p.rootMultiplicity a : ℤ) - (q.rootMultiplicity a : ℤ) := by
  set f : RatFunc k := algebraMap k[X] (RatFunc k) p / algebraMap k[X] (RatFunc k) q with hf
  have hq' : algebraMap k[X] (RatFunc k) q ≠ 0 := by
    simpa [algebraMap_ne_zero_iff] using hq
  have hd' : algebraMap k[X] (RatFunc k) f.denom ≠ 0 := by
    simpa [algebraMap_ne_zero_iff] using f.denom_ne_zero
  have hcross : algebraMap k[X] (RatFunc k) p * algebraMap k[X] (RatFunc k) f.denom
      = algebraMap k[X] (RatFunc k) f.num * algebraMap k[X] (RatFunc k) q := by
    have h1 : algebraMap k[X] (RatFunc k) f.num / algebraMap k[X] (RatFunc k) f.denom = f :=
      f.num_div_denom
    rw [← h1] at hf
    field_simp at hf
    linear_combination hf
  have hcross' : p * f.denom = f.num * q := by
    apply RatFunc.algebraMap_injective k
    push_cast [map_mul] at hcross ⊢
    exact hcross
  have hnum : f.num ≠ 0 := by
    intro h
    rw [h] at hcross'
    simp only [zero_mul] at hcross'
    exact hp (by simpa [hq] using mul_eq_zero.1 hcross' |>.resolve_right f.denom_ne_zero)
  have h1 : (p * f.denom).rootMultiplicity a = (f.num * q).rootMultiplicity a := by
    rw [hcross']
  rw [Polynomial.rootMultiplicity_mul (by simp [hp, f.denom_ne_zero]),
    Polynomial.rootMultiplicity_mul (by simp [hnum, hq])] at h1
  simp only [ord_some]
  omega

/-- Order at the place at infinity, computed from an arbitrary representation as a quotient. -/
lemma ord_none_div {p q : k[X]} (hp : p ≠ 0) (hq : q ≠ 0) :
    ord none (algebraMap k[X] (RatFunc k) p / algebraMap k[X] (RatFunc k) q)
      = (q.natDegree : ℤ) - (p.natDegree : ℤ) := by
  have hp' : algebraMap k[X] (RatFunc k) p ≠ 0 := by
    simpa [algebraMap_ne_zero_iff] using hp
  have hq' : algebraMap k[X] (RatFunc k) q ≠ 0 := by
    simpa [algebraMap_ne_zero_iff] using hq
  have : (algebraMap k[X] (RatFunc k) p / algebraMap k[X] (RatFunc k) q).intDegree
      = (p.natDegree : ℤ) - q.natDegree := by
    rw [div_eq_mul_inv, RatFunc.intDegree_mul hp' (inv_ne_zero hq'), RatFunc.intDegree_inv,
      RatFunc.intDegree_polynomial, RatFunc.intDegree_polynomial]
    ring
  rw [ord_none, this]
  ring

lemma ord_algebraMap_some (a : k) {p : k[X]} (hp : p ≠ 0) :
    ord (some a) (algebraMap k[X] (RatFunc k) p) = (p.rootMultiplicity a : ℤ) := by
  have := ord_some_div a hp (q := (1 : k[X])) one_ne_zero
  simpa using this

lemma ord_algebraMap_none {p : k[X]} (hp : p ≠ 0) :
    ord none (algebraMap k[X] (RatFunc k) p) = -(p.natDegree : ℤ) := by
  have := ord_none_div hp (q := (1 : k[X])) one_ne_zero
  simpa using this

lemma ord_mul {f g : RatFunc k} (hf : f ≠ 0) (hg : g ≠ 0) (P : Place k) :
    ord P (f * g) = ord P f + ord P g := by
  have hfn : f.num ≠ 0 := RatFunc.num_ne_zero hf
  have hgn : g.num ≠ 0 := RatFunc.num_ne_zero hg
  have hfd : f.denom ≠ 0 := f.denom_ne_zero
  have hgd : g.denom ≠ 0 := g.denom_ne_zero
  have hrep : f * g = algebraMap k[X] (RatFunc k) (f.num * g.num) /
      algebraMap k[X] (RatFunc k) (f.denom * g.denom) := by
    rw [map_mul, map_mul, ← f.num_div_denom, ← g.num_div_denom]
    rw [RatFunc.num_div_denom, RatFunc.num_div_denom]
    field_simp
  cases P with
  | none =>
      rw [hrep, ord_none_div (mul_ne_zero hfn hgn) (mul_ne_zero hfd hgd)]
      rw [Polynomial.natDegree_mul hfd hgd, Polynomial.natDegree_mul hfn hgn]
      simp only [ord_none, RatFunc.intDegree]
      push_cast
      ring
  | some a =>
      rw [hrep, ord_some_div a (mul_ne_zero hfn hgn) (mul_ne_zero hfd hgd)]
      rw [Polynomial.rootMultiplicity_mul (mul_ne_zero hfd hgd),
        Polynomial.rootMultiplicity_mul (mul_ne_zero hfn hgn)]
      simp only [ord_some]
      push_cast
      ring

lemma ord_one (P : Place k) : ord P (1 : RatFunc k) = 0 := by
  cases P <;> simp [ord]

lemma ord_inv {f : RatFunc k} (hf : f ≠ 0) (P : Place k) : ord P f⁻¹ = -ord P f := by
  have h := ord_mul (f := f) (g := f⁻¹) hf (inv_ne_zero hf) P
  rw [mul_inv_cancel₀ hf, ord_one] at h
  omega

lemma ord_zpow {f : RatFunc k} (hf : f ≠ 0) (n : ℤ) (P : Place k) :
    ord P (f ^ n) = n * ord P f := by
  induction n using Int.induction_on with
  | hz => simp [ord_one]
  | hp i ih =>
      have hpow : f ^ (i : ℤ) ≠ 0 := zpow_ne_zero _ hf
      rw [show ((i : ℤ) + 1) = (i : ℤ) + 1 from rfl, zpow_add₀ hf, ord_mul hpow (by simpa using hf),
        ih]
      simp [zpow_one]
      ring
  | hn i ih =>
      have hpow : f ^ (-(i : ℤ)) ≠ 0 := zpow_ne_zero _ hf
      rw [show (-(i : ℤ) - 1) = -(i : ℤ) + (-1) by ring, zpow_add₀ hf, ord_mul hpow (by
        simpa using zpow_ne_zero (-1 : ℤ) hf), ih]
      rw [zpow_neg, zpow_one, ord_inv hf]
      ring

lemma ord_add_ge {f g : RatFunc k} (hf : f ≠ 0) (hg : g ≠ 0) (hfg : f + g ≠ 0) (P : Place k) :
    min (ord P f) (ord P g) ≤ ord P (f + g) := by
  have hfn : f.num ≠ 0 := RatFunc.num_ne_zero hf
  have hgn : g.num ≠ 0 := RatFunc.num_ne_zero hg
  have hfd : f.denom ≠ 0 := f.denom_ne_zero
  have hgd : g.denom ≠ 0 := g.denom_ne_zero
  cases P with
  | none =>
      have := RatFunc.intDegree_add_le hg hfg
      simp only [ord_none]
      omega
  | some a =>
      set p : k[X] := f.num * g.denom + g.num * f.denom with hp
      set q : k[X] := f.denom * g.denom with hq
      have hqne : q ≠ 0 := mul_ne_zero hfd hgd
      have hrep : f + g = algebraMap k[X] (RatFunc k) p / algebraMap k[X] (RatFunc k) q := by
        rw [hp, hq, map_add, map_mul, map_mul, map_mul, ← f.num_div_denom, ← g.num_div_denom]
        rw [RatFunc.num_div_denom, RatFunc.num_div_denom]
        field_simp
        ring
      have hpne : p ≠ 0 := by
        intro h
        rw [h] at hrep
        simp at hrep
        exact hfg hrep
      have hmul1 : (f.num * g.denom) ≠ 0 := mul_ne_zero hfn hgd
      have hmul2 : (g.num * f.denom) ≠ 0 := mul_ne_zero hgn hfd
      set m : ℕ := min ((f.num * g.denom).rootMultiplicity a)
        ((g.num * f.denom).rootMultiplicity a) with hm
      have hdvd : (X - C a) ^ m ∣ p := by
        have h1 : (X - C a) ^ m ∣ (f.num * g.denom) := by
          rw [← Polynomial.le_rootMultiplicity_iff hmul1]
          omega
        have h2 : (X - C a) ^ m ∣ (g.num * f.denom) := by
          rw [← Polynomial.le_rootMultiplicity_iff hmul2]
          omega
        exact hp ▸ dvd_add h1 h2
      have hmle : m ≤ p.rootMultiplicity a := by
        rw [Polynomial.le_rootMultiplicity_iff hpne]
        exact hdvd
      have e1 : (f.num * g.denom).rootMultiplicity a
          = f.num.rootMultiplicity a + g.denom.rootMultiplicity a :=
        Polynomial.rootMultiplicity_mul hmul1
      have e2 : (g.num * f.denom).rootMultiplicity a
          = g.num.rootMultiplicity a + f.denom.rootMultiplicity a :=
        Polynomial.rootMultiplicity_mul hmul2
      have e3 : q.rootMultiplicity a
          = f.denom.rootMultiplicity a + g.denom.rootMultiplicity a :=
        Polynomial.rootMultiplicity_mul hqne
      rw [hrep, ord_some_div a hpne hqne]
      simp only [ord_some]
      omega

lemma ord_const_smul (c : k) (hc : c ≠ 0) (f : RatFunc k) (P : Place k) :
    ord P (c • f) = ord P f := by
  rcases eq_or_ne f 0 with rfl | hf
  · simp
  · have hcm : (c • f) = algebraMap k[X] (RatFunc k) (Polynomial.C c) * f := by
      rw [Algebra.smul_def]
      congr 1
      simp [RatFunc.algebraMap_eq_C]
    have hCne : (Polynomial.C c : k[X]) ≠ 0 := by simpa using hc
    have hne : algebraMap k[X] (RatFunc k) (Polynomial.C c) ≠ 0 := by
      simpa [algebraMap_ne_zero_iff] using hCne
    rw [hcm, ord_mul hne hf]
    cases P with
    | none => rw [ord_algebraMap_none hCne]; simp
    | some a =>
        rw [ord_algebraMap_some a hCne, Polynomial.rootMultiplicity_eq_zero (by
          simp [Polynomial.IsRoot, hc])]
        simp

/-! ### Divisors -/

/-- A divisor on `ℙ¹`: a finitely supported `ℤ`-valued function on the places. -/
abbrev Divisor (k : Type*) [Field k] : Type _ := Place k →₀ ℤ

/-- The degree of a divisor (every closed point has degree one). -/
def degree (D : Divisor k) : ℤ := D.sum fun _ n => n

@[simp] lemma degree_single (P : Place k) (n : ℤ) :
    degree (Finsupp.single P n) = n := by
  classical
  simp [degree, Finsupp.sum_single_index]

lemma degree_sub (D E : Divisor k) : degree (D - E) = degree D - degree E := by
  simpa [degree] using
    Finsupp.sum_sub_index (f := D) (g := E) (h := fun (_ : Place k) (n : ℤ) => n)
      (by intro a b₁ b₂; rfl)

lemma degree_eq (D : Divisor k) : degree D = D none + (D.some.sum fun _ n => n) := by
  simpa [degree] using
    Finsupp.sum_option_index D (fun _ n => n) (fun _ => rfl) (fun _ m₁ m₂ => rfl)

/-! ### Riemann–Roch spaces -/

/-- The Riemann–Roch space `L(D) = {f ≠ 0 | div f + D ≥ 0} ∪ {0}`. -/
noncomputable def LSpace (D : Divisor k) : Submodule k (RatFunc k) where
  carrier := {f | f = 0 ∨ ∀ P, -D P ≤ ord P f}
  zero_mem' := Or.inl rfl
  add_mem' := by
    rintro f g (rfl | hf) hg
    · simpa using hg
    · rcases hg with rfl | hg
      · exact Or.inr (by simpa using hf)
      · rcases eq_or_ne f 0 with rfl | hf0
        · simpa using Or.inr hg
        rcases eq_or_ne g 0 with rfl | hg0
        · simpa using Or.inr hf
        rcases eq_or_ne (f + g) 0 with h0 | h0
        · exact Or.inl h0
        · refine Or.inr fun P => ?_
          have := ord_add_ge hf0 hg0 h0 P
          have h1 := hf P
          have h2 := hg P
          omega
  smul_mem' := by
    rintro c f (rfl | hf)
    · exact Or.inl (by simp)
    · rcases eq_or_ne c 0 with rfl | hc
      · exact Or.inl (by simp)
      · exact Or.inr fun P => by rw [ord_const_smul c hc]; exact hf P

lemma mem_LSpace_iff {D : Divisor k} {f : RatFunc k} :
    f ∈ LSpace D ↔ (f = 0 ∨ ∀ P, -D P ≤ ord P f) := Iff.rfl

/-- `ℓ(D)`, the dimension of the Riemann–Roch space of `D`. -/
noncomputable def ell (D : Divisor k) : ℕ := Module.finrank k (LSpace D)

/-- The canonical divisor of `ℙ¹`: the divisor of the differential `dX`, namely `-2·∞`. -/
noncomputable def canonical (k : Type*) [Field k] : Divisor k := Finsupp.single none (-2)

/-- The genus of the curve, `g = ℓ(K)`. -/
noncomputable def genus (k : Type*) [Field k] : ℕ := ell (canonical k)

/-! ### Computation of `ℓ` -/

/-- The `k`-linear inclusion of polynomials into rational functions. -/
noncomputable def polyToRatFunc (k : Type*) [Field k] : k[X] →ₗ[k] RatFunc k :=
  (IsScalarTower.toAlgHom k k[X] (RatFunc k)).toLinearMap

@[simp] lemma polyToRatFunc_apply (p : k[X]) :
    polyToRatFunc k p = algebraMap k[X] (RatFunc k) p := rfl

lemma polyToRatFunc_injective : Function.Injective (polyToRatFunc k) :=
  RatFunc.algebraMap_injective k

variable [IsAlgClosed k]

/-- Over an algebraically closed field, a rational function with no poles at the points of `k`
is a polynomial. -/
lemma denom_eq_one_of_no_poles {f : RatFunc k} (h : ∀ a : k, 0 ≤ ord (some a) f) :
    f.denom = 1 := by
  by_contra hne
  have hdeg : f.denom.degree ≠ 0 := by
    intro h0
    have : f.denom = Polynomial.C (f.denom.coeff 0) := Polynomial.eq_C_of_degree_eq_zero h0
    have hmonic := f.monic_denom
    rw [this] at hmonic ⊢
    simpa [Polynomial.Monic, Polynomial.leadingCoeff] using hmonic
  obtain ⟨a, ha⟩ := IsAlgClosed.exists_root f.denom hdeg
  have hda : 1 ≤ f.denom.rootMultiplicity a :=
    (Polynomial.le_rootMultiplicity_iff f.denom_ne_zero).2 (by
      simpa using (Polynomial.dvd_iff_isRoot).2 ha)
  have hna : 1 ≤ f.num.rootMultiplicity a := by
    have := h a
    simp only [ord_some] at this
    omega
  have hnr : f.num.IsRoot a := by
    by_contra hcon
    rw [Polynomial.rootMultiplicity_eq_zero hcon] at hna
    omega
  have hcop := RatFunc.isCoprime_num_denom f
  have hdvd1 : (X - C a) ∣ f.num := (Polynomial.dvd_iff_isRoot).2 hnr
  have hdvd2 : (X - C a) ∣ f.denom := (Polynomial.dvd_iff_isRoot).2 ha
  have := hcop.isUnit_of_dvd' hdvd1 hdvd2
  have hdegXa : (X - C a : k[X]).degree = 1 := Polynomial.degree_X_sub_C a
  have := Polynomial.isUnit_iff_degree_eq_zero.1 this
  rw [hdegXa] at this
  exact absurd this (by decide)

lemma LSpace_single_none (m : ℤ) :
    LSpace (Finsupp.single (none : Place k) m)
      = Submodule.map (polyToRatFunc k) (Polynomial.degreeLT k (m + 1).toNat) := by
  ext f
  constructor
  · rintro (rfl | hf)
    · exact ⟨0, by simp [Polynomial.mem_degreeLT], by simp⟩
    · rcases eq_or_ne f 0 with rfl | h0
      · exact ⟨0, by simp [Polynomial.mem_degreeLT], by simp⟩
      have hpoles : ∀ a : k, 0 ≤ ord (some a) f := by
        intro a
        have := hf (some a)
        simpa using this
      have hden : f.denom = 1 := denom_eq_one_of_no_poles hpoles
      have hfp : f = algebraMap k[X] (RatFunc k) f.num := by
        conv_lhs => rw [← f.num_div_denom]
        rw [hden]
        simp
      have hnum : f.num ≠ 0 := RatFunc.num_ne_zero h0
      have hinf := hf none
      rw [Finsupp.single_eq_same, hfp, ord_algebraMap_none hnum] at hinf
      refine ⟨f.num, ?_, hfp.symm⟩
      rw [Polynomial.mem_degreeLT]
      have hle : (f.num.natDegree : ℤ) ≤ m := by omega
      have : f.num.degree = (f.num.natDegree : ℕ) := Polynomial.degree_eq_natDegree hnum
      rw [this]
      have : (f.num.natDegree : ℤ) < (m + 1).toNat := by omega
      exact_mod_cast Nat.cast_lt.2 (by exact_mod_cast this)
  · rintro ⟨p, hp, rfl⟩
    rcases eq_or_ne p 0 with rfl | hp0
    · exact Or.inl (by simp)
    refine Or.inr fun P => ?_
    rw [Polynomial.mem_degreeLT] at hp
    have hdeg : (p.natDegree : ℤ) ≤ m := by
      have h1 : p.degree = (p.natDegree : ℕ) := Polynomial.degree_eq_natDegree hp0
      rw [h1] at hp
      have : p.natDegree < (m + 1).toNat := by exact_mod_cast hp
      omega
    cases P with
    | none =>
        rw [Finsupp.single_eq_same, polyToRatFunc_apply, ord_algebraMap_none hp0]
        omega
    | some a =>
        rw [polyToRatFunc_apply, ord_algebraMap_some a hp0]
        simp

lemma finrank_degreeLT (n : ℕ) : Module.finrank k (Polynomial.degreeLT k n) = n := by
  rw [Module.finrank_eq_card_basis (Polynomial.degreeLT.basis k n)]
  simp

lemma ell_single_none (m : ℤ) : ell (Finsupp.single (none : Place k) m) = (m + 1).toNat := by
  rw [ell, LSpace_single_none]
  rw [← LinearEquiv.finrank_eq
    (Submodule.equivMapOfInjective (polyToRatFunc k) polyToRatFunc_injective
      (Polynomial.degreeLT k (m + 1).toNat))]
  exact finrank_degreeLT _

/-! ### The witness function realizing a divisor away from `∞` -/

/-- A rational function whose divisor agrees with `D` at all finite places. -/
noncomputable def witness (D : Divisor k) : RatFunc k :=
  D.some.prod fun a n => (algebraMap k[X] (RatFunc k) (X - C a)) ^ n

lemma ord_linear_some (a b : k) :
    ord (some b) (algebraMap k[X] (RatFunc k) (X - C a)) = if a = b then 1 else 0 := by
  rw [ord_algebraMap_some b (Polynomial.X_sub_C_ne_zero a)]
  by_cases h : a = b
  · subst h; simp [Polynomial.rootMultiplicity_X_sub_C_self]
  · rw [Polynomial.rootMultiplicity_eq_zero (by
      simp [Polynomial.IsRoot, sub_eq_zero, Ne.symm h])]
    simp [h]

lemma ord_linear_none (a : k) :
    ord none (algebraMap k[X] (RatFunc k) (X - C a)) = -1 := by
  rw [ord_algebraMap_none (Polynomial.X_sub_C_ne_zero a)]
  simp

lemma linear_ne_zero (a : k) : (algebraMap k[X] (RatFunc k) (X - C a)) ≠ 0 := by
  simpa [algebraMap_ne_zero_iff] using Polynomial.X_sub_C_ne_zero a

lemma witness_ne_zero (D : Divisor k) : witness D ≠ 0 := by
  rw [witness, Finsupp.prod]
  exact Finset.prod_ne_zero_iff.2 fun a _ => zpow_ne_zero _ (linear_ne_zero a)

lemma ord_witness (D : Divisor k) (P : Place k) :
    ord P (witness D) = ∑ a ∈ D.some.support, D.some a * ord P
      (algebraMap k[X] (RatFunc k) (X - C a)) := by
  rw [witness, Finsupp.prod]
  induction D.some.support using Finset.induction with
  | empty => simp [ord_one]
  | insert a s ha ih =>
      rw [Finset.prod_insert ha, Finset.sum_insert ha, ord_mul (zpow_ne_zero _ (linear_ne_zero a))
        (Finset.prod_ne_zero_iff.2 fun b _ => zpow_ne_zero _ (linear_ne_zero b)) P,
        ord_zpow (linear_ne_zero a), ih]

lemma ord_some_witness (D : Divisor k) (b : k) :
    ord (some b) (witness D) = D (some b) := by
  classical
  rw [ord_witness]
  simp only [ord_linear_some]
  rw [Finset.sum_congr rfl (fun a _ => by rw [mul_ite, mul_one, mul_zero])]
  rw [Finset.sum_ite_eq D.some.support b (fun a => D.some a)]
  by_cases hb : b ∈ D.some.support
  · simp [hb, Finsupp.some_apply]
  · simp only [hb, if_false]
    have : D.some b = 0 := by
      simpa using Finsupp.not_mem_support_iff.1 hb
    rw [Finsupp.some_apply] at this
    exact this.symm

lemma ord_none_witness (D : Divisor k) :
    ord none (witness D) = -(D.some.sum fun _ n => n) := by
  rw [ord_witness]
  simp only [ord_linear_none, mul_neg, mul_one]
  rw [Finsupp.sum]
  simp [Finset.sum_neg_distrib]

/-! ### The key dimension computation -/

lemma ell_eq (D : Divisor k) : ell D = (degree D + 1).toNat := by
  classical
  set w : RatFunc k := witness D with hw
  have hwne : w ≠ 0 := witness_ne_zero D
  have hwinv : w⁻¹ ≠ 0 := inv_ne_zero hwne
  set D' : Divisor k := Finsupp.single (none : Place k) (degree D) with hD'
  -- multiplication by `w⁻¹` maps `L(D)` isomorphically onto `L(D')`
  have hmap : Submodule.map (LinearMap.mulLeft k w⁻¹) (LSpace D) = LSpace D' := by
    ext g
    constructor
    · rintro ⟨f, hf, rfl⟩
      rcases hf with rfl | hf
      · exact Or.inl (by simp)
      rcases eq_or_ne f 0 with rfl | hf0
      · exact Or.inl (by simp)
      refine Or.inr fun P => ?_
      have hval : (LinearMap.mulLeft k w⁻¹) f = w⁻¹ * f := rfl
      rw [hval, ord_mul hwinv hf0, ord_inv hwne]
      have hfP := hf P
      cases P with
      | none =>
          rw [ord_none_witness]
          have hdeg := degree_eq D
          rw [hD', Finsupp.single_eq_same]
          omega
      | some a =>
          rw [ord_some_witness]
          rw [hD', Finsupp.single_apply]
          simp only [reduceCtorEq, if_false]
          omega
    · intro hg
      rcases hg with rfl | hg
      · exact ⟨0, Or.inl rfl, by simp⟩
      rcases eq_or_ne g 0 with rfl | hg0
      · exact ⟨0, Or.inl rfl, by simp⟩
      refine ⟨w * g, Or.inr fun P => ?_, by
        show w⁻¹ * (w * g) = g
        field_simp⟩
      rw [ord_mul hwne hg0]
      have hgP := hg P
      cases P with
      | none =>
          rw [ord_none_witness]
          have hdeg := degree_eq D
          rw [hD', Finsupp.single_eq_same] at hgP
          omega
      | some a =>
          rw [ord_some_witness]
          rw [hD', Finsupp.single_apply] at hgP
          simp only [reduceCtorEq, if_false] at hgP
          omega
  have hinj : Function.Injective (LinearMap.mulLeft k (w⁻¹ : RatFunc k)) := by
    intro x y hxy
    have : w⁻¹ * x = w⁻¹ * y := hxy
    exact mul_left_cancel₀ hwinv this
  have := (Submodule.equivMapOfInjective (LinearMap.mulLeft k (w⁻¹ : RatFunc k)) hinj
    (LSpace D)).finrank_eq
  rw [ell, this, hmap]
  rw [← ell, hD', ell_single_none]

/-! ### Riemann–Roch -/

@[simp] lemma degree_canonical : degree (canonical k) = -2 := by
  simp [canonical]

lemma genus_eq_zero : genus k = 0 := by
  rw [genus, canonical, ell_single_none]
  norm_num

/-- **Riemann–Roch for a smooth projective curve** (here: the curve `ℙ¹` over an algebraically
closed field `k`, whose function field is `RatFunc k`):
for every divisor `D`, `ℓ(D) - ℓ(K - D) = deg D + 1 - g`, where `K` is the canonical divisor and
`g` the genus. -/
theorem riemann_roch_curve (D : Divisor k) :
    (ell D : ℤ) - (ell (canonical k - D) : ℤ) = degree D + 1 - (genus k : ℤ) := by
  rw [ell_eq, ell_eq, genus_eq_zero, degree_sub, degree_canonical]
  omega

end Math2

