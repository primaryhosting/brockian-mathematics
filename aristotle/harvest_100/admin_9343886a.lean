import Mathlib

/-!
# Riemann Roch Curve
Category: Frontier Math
Target: Math2.riemann_roch_curve
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open scoped BigOperators
open scoped Classical

set_option maxHeartbeats 1000000
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
## Scope and setup

We formalise the Riemann–Roch theorem for the projective line `ℙ¹` over an algebraically
closed field `k`, a smooth projective curve, with everything built from scratch:

* the places of `ℙ¹` are the points `a : k` of the affine line together with the point at
  infinity, and the associated discrete valuations are `ordAt a` and `ordInf`;
* a divisor is a finitely supported family of integers on the affine points together with a
  coefficient at infinity, and `Divisor.deg` is its degree;
* `RRSpace D` is the Riemann-Roch space `L(D) = {f : div f + D ≥ 0}` and
  `ell D = ℓ(D) = dim_k L(D)`;
* `canonicalDivisor k` is the divisor `-2·∞` of the differential `dt`, and the genus is
  defined intrinsically as `genus k = ℓ(K)`.

The main theorem `Math2.riemann_roch_curve` states `ℓ(D) - ℓ(K - D) = deg D + 1 - g`.
It is deduced from the computation `Math2.ell_eq : ℓ(D) = max (deg D + 1) 0`, which is proved
by exhibiting an explicit `k`-linear isomorphism between `L(D)` and the space of polynomials
of degree at most `deg D`.
-/

namespace Math2

open Polynomial

variable {k : Type*} [Field k]

/-! ## Orders of vanishing (the discrete valuations of `ℙ¹`) -/

/-- The order of vanishing at the point `a` of the affine line, of a rational function `f`. -/
noncomputable def ordAt (a : k) (f : RatFunc k) : ℤ :=
  (f.num.rootMultiplicity a : ℤ) - (f.denom.rootMultiplicity a : ℤ)

/-- The order of vanishing at the point at infinity of `ℙ¹`. -/
noncomputable def ordInf (f : RatFunc k) : ℤ := -f.intDegree

theorem ordAt_div (a : k) {P Q : k[X]} (hP : P ≠ 0) (hQ : Q ≠ 0) :
    ordAt a (algebraMap k[X] (RatFunc k) P / algebraMap k[X] (RatFunc k) Q)
      = (P.rootMultiplicity a : ℤ) - (Q.rootMultiplicity a : ℤ) := by
  set f : RatFunc k := algebraMap k[X] (RatFunc k) P / algebraMap k[X] (RatFunc k) Q with hf
  have hf0 : f ≠ 0 := by
    simp [hf, RatFunc.algebraMap_ne_zero hP, RatFunc.algebraMap_ne_zero hQ]
  have hcross : f.num * Q = P * f.denom := by
    have h1 : (algebraMap k[X] (RatFunc k)) (f.num * Q)
        = (algebraMap k[X] (RatFunc k)) (P * f.denom) := by
      push_cast [map_mul]
      rw [← div_eq_div_iff (RatFunc.algebraMap_ne_zero f.denom_ne_zero)
        (RatFunc.algebraMap_ne_zero hQ), RatFunc.num_div_denom]
    exact IsFractionRing.injective k[X] (RatFunc k) h1
  have hnum : f.num ≠ 0 := RatFunc.num_ne_zero hf0
  have h2 := congrArg (fun p => Polynomial.rootMultiplicity a p) hcross
  simp only [Polynomial.rootMultiplicity_mul (mul_ne_zero hnum hQ),
    Polynomial.rootMultiplicity_mul (mul_ne_zero hP f.denom_ne_zero)] at h2
  simp only [ordAt]
  omega

@[simp] theorem ordAt_zero (a : k) : ordAt a (0 : RatFunc k) = 0 := by simp [ordAt]

@[simp] theorem ordInf_zero : ordInf (0 : RatFunc k) = 0 := by simp [ordInf]

theorem ordAt_polynomial (a : k) (P : k[X]) :
    ordAt a (algebraMap k[X] (RatFunc k) P) = (P.rootMultiplicity a : ℤ) := by
  rcases eq_or_ne P 0 with rfl | hP
  · simp
  · have h := ordAt_div a hP (one_ne_zero (α := k[X]))
    rw [map_one, div_one] at h
    have h1 : Polynomial.rootMultiplicity a (1 : k[X]) = 0 :=
      Polynomial.rootMultiplicity_eq_zero (by simp)
    rw [h, h1]
    simp

theorem ordInf_polynomial (P : k[X]) :
    ordInf (algebraMap k[X] (RatFunc k) P) = -(P.natDegree : ℤ) := by
  simp [ordInf]

theorem ordAt_mul (a : k) {f g : RatFunc k} (hf : f ≠ 0) (hg : g ≠ 0) :
    ordAt a (f * g) = ordAt a f + ordAt a g := by
  have h1 : f = algebraMap k[X] (RatFunc k) f.num / algebraMap k[X] (RatFunc k) f.denom :=
    (RatFunc.num_div_denom f).symm
  have h2 : g = algebraMap k[X] (RatFunc k) g.num / algebraMap k[X] (RatFunc k) g.denom :=
    (RatFunc.num_div_denom g).symm
  have hfn := RatFunc.num_ne_zero hf
  have hgn := RatFunc.num_ne_zero hg
  have key : f * g = algebraMap k[X] (RatFunc k) (f.num * g.num)
      / algebraMap k[X] (RatFunc k) (f.denom * g.denom) := by
    rw [map_mul, map_mul, ← div_mul_div_comm, ← h1, ← h2]
  rw [key, ordAt_div a (mul_ne_zero hfn hgn) (mul_ne_zero f.denom_ne_zero g.denom_ne_zero),
    Polynomial.rootMultiplicity_mul (mul_ne_zero hfn hgn),
    Polynomial.rootMultiplicity_mul (mul_ne_zero f.denom_ne_zero g.denom_ne_zero)]
  simp only [ordAt]
  push_cast
  ring

theorem ordInf_mul {f g : RatFunc k} (hf : f ≠ 0) (hg : g ≠ 0) :
    ordInf (f * g) = ordInf f + ordInf g := by
  simp [ordInf, RatFunc.intDegree_mul hf hg]
  ring

@[simp] theorem ordAt_one (a : k) : ordAt a (1 : RatFunc k) = 0 := by
  have h1 : Polynomial.rootMultiplicity a (1 : k[X]) = 0 :=
    Polynomial.rootMultiplicity_eq_zero (by simp)
  simpa [h1] using ordAt_polynomial a (1 : k[X])

@[simp] theorem ordInf_one : ordInf (1 : RatFunc k) = 0 := by simp [ordInf]

theorem ordAt_inv (a : k) (f : RatFunc k) : ordAt a f⁻¹ = -ordAt a f := by
  rcases eq_or_ne f 0 with rfl | hf
  · simp
  · have h : ordAt a (f⁻¹ * f) = ordAt a f⁻¹ + ordAt a f :=
      ordAt_mul a (inv_ne_zero hf) hf
    rw [inv_mul_cancel₀ hf, ordAt_one] at h
    omega

theorem ordInf_inv (f : RatFunc k) : ordInf f⁻¹ = -ordInf f := by
  simp [ordInf]

theorem ordAt_pow (a : k) {f : RatFunc k} (hf : f ≠ 0) (n : ℕ) :
    ordAt a (f ^ n) = n * ordAt a f := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [pow_succ, ordAt_mul a (pow_ne_zero _ hf) hf, ih]
    push_cast
    ring

theorem ordInf_pow {f : RatFunc k} (hf : f ≠ 0) (n : ℕ) :
    ordInf (f ^ n) = n * ordInf f := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [pow_succ, ordInf_mul (pow_ne_zero _ hf) hf, ih]
    push_cast
    ring

theorem ordAt_zpow (a : k) {f : RatFunc k} (hf : f ≠ 0) (n : ℤ) :
    ordAt a (f ^ n) = n * ordAt a f := by
  obtain ⟨m, rfl | rfl⟩ := n.eq_nat_or_neg
  · simpa using ordAt_pow a hf m
  · rw [zpow_neg, ordAt_inv, zpow_natCast, ordAt_pow a hf m]
    ring

theorem ordInf_zpow {f : RatFunc k} (hf : f ≠ 0) (n : ℤ) :
    ordInf (f ^ n) = n * ordInf f := by
  obtain ⟨m, rfl | rfl⟩ := n.eq_nat_or_neg
  · simpa using ordInf_pow hf m
  · rw [zpow_neg, ordInf_inv, zpow_natCast, ordInf_pow hf m]
    ring

theorem ordAt_prod {ι : Type*} (a : k) (s : Finset ι) (F : ι → RatFunc k)
    (h : ∀ i ∈ s, F i ≠ 0) : ordAt a (∏ i ∈ s, F i) = ∑ i ∈ s, ordAt a (F i) := by
  classical
  induction s using Finset.induction with
  | empty => simp
  | insert i s hi ih =>
    rw [Finset.prod_insert hi, Finset.sum_insert hi,
      ordAt_mul a (h i (Finset.mem_insert_self i s))
        (Finset.prod_ne_zero_iff.2 fun j hj => h j (Finset.mem_insert_of_mem hj)),
      ih fun j hj => h j (Finset.mem_insert_of_mem hj)]

theorem ordInf_prod {ι : Type*} (s : Finset ι) (F : ι → RatFunc k)
    (h : ∀ i ∈ s, F i ≠ 0) : ordInf (∏ i ∈ s, F i) = ∑ i ∈ s, ordInf (F i) := by
  classical
  induction s using Finset.induction with
  | empty => simp
  | insert i s hi ih =>
    rw [Finset.prod_insert hi, Finset.sum_insert hi,
      ordInf_mul (h i (Finset.mem_insert_self i s))
        (Finset.prod_ne_zero_iff.2 fun j hj => h j (Finset.mem_insert_of_mem hj)),
      ih fun j hj => h j (Finset.mem_insert_of_mem hj)]

theorem pow_dvd_of_le_rootMultiplicity {p : k[X]} {a : k} {M : ℕ}
    (h : M ≤ p.rootMultiplicity a) : ((X : k[X]) - C a) ^ M ∣ p :=
  dvd_trans (pow_dvd_pow _ h) (Polynomial.pow_rootMultiplicity_dvd p a)

/-- The ultrametric inequality at a finite place. -/
theorem le_ordAt_add (a : k) {f g : RatFunc k} {n : ℤ} (hfg : f + g ≠ 0)
    (hf : n ≤ ordAt a f) (hg : n ≤ ordAt a g) : n ≤ ordAt a (f + g) := by
  rcases eq_or_ne f 0 with rfl | hf0
  · simpa using hg
  rcases eq_or_ne g 0 with rfl | hg0
  · simpa using hf
  have hN : f.num * g.denom + f.denom * g.num ≠ 0 :=
    RatFunc.num_mul_denom_add_denom_mul_num_ne_zero hfg
  have key : f + g = algebraMap k[X] (RatFunc k) (f.num * g.denom + f.denom * g.num)
      / algebraMap k[X] (RatFunc k) (f.denom * g.denom) := by
    conv_lhs => rw [← RatFunc.num_div_denom f, ← RatFunc.num_div_denom g]
    rw [div_add_div _ _ (RatFunc.algebraMap_ne_zero f.denom_ne_zero)
      (RatFunc.algebraMap_ne_zero g.denom_ne_zero), map_add, map_mul, map_mul, map_mul]
  rw [key, ordAt_div a hN (mul_ne_zero f.denom_ne_zero g.denom_ne_zero),
    Polynomial.rootMultiplicity_mul (mul_ne_zero f.denom_ne_zero g.denom_ne_zero)]
  simp only [ordAt] at hf hg
  set M : ℤ := n + (f.denom.rootMultiplicity a : ℤ) + (g.denom.rootMultiplicity a : ℤ) with hM
  rcases le_or_gt M 0 with hM0 | hM0
  · have : (0 : ℤ) ≤ (f.denom.rootMultiplicity a : ℤ) := Int.natCast_nonneg _
    have : (0 : ℤ) ≤ ((f.num * g.denom + f.denom * g.num).rootMultiplicity a : ℤ) :=
      Int.natCast_nonneg _
    omega
  · lift M to ℕ using le_of_lt hM0 with M' hM'
    have hd1 : ((X : k[X]) - C a) ^ M' ∣ f.num * g.denom := by
      refine pow_dvd_of_le_rootMultiplicity ?_
      rw [Polynomial.rootMultiplicity_mul (mul_ne_zero (RatFunc.num_ne_zero hf0)
        g.denom_ne_zero)]
      omega
    have hd2 : ((X : k[X]) - C a) ^ M' ∣ f.denom * g.num := by
      refine pow_dvd_of_le_rootMultiplicity ?_
      rw [Polynomial.rootMultiplicity_mul (mul_ne_zero f.denom_ne_zero
        (RatFunc.num_ne_zero hg0))]
      omega
    have : M' ≤ (f.num * g.denom + f.denom * g.num).rootMultiplicity a :=
      (Polynomial.le_rootMultiplicity_iff hN).2 (dvd_add hd1 hd2)
    omega

/-- The ultrametric inequality at the place at infinity. -/
theorem le_ordInf_add {f g : RatFunc k} {n : ℤ} (hfg : f + g ≠ 0)
    (hf : n ≤ ordInf f) (hg : n ≤ ordInf g) : n ≤ ordInf (f + g) := by
  rcases eq_or_ne g 0 with rfl | hg0
  · simpa using hf
  have h := RatFunc.intDegree_add_le hg0 hfg
  simp only [ordInf] at hf hg ⊢
  rcases le_max_iff.1 h with h' | h' <;> omega

theorem ordAt_smul (a : k) {c : k} (hc : c ≠ 0) (f : RatFunc k) :
    ordAt a (c • f) = ordAt a f := by
  rcases eq_or_ne f 0 with rfl | hf
  · simp
  have hCc : (RatFunc.C c : RatFunc k) ≠ 0 := by
    simpa using hc
  have h0 : ordAt a (RatFunc.C c : RatFunc k) = 0 := by
    rw [← RatFunc.algebraMap_C, ordAt_polynomial]
    rw [Polynomial.rootMultiplicity_eq_zero (by simpa using hc)]
    simp
  rw [RatFunc.smul_eq_C_mul, ordAt_mul a hCc hf, h0, zero_add]

theorem ordInf_smul {c : k} (hc : c ≠ 0) (f : RatFunc k) :
    ordInf (c • f) = ordInf f := by
  rcases eq_or_ne f 0 with rfl | hf
  · simp
  have hCc : (RatFunc.C c : RatFunc k) ≠ 0 := by simpa using hc
  rw [RatFunc.smul_eq_C_mul, ordInf_mul hCc hf]
  simp [ordInf]

/-- A rational function with nonnegative order at every point of the affine line is
a polynomial (this uses that `k` is algebraically closed). -/
theorem exists_polynomial_of_ordAt_nonneg [IsAlgClosed k] {f : RatFunc k}
    (h : ∀ a : k, 0 ≤ ordAt a f) : ∃ u : k[X], f = algebraMap k[X] (RatFunc k) u := by
  have hcop : IsCoprime f.num f.denom := RatFunc.isCoprime_num_denom f
  have hnoroot : ∀ a : k, ¬ f.denom.IsRoot a := by
    intro a ha
    have h1 : 0 < f.denom.rootMultiplicity a :=
      (Polynomial.rootMultiplicity_pos f.denom_ne_zero).2 ha
    have h2 := h a
    simp only [ordAt] at h2
    have h3 : 0 < f.num.rootMultiplicity a := by omega
    have hdvd1 : ((X : k[X]) - C a) ∣ f.num := by
      simpa using pow_dvd_of_le_rootMultiplicity (p := f.num) (a := a) (M := 1) h3
    have hdvd2 : ((X : k[X]) - C a) ∣ f.denom := by
      simpa using pow_dvd_of_le_rootMultiplicity (p := f.denom) (a := a) (M := 1) h1
    have := hcop.isUnit_of_dvd' hdvd1 hdvd2
    exact (Polynomial.not_isUnit_X_sub_C a) this
  have hdeg : f.denom.natDegree = 0 := by
    by_contra hne
    obtain ⟨a, ha⟩ := IsAlgClosed.exists_root f.denom
      (fun hd => hne (Polynomial.natDegree_eq_zero_iff_degree_le_zero.2 (le_of_eq hd)))
    exact hnoroot a ha
  have hone : f.denom = 1 := by
    have hm : f.denom.Monic := RatFunc.monic_denom f
    exact hm.natDegree_eq_zero.1 hdeg
  refine ⟨f.num, ?_⟩
  conv_lhs => rw [← RatFunc.num_div_denom f]
  rw [hone, map_one, div_one]

/-! ## Divisors -/

/-- A divisor on `ℙ¹` over `k`: a finitely supported family of integers indexed by the points
of the affine line, together with the coefficient at the point at infinity. -/
abbrev Divisor (k : Type*) [Field k] := (k →₀ ℤ) × ℤ

/-- The degree of a divisor (every point of `ℙ¹` over an algebraically closed field has
degree one). -/
def Divisor.deg (D : Divisor k) : ℤ := (D.1.sum fun _ n => n) + D.2

theorem Divisor.deg_sub (D E : Divisor k) : (D - E).deg = D.deg - E.deg := by
  simp only [Divisor.deg, Prod.fst_sub, Prod.snd_sub]
  rw [Finsupp.sum_sub_index (fun _ _ _ => rfl)]
  ring

/-- The Riemann–Roch space `L(D) = {f : div f + D ≥ 0}`. -/
def RRSpace (D : Divisor k) : Submodule k (RatFunc k) where
  carrier := {f | f = 0 ∨ ((∀ a : k, -(D.1 a) ≤ ordAt a f) ∧ -D.2 ≤ ordInf f)}
  add_mem' := by
    rintro f g (rfl | ⟨hf1, hf2⟩) hg
    · simpa using hg
    rcases hg with rfl | ⟨hg1, hg2⟩
    · simp only [add_zero]
      exact Or.inr ⟨hf1, hf2⟩
    rcases eq_or_ne (f + g) 0 with h0 | h0
    · exact Or.inl h0
    exact Or.inr ⟨fun a => le_ordAt_add a h0 (hf1 a) (hg1 a), le_ordInf_add h0 hf2 hg2⟩
  zero_mem' := Or.inl rfl
  smul_mem' := by
    rintro c f (rfl | ⟨hf1, hf2⟩)
    · simp
    rcases eq_or_ne c 0 with rfl | hc
    · simp
    exact Or.inr ⟨fun a => by rw [ordAt_smul a hc]; exact hf1 a,
      by rw [ordInf_smul hc]; exact hf2⟩

theorem mem_RRSpace_iff {D : Divisor k} {f : RatFunc k} :
    f ∈ RRSpace D ↔ f = 0 ∨ ((∀ a : k, -(D.1 a) ≤ ordAt a f) ∧ -D.2 ≤ ordInf f) := Iff.rfl

/-- `ℓ(D)`, the dimension of the Riemann–Roch space of `D`. -/
noncomputable def ell (D : Divisor k) : ℕ := Module.finrank k (RRSpace D)

/-- The canonical divisor of `ℙ¹`: the divisor of the differential `dt`, namely `-2·∞`. -/
def canonicalDivisor (k : Type*) [Field k] : Divisor k := (0, -2)

/-- The genus of a curve is the dimension of the space of global regular differentials,
i.e. `ℓ(K)` for a canonical divisor `K`. -/
noncomputable def genus (k : Type*) [Field k] : ℕ := ell (canonicalDivisor k)

/-! ## Computation of `ℓ(D)` -/

/-- The rational function `∏ (X - a) ^ D a` cutting out the finite part of `D`. -/
noncomputable def divisorFun (D : Divisor k) : RatFunc k :=
  ∏ a ∈ D.1.support, (algebraMap k[X] (RatFunc k) (X - C a)) ^ (D.1 a)

theorem algebraMap_X_sub_C_ne_zero (a : k) :
    algebraMap k[X] (RatFunc k) (X - C a) ≠ 0 :=
  RatFunc.algebraMap_ne_zero (Polynomial.X_sub_C_ne_zero a)

theorem divisorFun_ne_zero (D : Divisor k) : divisorFun D ≠ 0 := by
  refine Finset.prod_ne_zero_iff.2 fun a _ => ?_
  exact zpow_ne_zero _ (algebraMap_X_sub_C_ne_zero a)

theorem ordAt_divisorFun (D : Divisor k) (b : k) : ordAt b (divisorFun D) = D.1 b := by
  classical
  rw [divisorFun, ordAt_prod b _ _ (fun a _ => zpow_ne_zero _ (algebraMap_X_sub_C_ne_zero a))]
  have hterm : ∀ a : k, ordAt b ((algebraMap k[X] (RatFunc k) (X - C a)) ^ (D.1 a))
      = D.1 a * (if b = a then 1 else 0) := by
    intro a
    rw [ordAt_zpow b (algebraMap_X_sub_C_ne_zero a), ordAt_polynomial,
      Polynomial.rootMultiplicity_X_sub_C]
    split_ifs <;> simp
  simp only [hterm]
  rw [Finset.sum_eq_single b]
  · simp
  · intro a _ hab
    simp [Ne.symm hab]
  · intro hb
    simp [Finsupp.notMem_support_iff.1 hb]

theorem ordInf_divisorFun (D : Divisor k) :
    ordInf (divisorFun D) = -(D.1.sum fun _ n => n) := by
  rw [divisorFun, ordInf_prod _ _ (fun a _ => zpow_ne_zero _ (algebraMap_X_sub_C_ne_zero a))]
  have hterm : ∀ a : k, ordInf ((algebraMap k[X] (RatFunc k) (X - C a)) ^ (D.1 a))
      = -(D.1 a) := by
    intro a
    rw [ordInf_zpow (algebraMap_X_sub_C_ne_zero a), ordInf_polynomial,
      Polynomial.natDegree_X_sub_C]
    ring
  simp only [hterm]
  rw [Finsupp.sum]
  rw [← Finset.sum_neg_distrib]

/-- Multiplication by a nonzero rational function, as a `k`-linear automorphism. -/
noncomputable def mulEquiv (h : RatFunc k) (hh : h ≠ 0) : RatFunc k ≃ₗ[k] RatFunc k where
  toFun f := f * h
  map_add' f g := add_mul f g h
  map_smul' c f := by simp
  invFun f := f * h⁻¹
  left_inv f := by field_simp
  right_inv f := by field_simp

@[simp] theorem mulEquiv_apply (h : RatFunc k) (hh : h ≠ 0) (f : RatFunc k) :
    mulEquiv h hh f = f * h := rfl

/-- The space of polynomials of degree `< N`, viewed inside the field of rational functions. -/
noncomputable def polySpace (k : Type*) [Field k] (N : ℕ) : Submodule k (RatFunc k) :=
  Submodule.map (IsScalarTower.toAlgHom k k[X] (RatFunc k)).toLinearMap (Polynomial.degreeLT k N)

theorem mem_polySpace_iff {N : ℕ} {f : RatFunc k} :
    f ∈ polySpace k N ↔ ∃ u : k[X], u.degree < (N : WithBot ℕ) ∧
      f = algebraMap k[X] (RatFunc k) u := by
  constructor
  · rintro ⟨u, hu, rfl⟩
    exact ⟨u, Polynomial.mem_degreeLT.1 hu, rfl⟩
  · rintro ⟨u, hu, rfl⟩
    exact ⟨u, Polynomial.mem_degreeLT.2 hu, rfl⟩

theorem finrank_polySpace (N : ℕ) : Module.finrank k (polySpace k N) = N := by
  have hinj : Function.Injective
      ⇑(IsScalarTower.toAlgHom k k[X] (RatFunc k)).toLinearMap :=
    IsFractionRing.injective k[X] (RatFunc k)
  have he := (Submodule.equivMapOfInjective _ hinj (Polynomial.degreeLT k N)).symm
  rw [polySpace, he.finrank_eq]
  simpa using Module.finrank_eq_card_basis (Polynomial.degreeLT.basis k N)

/-- The key computation: multiplication by `divisorFun D` identifies `L(D)` with the space of
polynomials of degree at most `deg D`. -/
theorem map_mulEquiv_RRSpace [IsAlgClosed k] (D : Divisor k) :
    Submodule.map (mulEquiv (divisorFun D) (divisorFun_ne_zero D)).toLinearMap (RRSpace D)
      = polySpace k (D.deg + 1).toNat := by
  classical
  set H := divisorFun D with hHdef
  have hH : H ≠ 0 := divisorFun_ne_zero D
  set S : ℤ := D.1.sum (fun _ n => n) with hS
  have hdeg : D.deg = S + D.2 := rfl
  have hordH : ∀ a : k, ordAt a H = D.1 a := ordAt_divisorFun D
  have hoinfH : ordInf H = -S := ordInf_divisorFun D
  ext g
  constructor
  · rintro ⟨f, hf, rfl⟩
    have hgf : (mulEquiv H hH).toLinearMap f = f * H := rfl
    rw [hgf]
    rcases hf with rfl | ⟨hf1, hf2⟩
    · simp
    by_cases hf0 : f = 0
    · simp [hf0]
    have hfH : f * H ≠ 0 := mul_ne_zero hf0 hH
    have hordmul : ∀ a : k, ordAt a (f * H) = ordAt a f + D.1 a := by
      intro a
      rw [ordAt_mul a hf0 hH, hordH a]
    obtain ⟨u, hu⟩ := exists_polynomial_of_ordAt_nonneg (f := f * H) (by
      intro a
      have := hf1 a
      rw [hordmul a]
      omega)
    have hu0 : u ≠ 0 := by
      intro h0
      rw [h0, map_zero] at hu
      exact hfH hu
    have hoinf : ordInf (f * H) = ordInf f - S := by
      rw [ordInf_mul hf0 hH, hoinfH]
      ring
    have hdegu : (u.natDegree : ℤ) ≤ D.deg := by
      have h1 : ordInf (algebraMap k[X] (RatFunc k) u) = -(u.natDegree : ℤ) :=
        ordInf_polynomial u
      rw [← hu, hoinf] at h1
      omega
    refine mem_polySpace_iff.2 ⟨u, ?_, hu⟩
    refine (Polynomial.natDegree_lt_iff_degree_lt hu0).1 ?_
    have : (0 : ℤ) ≤ (u.natDegree : ℤ) := Int.natCast_nonneg _
    omega
  · intro hg
    obtain ⟨u, hudeg, rfl⟩ := mem_polySpace_iff.1 hg
    refine ⟨algebraMap k[X] (RatFunc k) u * H⁻¹, ?_, ?_⟩
    · rcases eq_or_ne u 0 with rfl | hu0
      · simp
      have hne : algebraMap k[X] (RatFunc k) u ≠ 0 := RatFunc.algebraMap_ne_zero hu0
      have hinvne : H⁻¹ ≠ 0 := inv_ne_zero hH
      have hordu : ∀ a : k, ordAt a (algebraMap k[X] (RatFunc k) u * H⁻¹)
          = (u.rootMultiplicity a : ℤ) - D.1 a := by
        intro a
        rw [ordAt_mul a hne hinvne, ordAt_inv, ordAt_polynomial, hordH a]
        ring
      have hoinfu : ordInf (algebraMap k[X] (RatFunc k) u * H⁻¹) = -(u.natDegree : ℤ) + S := by
        rw [ordInf_mul hne hinvne, ordInf_inv, hoinfH, ordInf_polynomial]
        ring
      have hnd : u.natDegree < (D.deg + 1).toNat :=
        (Polynomial.natDegree_lt_iff_degree_lt hu0).2 hudeg
      refine Or.inr ⟨fun a => ?_, ?_⟩
      · rw [hordu a]
        have : (0 : ℤ) ≤ (u.rootMultiplicity a : ℤ) := Int.natCast_nonneg _
        omega
      · rw [hoinfu]
        have h2 : (u.natDegree : ℤ) < ((D.deg + 1).toNat : ℤ) := by exact_mod_cast hnd
        omega
    · show algebraMap k[X] (RatFunc k) u * H⁻¹ * H = algebraMap k[X] (RatFunc k) u
      field_simp

/-- `ℓ(D) = max (deg D + 1) 0`. -/
theorem ell_eq [IsAlgClosed k] (D : Divisor k) : (ell D : ℤ) = max (D.deg + 1) 0 := by
  have hinj : Function.Injective ⇑(mulEquiv (divisorFun D) (divisorFun_ne_zero D)).toLinearMap :=
    (mulEquiv (divisorFun D) (divisorFun_ne_zero D)).injective
  have he := Submodule.equivMapOfInjective _ hinj (RRSpace D)
  have h1 : Module.finrank k (RRSpace D)
      = Module.finrank k (polySpace k (D.deg + 1).toNat) := by
    rw [he.finrank_eq, map_mulEquiv_RRSpace D]
  rw [ell, h1, finrank_polySpace]
  omega

theorem genus_eq_zero [IsAlgClosed k] : genus k = 0 := by
  have h := ell_eq (canonicalDivisor k)
  have hK : (canonicalDivisor k).deg = -2 := by
    simp [Divisor.deg, canonicalDivisor]
  rw [hK] at h
  simp only [genus]
  omega

/-! ## The Riemann–Roch theorem -/

/-- **Riemann–Roch** for the smooth projective curve `ℙ¹` over an algebraically closed field:
`ℓ(D) - ℓ(K - D) = deg D + 1 - g`. -/
theorem riemann_roch_curve [IsAlgClosed k] (D : Divisor k) :
    (ell D : ℤ) - (ell (canonicalDivisor k - D) : ℤ) = D.deg + 1 - (genus k : ℤ) := by
  have hK : (canonicalDivisor k).deg = -2 := by
    simp [Divisor.deg, canonicalDivisor]
  have h1 := ell_eq D
  have h2 := ell_eq (canonicalDivisor k - D)
  rw [Divisor.deg_sub, hK] at h2
  rw [h1, h2, genus_eq_zero]
  omega

/-- The degree of the canonical divisor is `2g - 2`. -/
theorem deg_canonicalDivisor [IsAlgClosed k] :
    (canonicalDivisor k).deg = 2 * (genus k : ℤ) - 2 := by
  rw [genus_eq_zero]
  simp [Divisor.deg, canonicalDivisor]

/-- Riemann's inequality: `ℓ(D) ≥ deg D + 1 - g`. -/
theorem riemann_inequality [IsAlgClosed k] (D : Divisor k) :
    D.deg + 1 - (genus k : ℤ) ≤ (ell D : ℤ) := by
  have h := riemann_roch_curve D
  have h2 : (0 : ℤ) ≤ (ell (canonicalDivisor k - D) : ℤ) := Int.natCast_nonneg _
  omega

/-- For divisors of large degree the correction term vanishes: if `deg D > 2g - 2` then
`ℓ(D) = deg D + 1 - g`. -/
theorem ell_eq_of_deg_gt [IsAlgClosed k] (D : Divisor k)
    (hD : 2 * (genus k : ℤ) - 2 < D.deg) : (ell D : ℤ) = D.deg + 1 - (genus k : ℤ) := by
  have h := riemann_roch_curve D
  have h2 := ell_eq (canonicalDivisor k - D)
  rw [Divisor.deg_sub, deg_canonicalDivisor] at h2
  rw [genus_eq_zero] at h hD h2 ⊢
  omega

end Math2

