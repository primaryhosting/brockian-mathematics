import RequestProject.BelyiPoly

/-!
# Belyi polynomials for finite sets of rational points

A polynomial `f ∈ ℚ[X]` is *Belyi* if it is non-constant and all of its finite critical values
(computed over `ℂ`) lie in `{0, 1}`; viewed as a map `ℙ¹ → ℙ¹` such an `f` is ramified only
above `{0, 1, ∞}`.

The main result of this file is `Math2.exists_belyiPolynomial_of_rat`: for every finite set of
rational numbers there is a Belyi polynomial taking each of them to `0` or `1`.
-/

set_option maxRecDepth 8000

namespace Math2

open Polynomial

/-- `f` is a Belyi polynomial: non-constant, with all finite critical values in `{0, 1}`. -/
def IsBelyiPolynomial (f : ℚ[X]) : Prop :=
  0 < f.natDegree ∧ ∀ z : ℂ, aeval z (derivative f) = 0 → aeval z f = 0 ∨ aeval z f = 1

/-- Composition of Belyi polynomials, provided the critical values of the inner map are sent
into `{0, 1}` by the outer map. -/
lemma IsBelyiPolynomial.comp {f g : ℚ[X]} (hf : 0 < f.natDegree) (hg : IsBelyiPolynomial g)
    (hcrit : ∀ z : ℂ, aeval z (derivative f) = 0 →
      aeval (aeval z f) g = 0 ∨ aeval (aeval z f) g = 1) :
    IsBelyiPolynomial (g.comp f) := by
  refine ⟨?_, ?_⟩
  · rw [natDegree_comp]
    exact Nat.mul_pos hg.1 hf
  · intro z hz
    rw [derivative_comp] at hz
    simp only [map_mul, aeval_comp] at hz
    rw [aeval_comp]
    rcases mul_eq_zero.1 hz with h | h
    · exact hcrit z h
    · exact hg.2 _ h

lemma isBelyiPolynomial_X : IsBelyiPolynomial (X : ℚ[X]) := by
  refine ⟨by simp, ?_⟩
  intro z hz
  simp at hz

/-- The property we propagate through the induction on finite sets of rationals in `[0,1]`. -/
def RatBelyi (S : Finset ℚ) (f : ℚ[X]) : Prop :=
  IsBelyiPolynomial f ∧ (∀ x ∈ S, f.eval x = 0 ∨ f.eval x = 1) ∧
    (f.eval 0 = 0 ∨ f.eval 0 = 1) ∧ (f.eval 1 = 0 ∨ f.eval 1 = 1) ∧
    (∀ x : ℚ, 0 ≤ x → x ≤ 1 → 0 ≤ f.eval x ∧ f.eval x ≤ 1)

/-- Writing a rational number in `(0,1)` as `m/(m+n)` with `m, n` positive naturals. -/
lemma exists_num_den {lam : ℚ} (h0 : 0 < lam) (h1 : lam < 1) :
    ∃ m n : ℕ, 0 < m ∧ 0 < n ∧ (m : ℚ) / ((m : ℚ) + (n : ℚ)) = lam := by
  refine ⟨lam.num.toNat, lam.den - lam.num.toNat, ?_, ?_, ?_⟩
  · have : 0 < lam.num := Rat.num_pos.2 h0
    omega
  · have hnum : 0 < lam.num := Rat.num_pos.2 h0
    have : lam.num < (lam.den : ℤ) := Rat.lt_one_iff_num_lt_denom.mp h1
    omega
  · have hnum : 0 < lam.num := Rat.num_pos.2 h0
    have hlt : lam.num < (lam.den : ℤ) := Rat.lt_one_iff_num_lt_denom.mp h1
    have hsum : (lam.num.toNat : ℚ) + ((lam.den - lam.num.toNat : ℕ) : ℚ) = (lam.den : ℚ) := by
      have : lam.num.toNat ≤ lam.den := by omega
      push_cast [Nat.cast_sub this]
      ring
    rw [hsum]
    have hnum' : (lam.num.toNat : ℚ) = (lam.num : ℚ) := by
      have : (lam.num.toNat : ℤ) = lam.num := Int.toNat_of_nonneg hnum.le
      exact_mod_cast congrArg (fun z : ℤ => (z : ℚ)) this
    rw [hnum']
    exact Rat.num_div_den lam

/-- Values of `f ∈ ℚ[X]` at rational points, transported to `ℂ`. -/
lemma aeval_rat_mem {f : ℚ[X]} {q : ℚ} (h : f.eval q = 0 ∨ f.eval q = 1) :
    aeval (q : ℂ) f = 0 ∨ aeval (q : ℂ) f = 1 := by
  rw [aeval_rat]
  rcases h with h | h <;> rw [h] <;> simp

/-- Main induction: a Belyi polynomial sending a finite set of rationals of `[0,1]` into `{0,1}`,
which moreover fixes the unit interval and sends `0, 1` into `{0,1}`. -/
lemma exists_ratBelyi_aux : ∀ (k : ℕ) (S : Finset ℚ), (∀ x ∈ S, 0 ≤ x ∧ x ≤ 1) →
    (S.filter (fun x => x ≠ 0 ∧ x ≠ 1)).card ≤ k → ∃ f : ℚ[X], RatBelyi S f := by
  intro k
  induction k with
  | zero =>
    intro S _ hcard
    refine ⟨X, isBelyiPolynomial_X, ?_, by simp, by simp, ?_⟩
    · intro x hx
      have hempty : S.filter (fun x => x ≠ 0 ∧ x ≠ 1) = ∅ := Finset.card_eq_zero.1 (by omega)
      by_contra hcon
      push_neg at hcon
      have : x ∈ S.filter (fun x => x ≠ 0 ∧ x ≠ 1) := by
        simp only [Finset.mem_filter]
        refine ⟨hx, ?_, ?_⟩
        · simpa using hcon.1
        · simpa using hcon.2
      rw [hempty] at this
      simp at this
    · intro x hx0 hx1
      simpa using ⟨hx0, hx1⟩
  | succ k ih =>
    intro S hS hcard
    by_cases hne : (S.filter (fun x => x ≠ 0 ∧ x ≠ 1)).Nonempty
    · obtain ⟨lam, hlam⟩ := hne
      rw [Finset.mem_filter] at hlam
      obtain ⟨hlamS, hlam0, hlam1⟩ := hlam
      have hb := hS lam hlamS
      have h0 : 0 < lam := lt_of_le_of_ne hb.1 (Ne.symm hlam0)
      have h1 : lam < 1 := lt_of_le_of_ne hb.2 hlam1
      obtain ⟨m, n, hm, hn, hmn⟩ := exists_num_den h0 h1
      set B := belyiPoly m n with hB
      set e : ℚ → ℚ := fun x => B.eval x with he
      set S' : Finset ℚ := S.image e with hS'
      -- the new set is again contained in the unit interval
      have hS'mem : ∀ y ∈ S', 0 ≤ y ∧ y ≤ 1 := by
        intro y hy
        rw [hS', Finset.mem_image] at hy
        obtain ⟨x, hx, rfl⟩ := hy
        exact belyiPoly_eval_mem_Icc hm hn (hS x hx).1 (hS x hx).2
      -- the number of points outside `{0,1}` strictly decreases
      have hsub : S'.filter (fun y => y ≠ 0 ∧ y ≠ 1) ⊆
          ((S.filter (fun x => x ≠ 0 ∧ x ≠ 1)).erase lam).image e := by
        intro y hy
        rw [Finset.mem_filter, hS', Finset.mem_image] at hy
        obtain ⟨⟨x, hxS, rfl⟩, hy0, hy1⟩ := hy
        have hx0 : x ≠ 0 := by
          rintro rfl
          exact hy0 (by simpa [he, hB] using belyiPoly_eval_zero (m := m) (n := n) hm)
        have hx1 : x ≠ 1 := by
          rintro rfl
          exact hy0 (by simpa [he, hB] using belyiPoly_eval_one (m := m) (n := n) hn)
        have hxlam : x ≠ lam := by
          rintro rfl
          refine hy1 ?_
          have : (belyiPoly m n).eval ((m : ℚ) / ((m : ℚ) + (n : ℚ))) = 1 :=
            belyiPoly_eval_lambda hm hn
          rw [hmn] at this
          simpa [he, hB] using this
        exact Finset.mem_image.2 ⟨x, Finset.mem_erase.2 ⟨hxlam,
          Finset.mem_filter.2 ⟨hxS, hx0, hx1⟩⟩, rfl⟩
      have hcard' : (S'.filter (fun y => y ≠ 0 ∧ y ≠ 1)).card ≤ k := by
        have h2 := Finset.card_le_card hsub
        have h3 := Finset.card_image_le (s := (S.filter (fun x => x ≠ 0 ∧ x ≠ 1)).erase lam) (f := e)
        have h4 : ((S.filter (fun x => x ≠ 0 ∧ x ≠ 1)).erase lam).card
            = (S.filter (fun x => x ≠ 0 ∧ x ≠ 1)).card - 1 :=
          Finset.card_erase_of_mem (Finset.mem_filter.2 ⟨hlamS, hlam0, hlam1⟩)
        have h5 : 1 ≤ (S.filter (fun x => x ≠ 0 ∧ x ≠ 1)).card :=
          Finset.card_pos.2 ⟨lam, Finset.mem_filter.2 ⟨hlamS, hlam0, hlam1⟩⟩
        omega
      obtain ⟨g, hg⟩ := ih S' hS'mem hcard'
      obtain ⟨hgB, hgS, hg0, hg1, hgIcc⟩ := hg
      refine ⟨g.comp B, ?_, ?_, ?_, ?_, ?_⟩
      · refine IsBelyiPolynomial.comp (by rw [hB, belyiPoly_natDegree hm hn]; omega) hgB ?_
        · intro z hz
          have hcv := belyiPoly_critical_value hm hn z hz
          rcases hcv with hcv | hcv <;> rw [hcv]
          · have : aeval ((0 : ℚ) : ℂ) g = 0 ∨ aeval ((0 : ℚ) : ℂ) g = 1 := aeval_rat_mem hg0
            simpa using this
          · have : aeval ((1 : ℚ) : ℂ) g = 0 ∨ aeval ((1 : ℚ) : ℂ) g = 1 := aeval_rat_mem hg1
            simpa using this
      · intro x hx
        rw [eval_comp]
        exact hgS _ (Finset.mem_image.2 ⟨x, hx, rfl⟩)
      · rw [eval_comp, hB, belyiPoly_eval_zero (m := m) (n := n) hm]
        exact hg0
      · rw [eval_comp, hB, belyiPoly_eval_one (m := m) (n := n) hn]
        exact hg0
      · intro x hx0 hx1
        rw [eval_comp]
        have := belyiPoly_eval_mem_Icc hm hn hx0 hx1
        exact hgIcc _ this.1 this.2
    · rw [Finset.not_nonempty_iff_eq_empty] at hne
      refine ⟨X, isBelyiPolynomial_X, ?_, by simp, by simp, ?_⟩
      · intro x hx
        by_contra hcon
        push_neg at hcon
        have : x ∈ S.filter (fun x => x ≠ 0 ∧ x ≠ 1) := by
          simp only [Finset.mem_filter]
          exact ⟨hx, by simpa using hcon.1, by simpa using hcon.2⟩
        rw [hne] at this
        simp at this
      · intro x hx0 hx1
        simpa using ⟨hx0, hx1⟩

/-- Belyi's construction for a finite set of rationals contained in `[0,1]`. -/
lemma exists_ratBelyi (S : Finset ℚ) (hS : ∀ x ∈ S, 0 ≤ x ∧ x ≤ 1) :
    ∃ f : ℚ[X], RatBelyi S f :=
  exists_ratBelyi_aux _ S hS le_rfl

/-- Belyi's construction for an arbitrary finite set of rational numbers: there is a
non-constant `f ∈ ℚ[X]`, all of whose finite critical values lie in `{0,1}`, taking every
element of `S` to `0` or `1`. -/
theorem exists_belyiPolynomial_of_rat (S : Finset ℚ) :
    ∃ f : ℚ[X], IsBelyiPolynomial f ∧ ∀ x ∈ S, f.eval x = 0 ∨ f.eval x = 1 := by
  rcases S.eq_empty_or_nonempty with rfl | hne
  · exact ⟨X, isBelyiPolynomial_X, by simp⟩
  · set a := S.min' hne with ha
    set b := S.max' hne with hb
    set d : ℚ := if b - a = 0 then 1 else b - a with hd
    have hdpos : 0 < d := by
      rcases eq_or_ne (b - a) 0 with h | h
      · simp [hd, h]
      · have hab : a ≤ b := S.min'_le_max' hne
        have : 0 < b - a := lt_of_le_of_ne (by linarith) (Ne.symm h)
        simp [hd, h, this]
    set A : ℚ[X] := C d⁻¹ * (X - C a) with hA
    have hAdeg : A.natDegree = 1 := by
      rw [hA, natDegree_mul (by simp [hdpos.ne']) (X_sub_C_ne_zero a), natDegree_C,
        natDegree_X_sub_C]
    have hAnocrit : ∀ z : ℂ, aeval z (derivative A) ≠ 0 := by
      intro z hz
      rw [hA] at hz
      simp only [derivative_mul, derivative_C, derivative_X, zero_mul, zero_add, map_sub] at hz
      have hne0 : (d⁻¹ : ℚ) ≠ 0 := inv_ne_zero hdpos.ne'
      exact hne0 (by simpa using hz)
    have hAbelyi : IsBelyiPolynomial A :=
      ⟨by rw [hAdeg]; omega, fun z hz => absurd hz (hAnocrit z)⟩
    have hAmem : ∀ x ∈ S, 0 ≤ A.eval x ∧ A.eval x ≤ 1 := by
      intro x hx
      have hax : a ≤ x := S.min'_le x hx
      have hxb : x ≤ b := S.le_max' x hx
      have hev : A.eval x = (x - a) / d := by rw [hA]; simp [div_eq_inv_mul]
      rw [hev]
      constructor
      · exact div_nonneg (by linarith) hdpos.le
      · rw [div_le_one hdpos]
        rcases eq_or_ne (b - a) 0 with h | h
        · have : x = a := by
            have : b = a := by linarith
            rw [this] at hxb; linarith
          simp [hd, h, this]
        · simp only [hd, if_neg h]
          linarith
    obtain ⟨g, hgB, hgS, _, _, _⟩ := exists_ratBelyi (S.image (fun x => A.eval x)) (by
      intro y hy
      rw [Finset.mem_image] at hy
      obtain ⟨x, hx, rfl⟩ := hy
      exact hAmem x hx)
    refine ⟨g.comp A, ?_, ?_⟩
    · exact IsBelyiPolynomial.comp hAbelyi.1 hgB (fun z hz => absurd hz (hAnocrit z))
    · intro x hx
      rw [eval_comp]
      exact hgS _ (Finset.mem_image.2 ⟨x, hx, rfl⟩)

end Math2

import Mathlib

/-!
# The elementary Belyi polynomials `x ↦ c · x^m (1-x)^n`

This file develops the basic properties of the polynomials used in Belyi's construction:
for positive naturals `m, n` the polynomial
`B_{m,n}(x) = ((m+n)^(m+n)/(m^m n^n)) · x^m (1-x)^n`
has all of its finite critical values in `{0, 1}`, sends `0, 1` to `0`, sends `m/(m+n)` to `1`,
and maps the unit interval into itself.
-/

set_option maxRecDepth 8000

namespace Math2

open Polynomial

/-- The normalizing constant `(m+n)^(m+n) / (m^m n^n)`. -/
noncomputable def bcoef (m n : ℕ) : ℚ := ((m + n : ℚ)) ^ (m + n) / ((m : ℚ) ^ m * (n : ℚ) ^ n)

/-- The Belyi polynomial `c · X^m (1-X)^n`, normalized so that its value at `m/(m+n)` is `1`. -/
noncomputable def belyiPoly (m n : ℕ) : ℚ[X] := C (bcoef m n) * X ^ m * (1 - X) ^ n

lemma bcoef_pos {m n : ℕ} (hm : 0 < m) (hn : 0 < n) : 0 < bcoef m n := by
  have hm' : (0 : ℚ) < (m : ℚ) := by exact_mod_cast hm
  have hn' : (0 : ℚ) < (n : ℚ) := by exact_mod_cast hn
  unfold bcoef
  positivity

lemma belyiPoly_eval (m n : ℕ) (x : ℚ) :
    (belyiPoly m n).eval x = bcoef m n * x ^ m * (1 - x) ^ n := by
  simp [belyiPoly]

lemma belyiPoly_aeval {K : Type*} [Field K] [Algebra ℚ K] (m n : ℕ) (z : K) :
    aeval z (belyiPoly m n) = algebraMap ℚ K (bcoef m n) * z ^ m * (1 - z) ^ n := by
  simp [belyiPoly]

/-- `B_{m,n}(0) = 0`. -/
lemma belyiPoly_eval_zero {m n : ℕ} (hm : 0 < m) : (belyiPoly m n).eval 0 = 0 := by
  simp [belyiPoly_eval, zero_pow hm.ne']

/-- `B_{m,n}(1) = 0`. -/
lemma belyiPoly_eval_one {m n : ℕ} (hn : 0 < n) : (belyiPoly m n).eval 1 = 0 := by
  simp [belyiPoly_eval, zero_pow hn.ne']

/-- `B_{m,n}(m/(m+n)) = 1`. -/
lemma belyiPoly_eval_lambda {m n : ℕ} (hm : 0 < m) (hn : 0 < n) :
    (belyiPoly m n).eval ((m : ℚ) / ((m : ℚ) + n)) = 1 := by
  have hm' : (0 : ℚ) < (m : ℚ) := by exact_mod_cast hm
  have hn' : (0 : ℚ) < (n : ℚ) := by exact_mod_cast hn
  have hN : (0 : ℚ) < (m : ℚ) + n := by linarith
  have h1 : (1 : ℚ) - (m : ℚ) / ((m : ℚ) + n) = (n : ℚ) / ((m : ℚ) + n) := by
    field_simp; ring
  rw [belyiPoly_eval, h1]
  unfold bcoef
  rw [div_pow, div_pow, pow_add]
  field_simp

lemma belyiPoly_natDegree {m n : ℕ} (hm : 0 < m) (hn : 0 < n) :
    (belyiPoly m n).natDegree = m + n := by
  have hc : bcoef m n ≠ 0 := (bcoef_pos hm hn).ne'
  have h1 : ((1 : ℚ[X]) - X).natDegree = 1 := by
    have h : ((1 : ℚ[X]) - X) = -(X - C 1) := by simp only [C_1]; ring
    rw [h, natDegree_neg, natDegree_X_sub_C]
  unfold belyiPoly
  rw [natDegree_mul, natDegree_mul, natDegree_C, natDegree_pow, natDegree_pow, natDegree_X, h1]
  · ring
  · exact (C_ne_zero.mpr hc)
  · exact pow_ne_zero _ X_ne_zero
  · exact mul_ne_zero (C_ne_zero.mpr hc) (pow_ne_zero _ X_ne_zero)
  · refine pow_ne_zero _ ?_
    intro h
    have := congrArg (fun p => Polynomial.eval (0 : ℚ) p) h
    simp at this

/-- The derivative of `B_{m,n}` factors as `c · X^(m-1) (1-X)^(n-1) (m - (m+n) X)`. -/
lemma belyiPoly_derivative (a b : ℕ) :
    derivative (belyiPoly (a + 1) (b + 1)) =
      C (bcoef (a + 1) (b + 1)) *
        (X ^ a * (1 - X) ^ b * (C ((a : ℚ) + 1) - C ((a : ℚ) + (b : ℚ) + 2) * X)) := by
  unfold belyiPoly
  simp only [derivative_mul, derivative_pow, derivative_X, derivative_C, derivative_sub,
    derivative_one, zero_mul, zero_add, mul_one, Nat.add_sub_cancel]
  simp only [Nat.cast_add, Nat.cast_one, C_add, C_1, map_ofNat]
  ring

section CriticalValues

/-- Evaluating a rational polynomial at a rational point, seen inside `ℂ`. -/
lemma aeval_rat (p : ℚ[X]) (q : ℚ) : aeval (q : ℂ) p = ((p.eval q : ℚ) : ℂ) := by
  have h : ((q : ℂ)) = algebraMap ℚ ℂ q := by simp
  rw [h, aeval_algebraMap_apply]
  simp

/-- Every finite critical value of `B_{m,n}` lies in `{0, 1}`. -/
lemma belyiPoly_critical_value {m n : ℕ} (hm : 0 < m) (hn : 0 < n) (z : ℂ)
    (hz : aeval z (derivative (belyiPoly m n)) = 0) :
    aeval z (belyiPoly m n) = 0 ∨ aeval z (belyiPoly m n) = 1 := by
  obtain ⟨a, rfl⟩ : ∃ a, m = a + 1 := ⟨m - 1, by omega⟩
  obtain ⟨b, rfl⟩ : ∃ b, n = b + 1 := ⟨n - 1, by omega⟩
  have hc : bcoef (a + 1) (b + 1) ≠ 0 := (bcoef_pos hm hn).ne'
  have hcK : algebraMap ℚ ℂ (bcoef (a + 1) (b + 1)) ≠ 0 := by
    simpa using (algebraMap ℚ ℂ).injective.ne hc
  rw [belyiPoly_derivative] at hz
  simp only [map_mul, map_sub, aeval_C, aeval_X, map_pow, map_one, map_add, map_natCast,
    map_ofNat] at hz
  rcases mul_eq_zero.1 hz with h | h
  · exact absurd h hcK
  rcases mul_eq_zero.1 h with h' | h'
  · rcases mul_eq_zero.1 h' with h'' | h''
    · -- z = 0
      have hz0 : z = 0 := pow_eq_zero_iff' .. |>.1 h'' |>.1
      left
      rw [belyiPoly_aeval, hz0]
      simp
    · -- z = 1
      have hz1 : z = 1 := by
        have h3 : (1 : ℂ) - z = 0 := pow_eq_zero_iff' (M₀ := ℂ) (a := 1 - z) (n := b) |>.1 h'' |>.1
        linear_combination -h3
      left
      rw [belyiPoly_aeval, hz1]
      simp
  · -- z = (a+1)/(a+b+2)
    right
    set q : ℚ := ((a : ℚ) + 1) / (((a : ℚ) + 1) + ((b : ℚ) + 1)) with hq
    have hden : (((a : ℂ) + 1) + ((b : ℂ) + 1)) ≠ 0 := by
      intro hcon
      have h1 : (((a + b + 2 : ℕ) : ℂ)) = 0 := by push_cast; linear_combination hcon
      simp only [Nat.cast_eq_zero] at h1
      omega
    have hzq : z = (q : ℂ) := by
      rw [hq]
      push_cast
      field_simp
      linear_combination -h'
    rw [hzq, aeval_rat]
    have : (belyiPoly (a + 1) (b + 1)).eval q = 1 := by
      have := belyiPoly_eval_lambda (m := a + 1) (n := b + 1) (by omega) (by omega)
      rw [hq]
      push_cast at this ⊢
      exact this
    rw [this]
    norm_num

end CriticalValues

section UnitInterval

/-- A form of the weighted AM-GM inequality, proved from `1 + t ≤ exp t`. -/
lemma amgm_two_weights (m n : ℕ) (u v : ℝ) (hu : 0 ≤ u) (hv : 0 ≤ v)
    (h : (m : ℝ) * u + (n : ℝ) * v = (m : ℝ) + (n : ℝ)) : u ^ m * v ^ n ≤ 1 := by
  have h1 : u ≤ Real.exp (u - 1) := by have := Real.add_one_le_exp (u - 1); linarith
  have h2 : v ≤ Real.exp (v - 1) := by have := Real.add_one_le_exp (v - 1); linarith
  have h3 : u ^ m ≤ Real.exp ((m : ℝ) * (u - 1)) := by
    calc u ^ m ≤ (Real.exp (u - 1)) ^ m := pow_le_pow_left₀ hu h1 m
    _ = Real.exp ((m : ℝ) * (u - 1)) := by rw [← Real.exp_nat_mul]
  have h4 : v ^ n ≤ Real.exp ((n : ℝ) * (v - 1)) := by
    calc v ^ n ≤ (Real.exp (v - 1)) ^ n := pow_le_pow_left₀ hv h2 n
    _ = Real.exp ((n : ℝ) * (v - 1)) := by rw [← Real.exp_nat_mul]
  calc u ^ m * v ^ n ≤ Real.exp ((m : ℝ) * (u - 1)) * Real.exp ((n : ℝ) * (v - 1)) :=
        mul_le_mul h3 h4 (by positivity) (by positivity)
    _ = Real.exp ((m : ℝ) * u + (n : ℝ) * v - ((m : ℝ) + (n : ℝ))) := by
        rw [← Real.exp_add]; ring_nf
    _ = 1 := by rw [h]; simp

lemma belyi_real_bound (m n : ℕ) (hm : 0 < m) (hn : 0 < n) (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    ((m + n : ℝ)) ^ (m + n) / ((m : ℝ) ^ m * (n : ℝ) ^ n) * x ^ m * (1 - x) ^ n ≤ 1 := by
  have hm' : (0 : ℝ) < m := by exact_mod_cast hm
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  have hx1' : (0 : ℝ) ≤ 1 - x := by linarith
  set N : ℝ := (m : ℝ) + n with hN
  have hNpos : 0 < N := by positivity
  have key := amgm_two_weights m n (x * N / m) ((1 - x) * N / n) (by positivity) (by positivity)
    (by field_simp; ring)
  have hx : (x * N / m) ^ m * ((1 - x) * N / n) ^ n
      = N ^ (m + n) / ((m : ℝ) ^ m * (n : ℝ) ^ n) * x ^ m * (1 - x) ^ n := by
    rw [div_pow, div_pow, mul_pow, mul_pow, pow_add]
    field_simp
  rw [hx] at key
  exact key

/-- `B_{m,n}` maps the rational points of the unit interval into the unit interval. -/
lemma belyiPoly_eval_mem_Icc {m n : ℕ} (hm : 0 < m) (hn : 0 < n) {x : ℚ}
    (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    0 ≤ (belyiPoly m n).eval x ∧ (belyiPoly m n).eval x ≤ 1 := by
  have hc := bcoef_pos hm hn
  have hx1' : (0 : ℚ) ≤ 1 - x := by linarith
  refine ⟨?_, ?_⟩
  · rw [belyiPoly_eval]
    positivity
  · rw [belyiPoly_eval]
    have hreal := belyi_real_bound m n hm hn (x : ℝ) (by exact_mod_cast hx0) (by exact_mod_cast hx1)
    have hcast : ((bcoef m n * x ^ m * (1 - x) ^ n : ℚ) : ℝ)
        = ((m + n : ℝ)) ^ (m + n) / ((m : ℝ) ^ m * (n : ℝ) ^ n) * (x : ℝ) ^ m * (1 - (x : ℝ)) ^ n := by
      unfold bcoef
      push_cast
      ring
    have : ((bcoef m n * x ^ m * (1 - x) ^ n : ℚ) : ℝ) ≤ ((1 : ℚ) : ℝ) := by
      rw [hcast]; simpa using hreal
    exact_mod_cast this

end UnitInterval

end Math2

/-
# Belyi Theorem
Category: Frontier Math
Target: Math2.belyi_theorem
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/
-- (Lean 4 requires `import` lines to precede any command, so the header above is a plain
-- block comment rather than a module docstring.)

import RequestProject.BelyiRat

/-!
# Belyi Theorem
Category: Frontier Math
Target: Math2.belyi_theorem
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

/-!
## Belyi's theorem for the projective line with marked points

We work with the following concrete incarnation of the theorem.  A *Belyi map* here is a
non-constant polynomial `f ∈ ℚ[X]`, viewed as a morphism `ℙ¹ → ℙ¹` defined over `ℚ`, all of whose
finite critical values lie in `{0, 1}`; equivalently, `f` is unramified outside the fibre over
`{0, 1, ∞}` (the point `∞` is totally ramified for a polynomial).  This is `IsBelyiPolynomial`.

The curve under consideration is the projective line together with a finite set `S ⊆ ℂ` of marked
points, and "defined over `ℚ̄`" means that every marked point is algebraic over `ℚ`.

`Math2.belyi_theorem` states that the marked points are defined over `ℚ̄` if and only if there is a
Belyi map taking every marked point into `{0, 1} ⊆ f⁻¹({0,1,∞})`.

The easy direction is that a point sent to `0` or `1` by a nonzero rational polynomial is
algebraic.  The substantive direction is Belyi's construction: first the degrees of the marked
points are reduced by repeatedly applying minimal polynomials (each such step adds the critical
values of the minimal polynomial to the set of marked points, but these have strictly smaller
degree), and then the resulting rational marked points are pushed into `{0, 1}` by the
polynomials `x ↦ c · x^m (1-x)^n` of `RequestProject.BelyiPoly`.
-/

set_option maxRecDepth 8000

namespace Math2

open Polynomial IntermediateField

/-- The degree over `ℚ` of a complex number. -/
noncomputable def algDeg (s : ℂ) : ℕ := (minpoly ℚ s).natDegree

lemma isIntegral_aeval {s : ℂ} (hs : IsIntegral ℚ s) (Q : ℚ[X]) : IsIntegral ℚ (aeval s Q) := by
  have hfin : FiniteDimensional ℚ ℚ⟮s⟯ := adjoin.finiteDimensional hs
  have hmem : aeval s Q ∈ ℚ⟮s⟯ :=
    IntermediateField.algebra_adjoin_le_adjoin ℚ {s} (Polynomial.aeval_mem_adjoin_singleton ℚ s)
  have h : IsIntegral ℚ (⟨aeval s Q, hmem⟩ : ℚ⟮s⟯) := IsIntegral.of_finite ℚ _
  exact h.map (IntermediateField.val ℚ⟮s⟯)

/-- A polynomial expression in an algebraic number has degree at most that of the number. -/
lemma algDeg_aeval_le {s : ℂ} (hs : IsIntegral ℚ s) (Q : ℚ[X]) : algDeg (aeval s Q) ≤ algDeg s := by
  have hfin : FiniteDimensional ℚ ℚ⟮s⟯ := adjoin.finiteDimensional hs
  have hmem : aeval s Q ∈ ℚ⟮s⟯ :=
    IntermediateField.algebra_adjoin_le_adjoin ℚ {s} (Polynomial.aeval_mem_adjoin_singleton ℚ s)
  have hle : ℚ⟮aeval s Q⟯ ≤ ℚ⟮s⟯ := (IntermediateField.adjoin_simple_le_iff).2 hmem
  have h1 : Module.finrank ℚ ℚ⟮aeval s Q⟯ ≤ Module.finrank ℚ ℚ⟮s⟯ := finrank_le_of_le_right hle
  rwa [adjoin.finrank (isIntegral_aeval hs Q), adjoin.finrank hs] at h1

lemma algDeg_pos {s : ℂ} (hs : IsIntegral ℚ s) : 0 < algDeg s := minpoly.natDegree_pos hs

/-- A complex number of degree one over `ℚ` is rational. -/
lemma exists_rat_of_algDeg_le_one {s : ℂ} (hs : IsIntegral ℚ s) (h : algDeg s ≤ 1) :
    ∃ q : ℚ, s = (q : ℂ) := by
  have h1 : algDeg s = 1 := le_antisymm h (algDeg_pos hs)
  rw [algDeg, minpoly.natDegree_eq_one_iff] at h1
  obtain ⟨q, hq⟩ := h1
  exact ⟨q, by simp [← hq]⟩

open Classical in
/-- A choice of rational number representing a complex number, when possible. -/
noncomputable def ratPart (s : ℂ) : ℚ := if h : ∃ q : ℚ, s = (q : ℂ) then h.choose else 0

lemma ratPart_spec {s : ℂ} (h : ∃ q : ℚ, s = (q : ℂ)) : ((ratPart s : ℚ) : ℂ) = s := by
  classical
  rw [ratPart, dif_pos h]
  exact (h.choose_spec).symm

/-- The main construction: for any finite set of algebraic numbers of degree at most `d` there is
a Belyi polynomial mapping all of them into `{0, 1}`. -/
lemma exists_belyiPolynomial_of_degree_le (d : ℕ) : ∀ S : Finset ℂ, (∀ s ∈ S, IsIntegral ℚ s) →
    (∀ s ∈ S, algDeg s ≤ d) →
    ∃ f : ℚ[X], IsBelyiPolynomial f ∧ ∀ s ∈ S, aeval s f = 0 ∨ aeval s f = 1 := by
  induction d using Nat.strong_induction_on with
  | _ d IH =>
    by_cases hd : d ≤ 1
    · -- all marked points are rational
      intro S hint hdeg
      obtain ⟨f, hf, hval⟩ := exists_belyiPolynomial_of_rat (S.image ratPart)
      refine ⟨f, hf, ?_⟩
      intro s hs
      have hq : ∃ q : ℚ, s = (q : ℂ) :=
        exists_rat_of_algDeg_le_one (hint s hs) (le_trans (hdeg s hs) hd)
      have hspec := ratPart_spec hq
      have := hval (ratPart s) (Finset.mem_image.2 ⟨s, hs, rfl⟩)
      rw [← hspec]
      exact aeval_rat_mem this
    · push_neg at hd
      have inner : ∀ k : ℕ, ∀ S : Finset ℂ, (∀ s ∈ S, IsIntegral ℚ s) → (∀ s ∈ S, algDeg s ≤ d) →
          (S.filter (fun s => algDeg s = d)).card ≤ k →
          ∃ f : ℚ[X], IsBelyiPolynomial f ∧ ∀ s ∈ S, aeval s f = 0 ∨ aeval s f = 1 := by
        intro k
        induction k with
        | zero =>
          intro S hint hdeg hcard
          have hempty : S.filter (fun s => algDeg s = d) = ∅ := Finset.card_eq_zero.1 (by omega)
          refine IH (d - 1) (by omega) S hint ?_
          intro s hs
          have hne : algDeg s ≠ d := by
            intro hcon
            have : s ∈ S.filter (fun s => algDeg s = d) := Finset.mem_filter.2 ⟨hs, hcon⟩
            rw [hempty] at this
            simp at this
          have := hdeg s hs
          omega
        | succ k ihk =>
          intro S hint hdeg hcard
          by_cases hne : (S.filter (fun s => algDeg s = d)).Nonempty
          · obtain ⟨alpha, halpha⟩ := hne
            rw [Finset.mem_filter] at halpha
            obtain ⟨halphaS, halphadeg⟩ := halpha
            have hai : IsIntegral ℚ alpha := hint alpha halphaS
            set P : ℚ[X] := minpoly ℚ alpha with hP
            have hPdeg : P.natDegree = d := halphadeg
            have hPne : P ≠ 0 := minpoly.ne_zero hai
            have hPderiv : (derivative P).natDegree < d := by
              rw [← hPdeg]
              exact natDegree_derivative_lt (by rw [hPdeg]; omega)
            have hderivne : derivative P ≠ 0 := by
              intro hcon
              have := natDegree_eq_zero_of_derivative_eq_zero hcon
              rw [hPdeg] at this
              omega
            -- the critical values of `P`
            set crit : Finset ℂ := ((derivative P).aroots ℂ).toFinset.image (fun z => aeval z P)
              with hcrit
            set S' : Finset ℂ := S.image (fun s => aeval s P) ∪ crit with hS'
            have hcritdeg : ∀ t ∈ crit, IsIntegral ℚ t ∧ algDeg t ≤ d - 1 := by
              intro t ht
              rw [hcrit, Finset.mem_image] at ht
              obtain ⟨z, hz, rfl⟩ := ht
              rw [Multiset.mem_toFinset, Polynomial.mem_aroots] at hz
              obtain ⟨-, hz0⟩ := hz
              have hzalg : IsAlgebraic ℚ z := ⟨derivative P, hderivne, hz0⟩
              have hzint : IsIntegral ℚ z := hzalg.isIntegral
              have hdvd : minpoly ℚ z ∣ derivative P := minpoly.dvd ℚ z hz0
              have hzdeg : algDeg z ≤ d - 1 := by
                have h6 : algDeg z ≤ (derivative P).natDegree :=
                  Polynomial.natDegree_le_of_dvd hdvd hderivne
                omega
              exact ⟨isIntegral_aeval hzint P, le_trans (algDeg_aeval_le hzint P) hzdeg⟩
            have hS'int : ∀ t ∈ S', IsIntegral ℚ t := by
              intro t ht
              rw [hS', Finset.mem_union] at ht
              rcases ht with ht | ht
              · rw [Finset.mem_image] at ht
                obtain ⟨s, hs, rfl⟩ := ht
                exact isIntegral_aeval (hint s hs) P
              · exact (hcritdeg t ht).1
            have hS'deg : ∀ t ∈ S', algDeg t ≤ d := by
              intro t ht
              rw [hS', Finset.mem_union] at ht
              rcases ht with ht | ht
              · rw [Finset.mem_image] at ht
                obtain ⟨s, hs, rfl⟩ := ht
                exact le_trans (algDeg_aeval_le (hint s hs) P) (hdeg s hs)
              · exact le_trans (hcritdeg t ht).2 (by omega)
            -- the number of points of maximal degree strictly decreases
            have hsub : S'.filter (fun t => algDeg t = d) ⊆
                ((S.filter (fun s => algDeg s = d)).erase alpha).image (fun s => aeval s P) := by
              intro t ht
              rw [Finset.mem_filter] at ht
              obtain ⟨htS', htdeg⟩ := ht
              rw [hS', Finset.mem_union] at htS'
              rcases htS' with htS' | htS'
              · rw [Finset.mem_image] at htS'
                obtain ⟨s, hs, rfl⟩ := htS'
                have hsdeg : algDeg s = d :=
                  le_antisymm (hdeg s hs) (by rw [← htdeg]; exact algDeg_aeval_le (hint s hs) P)
                have hsalpha : s ≠ alpha := by
                  rintro rfl
                  have h0 : aeval s P = 0 := by rw [hP]; exact minpoly.aeval ℚ s
                  rw [h0] at htdeg
                  have : algDeg (0 : ℂ) = 1 := by
                    rw [algDeg, minpoly.zero, natDegree_X]
                  omega
                exact Finset.mem_image.2 ⟨s, Finset.mem_erase.2 ⟨hsalpha,
                  Finset.mem_filter.2 ⟨hs, hsdeg⟩⟩, rfl⟩
              · exfalso
                have := (hcritdeg t htS').2
                omega
            have hcard' : (S'.filter (fun t => algDeg t = d)).card ≤ k := by
              have h2 := Finset.card_le_card hsub
              have h3 := Finset.card_image_le
                (s := (S.filter (fun s => algDeg s = d)).erase alpha) (f := fun s => aeval s P)
              have h4 : ((S.filter (fun s => algDeg s = d)).erase alpha).card
                  = (S.filter (fun s => algDeg s = d)).card - 1 :=
                Finset.card_erase_of_mem (Finset.mem_filter.2 ⟨halphaS, halphadeg⟩)
              have h5 : 1 ≤ (S.filter (fun s => algDeg s = d)).card :=
                Finset.card_pos.2 ⟨alpha, Finset.mem_filter.2 ⟨halphaS, halphadeg⟩⟩
              omega
            obtain ⟨g, hgB, hgval⟩ := ihk S' hS'int hS'deg hcard'
            refine ⟨g.comp P, ?_, ?_⟩
            · refine IsBelyiPolynomial.comp (by rw [hPdeg]; omega) hgB ?_
              intro z hz
              have hmem : aeval z P ∈ S' := by
                rw [hS', Finset.mem_union]
                right
                rw [hcrit]
                exact Finset.mem_image.2 ⟨z, by
                  rw [Multiset.mem_toFinset, Polynomial.mem_aroots]
                  exact ⟨hderivne, hz⟩, rfl⟩
              exact hgval _ hmem
            · intro s hs
              rw [aeval_comp]
              exact hgval _ (by
                rw [hS', Finset.mem_union]
                exact Or.inl (Finset.mem_image.2 ⟨s, hs, rfl⟩))
          · rw [Finset.not_nonempty_iff_eq_empty] at hne
            refine IH (d - 1) (by omega) S hint ?_
            intro s hs
            have hne' : algDeg s ≠ d := by
              intro hcon
              have : s ∈ S.filter (fun s => algDeg s = d) := Finset.mem_filter.2 ⟨hs, hcon⟩
              rw [hne] at this
              simp at this
            have := hdeg s hs
            omega
      intro S hint hdeg
      exact inner _ S hint hdeg le_rfl

/-- **Belyi's theorem** for the projective line with marked points.

For a finite set `S ⊆ ℂ` of marked points on `ℙ¹`, the following are equivalent:

* every marked point is algebraic over `ℚ`, i.e. the marked curve `(ℙ¹, S)` is defined over `ℚ̄`;
* there is a Belyi map for it, namely a non-constant `f ∈ ℚ[X]` — a morphism `ℙ¹ → ℙ¹` defined
  over `ℚ` which is ramified only above `{0, 1, ∞}`, since all its finite critical values lie in
  `{0, 1}` and `∞` is totally ramified — carrying every marked point into `{0, 1}`, i.e. into
  the fibre above `{0, 1, ∞}`. -/
theorem belyi_theorem (S : Finset ℂ) :
    (∀ s ∈ S, IsAlgebraic ℚ s) ↔
      ∃ f : ℚ[X], IsBelyiPolynomial f ∧ ∀ s ∈ S, aeval s f = 0 ∨ aeval s f = 1 := by
  constructor
  · intro h
    refine exists_belyiPolynomial_of_degree_le (S.sup algDeg) S (fun s hs => (h s hs).isIntegral)
      (fun s hs => Finset.le_sup hs)
  · rintro ⟨f, hf, hval⟩ s hs
    have hf0 : f ≠ 0 := by
      intro hcon
      rw [hcon] at hf
      have h8 := hf.1
      simp at h8
    rcases hval s hs with hv | hv
    · exact ⟨f, hf0, hv⟩
    · refine ⟨f - C 1, ?_, ?_⟩
      · intro hcon
        have hfC : f = C 1 := by linear_combination (norm := ring_nf) hcon
        rw [hfC] at hf
        have h7 := hf.1
        simp at h7
      · simp only [map_sub, map_one, hv, sub_self]

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

