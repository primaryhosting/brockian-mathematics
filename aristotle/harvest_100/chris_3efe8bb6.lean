/-
# Belyi Theorem
Category: Frontier Math
Target: Math2.belyi_theorem
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/
import Mathlib

/-!
# Belyi Theorem

Category: Frontier Math
Target: `Math2.belyi_theorem`
Provenance: Aristotle theorem prover (Harmonic)

## Contents

This file formalizes Belyi's theorem for the projective line with marked points, i.e. for the
curves `ℙ¹ \ S` where `S` is a finite set of points: such a marked curve is defined over `ℚ̄`
(all points of `S` are algebraic numbers) if and only if there is a Belyi map, i.e. a nonconstant
map `ℙ¹ → ℙ¹` defined over `ℚ` which is ramified only above `{0, 1, ∞}` and which sends `S`
into `{0, 1, ∞}`.

Belyi maps are realized here by polynomials `f ∈ ℚ[X]`; such an `f`, viewed as a self-map of
`ℙ¹`, sends `∞` to `∞`, so ramification above `∞` is automatic and the condition on the
ramification is that all *finite* critical values lie in `{0, 1}`.  This is `Math2.IsBelyi`.

The main result is `Math2.belyi_theorem`.  The non-trivial direction is Belyi's construction,
which is carried out in two steps:

* `Math2.rationalize`: composing with a suitable polynomial over `ℚ` one can force all critical
  values to be rational.  This is the induction on the degrees over `ℚ` of the critical values,
  using that composing with the minimal polynomial of a critical value of maximal degree `D`
  strictly decreases the number of critical values of degree `D`.
* `Math2.rat_reduction`: any finite set of *rational* points can be pushed into `{0, 1}` by a
  Belyi polynomial.  This is Belyi's classical argument with the polynomials
  `x ↦ c · x ^ a (1 - x) ^ n` (`Math2.belyiP`), which have all their critical values in `{0, 1}`
  and collapse `{0, 1, a / (a + n)}` into `{0, 1}`, combined with affine normalizations.
-/

open Polynomial

set_option maxHeartbeats 1000000

namespace Math2

noncomputable section

/-- The degree over `ℚ` of a complex number (`0` if transcendental). -/
def algDeg (t : ℂ) : ℕ := (minpoly ℚ t).natDegree

/-- The (finite) set of critical values of a rational polynomial, computed over `ℂ`. -/
def critF (f : ℚ[X]) : Finset ℂ :=
  (((derivative f).aroots ℂ).toFinset).image (fun z => aeval z f)

/-- A *Belyi polynomial*: a nonconstant polynomial with rational coefficients all of whose
critical values (over `ℂ`) lie in `{0, 1}`.  Viewed as a map `ℙ¹ → ℙ¹` such an `f` is
ramified only above `0`, `1` and `∞`. -/
def IsBelyi (f : ℚ[X]) : Prop :=
  0 < f.natDegree ∧ ∀ z : ℂ, aeval z (derivative f) = 0 → aeval z f = 0 ∨ aeval z f = 1

/-! ### Basic facts -/

lemma derivative_ne_zero_of_natDegree_pos {f : ℚ[X]} (hf : 0 < f.natDegree) :
    derivative f ≠ 0 := by
  intro h
  have := Polynomial.natDegree_eq_zero_of_derivative_eq_zero h
  omega

lemma mem_critF {f : ℚ[X]} (hf : derivative f ≠ 0) {w : ℂ} :
    w ∈ critF f ↔ ∃ z : ℂ, aeval z (derivative f) = 0 ∧ aeval z f = w := by
  simp [critF, hf]

lemma natDegree_pos_of_aeval_ne {f : ℚ[X]} {x y : ℂ} (h : aeval x f ≠ aeval y f) :
    0 < f.natDegree := by
  rcases Nat.eq_zero_or_pos f.natDegree with h0 | h1
  · exact absurd (by rw [Polynomial.eq_C_of_natDegree_eq_zero h0]; simp) h
  · exact h1

lemma aeval_derivative_comp (p f : ℚ[X]) (z : ℂ) :
    aeval z (derivative (p.comp f))
      = aeval z (derivative f) * aeval (aeval z f) (derivative p) := by
  rw [Polynomial.derivative_comp, map_mul, Polynomial.aeval_comp]

lemma isIntegral_aeval {z : ℂ} (hz : IsIntegral ℚ z) (p : ℚ[X]) : IsIntegral ℚ (aeval z p) := by
  have h2 : Algebra.IsIntegral ℚ (Algebra.adjoin ℚ ({z} : Set ℂ)) :=
    Algebra.IsIntegral.adjoin (by simpa using hz)
  have h3 : aeval z p ∈ Algebra.adjoin ℚ ({z} : Set ℂ) := aeval_mem_adjoin_singleton ℚ z
  have h4 := h2.isIntegral (⟨aeval z p, h3⟩ : Algebra.adjoin ℚ ({z} : Set ℂ))
  have h5 := (isIntegral_algHom_iff (Algebra.adjoin ℚ ({z} : Set ℂ)).val
    Subtype.val_injective).mpr h4
  simpa using h5

/-- Critical values of a composite: `crit (p ∘ f) ⊆ p (crit f) ∪ crit p`. -/
lemma critF_comp_subset {p f : ℚ[X]} (hp : 0 < p.natDegree) (hf : 0 < f.natDegree) :
    critF (p.comp f) ⊆ (critF f).image (fun w => aeval w p) ∪ critF p := by
  have hpf : 0 < (p.comp f).natDegree := by
    rw [Polynomial.natDegree_comp]; positivity
  intro w hw
  rw [mem_critF (derivative_ne_zero_of_natDegree_pos hpf)] at hw
  obtain ⟨z, hz, rfl⟩ := hw
  rw [aeval_derivative_comp] at hz
  rcases mul_eq_zero.1 hz with h | h
  · refine Finset.mem_union_left _ ?_
    refine Finset.mem_image.2 ⟨aeval z f, ?_, ?_⟩
    · exact (mem_critF (derivative_ne_zero_of_natDegree_pos hf)).2 ⟨z, h, rfl⟩
    · exact (Polynomial.aeval_comp z).symm
  · refine Finset.mem_union_right _ ?_
    rw [mem_critF (derivative_ne_zero_of_natDegree_pos hp)]
    exact ⟨aeval z f, h, (Polynomial.aeval_comp z).symm⟩

lemma isIntegral_of_mem_critF {f : ℚ[X]} (hf : 0 < f.natDegree) {w : ℂ} (hw : w ∈ critF f) :
    IsIntegral ℚ w := by
  rw [mem_critF (derivative_ne_zero_of_natDegree_pos hf)] at hw
  obtain ⟨z, hz, rfl⟩ := hw
  have hzalg : IsAlgebraic ℚ z := ⟨derivative f, derivative_ne_zero_of_natDegree_pos hf, hz⟩
  exact isIntegral_aeval hzalg.isIntegral f

lemma algDeg_le_of_root {q : ℚ[X]} (hq : q ≠ 0) {z : ℂ} (hz : aeval z q = 0) :
    algDeg z ≤ q.natDegree :=
  Polynomial.natDegree_le_of_dvd (minpoly.dvd ℚ z hz) hq

lemma algDeg_aeval_le (p : ℚ[X]) {t : ℂ} (ht : IsIntegral ℚ t) :
    algDeg (aeval t p) ≤ algDeg t := by
  have hu' : IsIntegral ℚ (aeval t p) := isIntegral_aeval ht p
  have hu : aeval t p ∈ IntermediateField.adjoin ℚ ({t} : Set ℂ) := by
    have hsub : Algebra.adjoin ℚ ({t} : Set ℂ) ≤
        (IntermediateField.adjoin ℚ ({t} : Set ℂ)).toSubalgebra := by
      rw [Algebra.adjoin_le_iff]
      rintro x hx
      simp only [Set.mem_singleton_iff] at hx
      exact hx ▸ IntermediateField.mem_adjoin_simple_self ℚ t
    exact hsub (aeval_mem_adjoin_singleton ℚ t)
  have hle : IntermediateField.adjoin ℚ ({aeval t p} : Set ℂ) ≤
      IntermediateField.adjoin ℚ ({t} : Set ℂ) := IntermediateField.adjoin_simple_le_iff.mpr hu
  have hfd : FiniteDimensional ℚ (IntermediateField.adjoin ℚ ({t} : Set ℂ)) :=
    IntermediateField.adjoin.finiteDimensional ht
  have h1 : Module.finrank ℚ (IntermediateField.adjoin ℚ ({aeval t p} : Set ℂ))
      ≤ Module.finrank ℚ (IntermediateField.adjoin ℚ ({t} : Set ℂ)) :=
    LinearMap.finrank_le_finrank_of_injective
      (f := (IntermediateField.inclusion hle).toLinearMap)
      (IntermediateField.inclusion hle).injective
  rw [IntermediateField.adjoin.finrank hu', IntermediateField.adjoin.finrank ht] at h1
  exact h1

lemma rat_of_algDeg_le_one {t : ℂ} (ht : IsIntegral ℚ t) (h : algDeg t ≤ 1) :
    ∃ q : ℚ, algebraMap ℚ ℂ q = t := by
  have hmono : (minpoly ℚ t).Monic := minpoly.monic ht
  have hdeg : (minpoly ℚ t).natDegree = 1 := by
    have := minpoly.natDegree_pos ht
    unfold algDeg at h
    omega
  have h0 := minpoly.aeval ℚ t
  refine ⟨-(minpoly ℚ t).coeff 0, ?_⟩
  rw [hmono.eq_X_add_C hdeg] at h0
  simp only [map_add, aeval_X, aeval_C] at h0
  rw [map_neg]
  linear_combination -h0

/-! ### The Belyi polynomials `x ^ a (1 - x) ^ n` -/

/-- The normalizing constant of the Belyi polynomial. -/
def belyiC (a n : ℕ) : ℚ := ((a + n : ℕ) : ℚ) ^ (a + n) / ((a : ℚ) ^ a * (n : ℚ) ^ n)

/-- The Belyi polynomial `c * X ^ a * (1 - X) ^ n`, normalized so that its value at
`a / (a + n)` is `1`. -/
def belyiP (a n : ℕ) : ℚ[X] := C (belyiC a n) * (X ^ a * (1 - X) ^ n)

variable {A : Type*} [Field A] [Algebra ℚ A] [CharZero A]

omit [CharZero A] in
lemma aeval_belyiP (a n : ℕ) (x : A) :
    aeval x (belyiP a n) = algebraMap ℚ A (belyiC a n) * (x ^ a * (1 - x) ^ n) := by
  simp [belyiP]

omit [CharZero A] in
lemma algebraMap_belyiC (a n : ℕ) :
    algebraMap ℚ A (belyiC a n) = ((a : A) + (n : A)) ^ (a + n) / ((a : A) ^ a * (n : A) ^ n) := by
  simp [belyiC, map_div₀, map_mul, map_pow, map_add, map_natCast]

omit [CharZero A] in
lemma aeval_belyiP_zero (a n : ℕ) (ha : 0 < a) :
    aeval (0 : A) (belyiP a n) = 0 := by
  rw [aeval_belyiP]
  simp [zero_pow ha.ne']

omit [CharZero A] in
lemma aeval_belyiP_one (a n : ℕ) (hn : 0 < n) :
    aeval (1 : A) (belyiP a n) = 0 := by
  rw [aeval_belyiP]
  simp [zero_pow hn.ne']

lemma aeval_belyiP_lambda (a n : ℕ) (ha : 0 < a) (hn : 0 < n) :
    aeval ((a : A) / ((a : A) + (n : A))) (belyiP a n) = 1 := by
  have ha' : (a : A) ≠ 0 := Nat.cast_ne_zero.2 ha.ne'
  have hn' : (n : A) ≠ 0 := Nat.cast_ne_zero.2 hn.ne'
  have hs : (a : A) + (n : A) ≠ 0 := by
    have h := Nat.cast_ne_zero (R := A) (n := a + n) |>.2 (by omega : a + n ≠ 0)
    simpa using h
  rw [aeval_belyiP, algebraMap_belyiC]
  have h1 : (1 : A) - (a : A) / ((a : A) + (n : A)) = (n : A) / ((a : A) + (n : A)) := by
    field_simp
    ring
  rw [h1, div_pow, div_pow, pow_add]
  field_simp

omit [CharZero A] in
lemma aeval_derivative_belyiP (a n : ℕ) (x : A) :
    aeval x (derivative (belyiP a n))
      = algebraMap ℚ A (belyiC a n) *
          ((a : A) * x ^ (a - 1) * (1 - x) ^ n - (n : A) * x ^ a * (1 - x) ^ (n - 1)) := by
  rw [belyiP]
  simp [derivative_mul, derivative_pow, mul_sub]
  ring

omit [CharZero A] in
lemma algebraMap_belyiC_ne_zero (a n : ℕ) (ha : 0 < a) (hn : 0 < n) :
    algebraMap ℚ A (belyiC a n) ≠ 0 := by
  simp only [ne_eq, map_eq_zero]
  rw [belyiC]
  have hpos : ((a + n : ℕ) : ℚ) ^ (a + n) ≠ 0 := by positivity
  intro h
  rw [div_eq_zero_iff] at h
  rcases h with h | h
  · exact hpos h
  · rcases mul_eq_zero.1 h with h' | h'
    · exact absurd (pow_eq_zero_iff ha.ne' |>.1 h') (by exact_mod_cast ha.ne')
    · exact absurd (pow_eq_zero_iff hn.ne' |>.1 h') (by exact_mod_cast hn.ne')

/-- All critical values of a Belyi polynomial lie in `{0, 1}`. -/
lemma belyiP_crit (a n : ℕ) (ha : 0 < a) (hn : 0 < n) (z : A)
    (hz : aeval z (derivative (belyiP a n)) = 0) :
    aeval z (belyiP a n) = 0 ∨ aeval z (belyiP a n) = 1 := by
  have ha' : (a : A) ≠ 0 := Nat.cast_ne_zero.2 ha.ne'
  have hn' : (n : A) ≠ 0 := Nat.cast_ne_zero.2 hn.ne'
  have hs : (a : A) + (n : A) ≠ 0 := by
    have h := Nat.cast_ne_zero (R := A) (n := a + n) |>.2 (by omega : a + n ≠ 0)
    simpa using h
  by_cases hz0 : z = 0
  · left; rw [hz0]; exact aeval_belyiP_zero a n ha
  by_cases hz1 : z = 1
  · left; rw [hz1]; exact aeval_belyiP_one a n hn
  right
  rw [aeval_derivative_belyiP] at hz
  have hbr : (a : A) * z ^ (a - 1) * (1 - z) ^ n - (n : A) * z ^ a * (1 - z) ^ (n - 1) = 0 := by
    rcases mul_eq_zero.1 hz with h | h
    · exact absurd h (algebraMap_belyiC_ne_zero a n ha hn)
    · exact h
  have hza : z ^ a = z ^ (a - 1) * z := by
    conv_lhs => rw [show a = (a - 1) + 1 by omega]
    rw [pow_succ]
  have hzn : (1 - z) ^ n = (1 - z) ^ (n - 1) * (1 - z) := by
    conv_lhs => rw [show n = (n - 1) + 1 by omega]
    rw [pow_succ]
  rw [hza, hzn] at hbr
  have hfac : z ^ (a - 1) * (1 - z) ^ (n - 1) * ((a : A) * (1 - z) - (n : A) * z) = 0 := by
    linear_combination hbr
  have h1 : z ^ (a - 1) ≠ 0 := pow_ne_zero _ hz0
  have h2 : (1 - z) ^ (n - 1) ≠ 0 :=
    pow_ne_zero _ (fun h => hz1 (by linear_combination -h))
  have h3 : (a : A) * (1 - z) - (n : A) * z = 0 := by
    rcases mul_eq_zero.1 hfac with h | h
    · rcases mul_eq_zero.1 h with h' | h'
      · exact absurd h' h1
      · exact absurd h' h2
    · exact h
  have hzval : z = (a : A) / ((a : A) + (n : A)) := by
    rw [eq_div_iff hs]; linear_combination -h3
  rw [hzval]
  exact aeval_belyiP_lambda a n ha hn

lemma belyiP_natDegree_pos (a n : ℕ) (ha : 0 < a) (hn : 0 < n) :
    0 < (belyiP a n).natDegree := by
  refine natDegree_pos_of_aeval_ne
    (x := 0) (y := ((a : ℂ) / ((a : ℂ) + (n : ℂ)))) ?_
  rw [aeval_belyiP_zero a n ha, aeval_belyiP_lambda a n ha hn]
  exact zero_ne_one

/-! ### Step 1: reduction of a finite set of rational branch points to `{0,1}` -/

lemma aeval_ratCast (f : ℚ[X]) (r : ℚ) :
    aeval (algebraMap ℚ ℂ r) f = algebraMap ℚ ℂ (aeval r f) := by
  have h := Polynomial.aeval_algHom_apply (Algebra.ofId ℚ ℂ) r f
  simpa [Algebra.ofId_apply] using h

lemma aeval_transfer (f : ℚ[X]) (r : ℚ) (w : ℂ) (hw : w = algebraMap ℚ ℂ r)
    (hr : aeval r f = 0 ∨ aeval r f = 1) : aeval w f = 0 ∨ aeval w f = 1 := by
  subst hw
  rw [aeval_ratCast]
  rcases hr with h1 | h1 <;> simp [h1]

/-- The affine polynomial sending `u` to `0` and `v` to `1`. -/
def affP (u v : ℚ) : ℚ[X] := C (v - u)⁻¹ * (X - C u)

lemma derivative_affP (u v : ℚ) : derivative (affP u v) = C (v - u)⁻¹ := by
  simp [affP]

lemma affP_natDegree {u v : ℚ} (huv : u ≠ v) : (affP u v).natDegree = 1 := by
  have hc : ((v - u)⁻¹ : ℚ) ≠ 0 := inv_ne_zero (sub_ne_zero.2 (Ne.symm huv))
  rw [affP, Polynomial.natDegree_C_mul hc, Polynomial.natDegree_X_sub_C]

lemma aeval_affP_rat (u v x : ℚ) : aeval x (affP u v) = (v - u)⁻¹ * (x - u) := by
  simp [affP]

private lemma rat_reduction_aux (k : ℕ) : ∀ T : Finset ℚ, T.card ≤ k →
    ∃ h : ℚ[X], IsBelyi h ∧ ∀ t ∈ T, aeval t h = 0 ∨ aeval t h = 1 := by
  induction k using Nat.strong_induction_on with
  | _ k ih =>
  intro T hTk
  by_cases hcard : T.card ≤ 1
  · rcases T.eq_empty_or_nonempty with rfl | ⟨u, hu⟩
    · refine ⟨X, ⟨by simp, ?_⟩, by simp⟩
      intro z hz
      simp at hz
    · refine ⟨X - C u, ⟨by simp, ?_⟩, ?_⟩
      · intro z hz
        simp at hz
      · intro t ht
        left
        have htu : t = u := Finset.card_le_one.1 hcard t ht u hu
        simp [htu]
  · push_neg at hcard
    have hne : T.Nonempty := Finset.card_pos.1 (by omega)
    set u := T.min' hne with hu_def
    set v := T.max' hne with hv_def
    have huv : u < v := Finset.min'_lt_max'_of_card T hcard
    have hvu : (v - u) ≠ 0 := sub_ne_zero.2 (ne_of_gt huv)
    set A := affP u v with hA_def
    set phi : ℚ → ℚ := fun t => (v - u)⁻¹ * (t - u) with hphi_def
    have hAphi : ∀ t : ℚ, aeval t A = phi t := fun t => aeval_affP_rat u v t
    have hphi_inj : Function.Injective phi := by
      intro x y hxy
      simp only [hphi_def] at hxy
      field_simp at hxy
      linarith
    set U := T.image phi with hU_def
    have hcardU : U.card = T.card := Finset.card_image_of_injective _ hphi_inj
    have h0U : (0 : ℚ) ∈ U := by
      refine Finset.mem_image.2 ⟨u, T.min'_mem hne, ?_⟩
      simp [hphi_def]
    have h1U : (1 : ℚ) ∈ U := by
      refine Finset.mem_image.2 ⟨v, T.max'_mem hne, ?_⟩
      simp [hphi_def]
      field_simp
    have hU01 : ∀ x ∈ U, 0 ≤ x ∧ x ≤ 1 := by
      intro x hx
      obtain ⟨t, ht, rfl⟩ := Finset.mem_image.1 hx
      have hle1 : u ≤ t := T.min'_le t ht
      have hle2 : t ≤ v := T.le_max' t ht
      have hpos : (0 : ℚ) < (v - u)⁻¹ := inv_pos.2 (by linarith)
      constructor
      · have htu : (0 : ℚ) ≤ t - u := by linarith
        simp only [hphi_def]
        exact mul_nonneg hpos.le htu
      · simp only [hphi_def]
        rw [inv_mul_le_iff₀ (by linarith : (0:ℚ) < v - u)]
        linarith
    have hAbelyi : IsBelyi A := by
      refine ⟨by rw [affP_natDegree (ne_of_lt huv)]; norm_num, ?_⟩
      intro z hz
      exfalso
      rw [hA_def, derivative_affP] at hz
      simp only [aeval_C, map_eq_zero] at hz
      exact (inv_ne_zero hvu) hz
    by_cases hbig : 3 ≤ T.card
    · -- the main reduction step
      have hlam : ∃ lam ∈ U, lam ≠ 0 ∧ lam ≠ 1 := by
        by_contra hcon
        push_neg at hcon
        have hsub : U ⊆ ({0, 1} : Finset ℚ) := by
          intro x hx
          rcases eq_or_ne x 0 with rfl | hx0
          · simp
          · simp [hcon x hx hx0]
        have := Finset.card_le_card hsub
        have h2 : ({0, 1} : Finset ℚ).card = 2 := by decide
        omega
      obtain ⟨lam, hlamU, hlam0, hlam1⟩ := hlam
      obtain ⟨hlamge, hlamle⟩ := hU01 lam hlamU
      have hlampos : 0 < lam := lt_of_le_of_ne hlamge (Ne.symm hlam0)
      have hlamlt : lam < 1 := lt_of_le_of_ne hlamle hlam1
      set a := lam.num.toNat with ha_def
      set n := lam.den - a with hn_def
      have hnumpos : 0 < lam.num := Rat.num_pos.2 hlampos
      have ha : 0 < a := by omega
      have hnum : (lam.num : ℚ) = (a : ℚ) := by
        rw [ha_def]
        exact_mod_cast (Int.toNat_of_nonneg hnumpos.le).symm
      have haden : a < lam.den := by
        have h1 : (lam.num : ℚ) / (lam.den : ℚ) < 1 := by rw [Rat.num_div_den]; exact hlamlt
        have hd : (0 : ℚ) < (lam.den : ℚ) := by exact_mod_cast lam.pos
        rw [div_lt_one hd] at h1
        have h2 : lam.num < (lam.den : ℤ) := by exact_mod_cast h1
        omega
      have hn : 0 < n := by omega
      have han : a + n = lam.den := by omega
      have hlamval : lam = (a : ℚ) / ((a : ℚ) + (n : ℚ)) := by
        have hd : ((a : ℚ) + (n : ℚ)) = (lam.den : ℚ) := by
          rw [← Nat.cast_add, han]
        rw [hd, ← hnum, Rat.num_div_den]
      set P := belyiP a n with hP_def
      set g : ℚ → ℚ := fun x => aeval x P with hg_def
      have hg0 : g 0 = 0 := aeval_belyiP_zero a n ha
      have hg1 : g 1 = 0 := aeval_belyiP_one a n hn
      have hglam : g lam = 1 := by
        rw [hg_def]
        simp only
        rw [hlamval]
        exact aeval_belyiP_lambda a n ha hn
      set T' := U.image g ∪ ({0, 1} : Finset ℚ) with hT'_def
      have hsub3 : ({0, 1, lam} : Finset ℚ) ⊆ U := by
        intro x hx
        simp only [Finset.mem_insert, Finset.mem_singleton] at hx
        rcases hx with rfl | rfl | rfl
        · exact h0U
        · exact h1U
        · exact hlamU
      have hc3 : ({0, 1, lam} : Finset ℚ).card = 3 := by
        rw [Finset.card_insert_of_notMem (by simp [Ne.symm hlam0]),
          Finset.card_insert_of_notMem (by simp [Ne.symm hlam1])]
        simp
      have hsubT' : T' ⊆ (U \ ({0, 1, lam} : Finset ℚ)).image g ∪ ({0, 1} : Finset ℚ) := by
        intro y hy
        rcases Finset.mem_union.1 hy with hy | hy
        · obtain ⟨x, hx, rfl⟩ := Finset.mem_image.1 hy
          by_cases hx3 : x ∈ ({0, 1, lam} : Finset ℚ)
          · refine Finset.mem_union_right _ ?_
            simp only [Finset.mem_insert, Finset.mem_singleton] at hx3 ⊢
            rcases hx3 with rfl | rfl | rfl
            · exact Or.inl hg0
            · exact Or.inl hg1
            · exact Or.inr hglam
          · exact Finset.mem_union_left _
              (Finset.mem_image.2 ⟨x, Finset.mem_sdiff.2 ⟨hx, hx3⟩, rfl⟩)
        · exact Finset.mem_union_right _ hy
      have hcardT' : T'.card < k := by
        have hb1 := Finset.card_le_card hsubT'
        have hb2 := Finset.card_union_le ((U \ ({0, 1, lam} : Finset ℚ)).image g)
          ({0, 1} : Finset ℚ)
        have hb3 := Finset.card_image_le (s := U \ ({0, 1, lam} : Finset ℚ)) (f := g)
        have hb4 : (U \ ({0, 1, lam} : Finset ℚ)).card = U.card - 3 := by
          rw [Finset.card_sdiff_of_subset hsub3, hc3]
        have hb5 : ({0, 1} : Finset ℚ).card = 2 := by decide
        omega
      obtain ⟨h', hb', hT'⟩ := ih T'.card hcardT' T' le_rfl
      have h0T' : (0 : ℚ) ∈ T' := Finset.mem_union_right _ (by simp)
      have h1T' : (1 : ℚ) ∈ T' := Finset.mem_union_right _ (by simp)
      refine ⟨h'.comp (P.comp A), ⟨?_, ?_⟩, ?_⟩
      · rw [Polynomial.natDegree_comp, Polynomial.natDegree_comp]
        have hd1 := hb'.1
        have hd2 := belyiP_natDegree_pos a n ha hn
        have hd3 : A.natDegree = 1 := affP_natDegree (ne_of_lt huv)
        rw [hd3]
        exact Nat.mul_pos hd1 (Nat.mul_pos hd2 (by norm_num))
      · intro z hz
        rw [aeval_derivative_comp] at hz
        rcases mul_eq_zero.1 hz with hz1 | hz2
        · rw [aeval_derivative_comp] at hz1
          rcases mul_eq_zero.1 hz1 with hz3 | hz4
          · exfalso
            rw [hA_def, derivative_affP] at hz3
            simp only [aeval_C, map_eq_zero] at hz3
            exact (inv_ne_zero hvu) hz3
          · have hcrit := belyiP_crit a n ha hn (aeval z A) hz4
            rw [Polynomial.aeval_comp, Polynomial.aeval_comp]
            rcases hcrit with hh | hh
            · rw [hh]
              exact aeval_transfer h' 0 0 (by simp) (hT' 0 h0T')
            · rw [hh]
              exact aeval_transfer h' 1 1 (by simp) (hT' 1 h1T')
        · rw [Polynomial.aeval_comp]
          exact hb'.2 (aeval z (P.comp A)) hz2
      · intro t ht
        rw [Polynomial.aeval_comp, Polynomial.aeval_comp, hAphi]
        refine hT' _ (Finset.mem_union_left _ (Finset.mem_image.2 ⟨phi t, ?_, rfl⟩))
        exact Finset.mem_image.2 ⟨t, ht, rfl⟩
    · -- exactly two points: the affine map already works
      have hcard2 : T.card = 2 := by omega
      have hUeq : ({0, 1} : Finset ℚ) = U := by
        refine Finset.eq_of_subset_of_card_le ?_ ?_
        · intro x hx
          simp only [Finset.mem_insert, Finset.mem_singleton] at hx
          rcases hx with rfl | rfl
          · exact h0U
          · exact h1U
        · have h2 : ({0, 1} : Finset ℚ).card = 2 := by decide
          omega
      refine ⟨A, hAbelyi, ?_⟩
      intro t ht
      have hmem : phi t ∈ U := Finset.mem_image.2 ⟨t, ht, rfl⟩
      rw [← hUeq] at hmem
      simp only [Finset.mem_insert, Finset.mem_singleton] at hmem
      rw [hAphi]
      exact hmem

/-- **Belyi's reduction over `ℚ`**: for every finite set `T` of rational numbers there is a
Belyi polynomial mapping `T` into `{0, 1}`. -/
theorem rat_reduction (T : Finset ℚ) :
    ∃ h : ℚ[X], IsBelyi h ∧ ∀ t ∈ T, aeval t h = 0 ∨ aeval t h = 1 :=
  rat_reduction_aux T.card T le_rfl

/-! ### Step 2: making the critical values rational -/

/-- If `p` has degree `D` then every critical value of `p` has degree `< D` over `ℚ`. -/
lemma algDeg_critF_lt {p : ℚ[X]} (hppos : 0 < p.natDegree) {w : ℂ} (hw : w ∈ critF p) :
    algDeg w < p.natDegree := by
  have hd : derivative p ≠ 0 := derivative_ne_zero_of_natDegree_pos hppos
  rw [mem_critF hd] at hw
  obtain ⟨z, hz, rfl⟩ := hw
  have hzalg : IsAlgebraic ℚ z := ⟨derivative p, hd, hz⟩
  have hz0 : IsIntegral ℚ z := hzalg.isIntegral
  have h1 : algDeg z ≤ (derivative p).natDegree := algDeg_le_of_root hd hz
  have h2 : (derivative p).natDegree < p.natDegree :=
    Polynomial.natDegree_derivative_lt (by omega)
  have h3 := algDeg_aeval_le p hz0
  omega

lemma rationalize_aux (D : ℕ) : ∀ N : ℕ, ∀ f : ℚ[X], 0 < f.natDegree →
    (∀ w ∈ critF f, algDeg w ≤ D) →
    ((critF f).filter (fun w => algDeg w = D)).card ≤ N →
    ∃ g : ℚ[X], 0 < g.natDegree ∧
      ∀ w ∈ critF (g.comp f), ∃ q : ℚ, algebraMap ℚ ℂ q = w := by
  induction D using Nat.strong_induction_on with
  | _ D ihD =>
  by_cases hD1 : D ≤ 1
  · intro _ f hf hDf _
    refine ⟨X, by simp, ?_⟩
    intro w hw
    rw [Polynomial.X_comp] at hw
    exact rat_of_algDeg_le_one (isIntegral_of_mem_critF hf hw) (le_trans (hDf w hw) hD1)
  · intro N
    induction N with
    | zero =>
      intro f hf hDf hN
      by_cases hex : ∃ b ∈ critF f, algDeg b = D
      · obtain ⟨b, hb, hbD⟩ := hex
        exfalso
        have : b ∈ (critF f).filter (fun w => algDeg w = D) := Finset.mem_filter.2 ⟨hb, hbD⟩
        have := Finset.card_pos.2 ⟨b, this⟩
        omega
      · refine ihD (D - 1) (by omega) ((critF f).card) f hf ?_ (Finset.card_filter_le _ _)
        intro w hw
        have h1 := hDf w hw
        have h2 : algDeg w ≠ D := fun h => hex ⟨w, hw, h⟩
        omega
    | succ N ihN =>
      intro f hf hDf hN
      by_cases hex : ∃ b ∈ critF f, algDeg b = D
      · obtain ⟨b, hb, hbD⟩ := hex
        have hbint : IsIntegral ℚ b := isIntegral_of_mem_critF hf hb
        have hpdeg : (minpoly ℚ b).natDegree = D := hbD
        have hppos : 0 < (minpoly ℚ b).natDegree := by omega
        have hpf : 0 < ((minpoly ℚ b).comp f).natDegree := by
          rw [Polynomial.natDegree_comp]; exact Nat.mul_pos hppos hf
        have hbp : aeval b (minpoly ℚ b) = 0 := minpoly.aeval ℚ b
        have hzero : algDeg (0 : ℂ) = 1 := by simp [algDeg, minpoly.zero]
        have hcritp : ∀ w ∈ critF (minpoly ℚ b), algDeg w < D := by
          intro w hw
          have := algDeg_critF_lt hppos hw
          omega
        have hdegs : ∀ w ∈ critF ((minpoly ℚ b).comp f), algDeg w ≤ D := by
          intro w hw
          rcases Finset.mem_union.1 (critF_comp_subset hppos hf hw) with h | h
          · obtain ⟨t, ht, rfl⟩ := Finset.mem_image.1 h
            exact le_trans (algDeg_aeval_le _ (isIntegral_of_mem_critF hf ht)) (hDf t ht)
          · exact le_of_lt (hcritp w h)
        have hbfilter : b ∈ (critF f).filter (fun w => algDeg w = D) :=
          Finset.mem_filter.2 ⟨hb, hbD⟩
        have hcnt : ((critF ((minpoly ℚ b).comp f)).filter (fun w => algDeg w = D)).card ≤ N := by
          have hsub : (critF ((minpoly ℚ b).comp f)).filter (fun w => algDeg w = D) ⊆
              (((critF f).filter (fun w => algDeg w = D)).erase b).image
                (fun t => aeval t (minpoly ℚ b)) := by
            intro w hw
            obtain ⟨hw1, hw2⟩ := Finset.mem_filter.1 hw
            rcases Finset.mem_union.1 (critF_comp_subset hppos hf hw1) with h | h
            · obtain ⟨t, ht, rfl⟩ := Finset.mem_image.1 h
              have htD : algDeg t = D := by
                have h1 := algDeg_aeval_le (minpoly ℚ b) (isIntegral_of_mem_critF hf ht)
                have h2 := hDf t ht
                omega
              have htb : t ≠ b := by
                intro hcon
                rw [hcon, hbp, hzero] at hw2
                omega
              exact Finset.mem_image.2
                ⟨t, Finset.mem_erase.2 ⟨htb, Finset.mem_filter.2 ⟨ht, htD⟩⟩, rfl⟩
            · exact absurd hw2 (Nat.ne_of_lt (hcritp w h))
          have h1 := Finset.card_le_card hsub
          have h2 := Finset.card_image_le
            (s := ((critF f).filter (fun w => algDeg w = D)).erase b)
            (f := fun t => aeval t (minpoly ℚ b))
          have h3 : (((critF f).filter (fun w => algDeg w = D)).erase b).card
              = ((critF f).filter (fun w => algDeg w = D)).card - 1 :=
            Finset.card_erase_of_mem hbfilter
          have h4 : 1 ≤ ((critF f).filter (fun w => algDeg w = D)).card :=
            Finset.card_pos.2 ⟨b, hbfilter⟩
          omega
        obtain ⟨g', hg'pos, hg'⟩ := ihN ((minpoly ℚ b).comp f) hpf hdegs hcnt
        refine ⟨g'.comp (minpoly ℚ b), ?_, ?_⟩
        · rw [Polynomial.natDegree_comp]; exact Nat.mul_pos hg'pos hppos
        · intro w hw
          rw [Polynomial.comp_assoc] at hw
          exact hg' w hw
      · refine ihD (D - 1) (by omega) ((critF f).card) f hf ?_ (Finset.card_filter_le _ _)
        intro w hw
        have h1 := hDf w hw
        have h2 : algDeg w ≠ D := fun h => hex ⟨w, hw, h⟩
        omega

/-- For any nonconstant `f ∈ ℚ[X]` there is a nonconstant `g ∈ ℚ[X]` such that all critical
values of `g ∘ f` are rational. -/
theorem rationalize (f : ℚ[X]) (hf : 0 < f.natDegree) :
    ∃ g : ℚ[X], 0 < g.natDegree ∧
      ∀ w ∈ critF (g.comp f), ∃ q : ℚ, algebraMap ℚ ℂ q = w :=
  rationalize_aux ((critF f).sup algDeg) ((critF f).card) f hf
    (fun _ hw => Finset.le_sup hw) (Finset.card_filter_le _ _)

/-! ### The main theorem -/

/-- **Belyi's theorem** (the case of the projective line with marked points).

A finite set `S ⊆ ℂ` consists of algebraic numbers -- i.e. the marked curve `(ℙ¹, S)` is
defined over `ℚ̄` -- if and only if there is a Belyi map `f : ℙ¹ → ℙ¹`, given by a polynomial
with rational coefficients, which is ramified only above `{0, 1, ∞}` and sends `S` into
`{0, 1, ∞}`.  (Polynomials send `∞` to `∞`, so ramification above `∞` is allowed
automatically and the finite critical values are required to lie in `{0, 1}`.) -/
theorem belyi_theorem (S : Finset ℂ) :
    (∀ s ∈ S, IsAlgebraic ℚ s) ↔
      ∃ f : ℚ[X], IsBelyi f ∧ ∀ s ∈ S, aeval s f = 0 ∨ aeval s f = 1 := by
  classical
  constructor
  · intro hS
    -- Step 0: a polynomial over `ℚ` vanishing on `S`.
    set f1 : ℚ[X] := X * ∏ s ∈ S, minpoly ℚ s with hf1_def
    have hmonic : (∏ s ∈ S, minpoly ℚ s).Monic :=
      monic_prod_of_monic _ _ (fun s hs => minpoly.monic (hS s hs).isIntegral)
    have hprod_ne : (∏ s ∈ S, minpoly ℚ s) ≠ 0 := hmonic.ne_zero
    have hf1deg : 0 < f1.natDegree := by
      rw [hf1_def, Polynomial.natDegree_mul Polynomial.X_ne_zero hprod_ne,
        Polynomial.natDegree_X]
      omega
    have hf1S : ∀ s ∈ S, aeval s f1 = 0 := by
      intro s hs
      rw [hf1_def]
      simp only [map_mul, map_prod, aeval_X]
      rw [Finset.prod_eq_zero hs (minpoly.aeval ℚ s)]
      ring
    -- Step 1: make all critical values rational.
    obtain ⟨g, hgdeg, hgrat⟩ := rationalize f1 hf1deg
    set F := g.comp f1 with hF_def
    have hFdeg : 0 < F.natDegree := by
      rw [hF_def, Polynomial.natDegree_comp]
      exact Nat.mul_pos hgdeg hf1deg
    set psi : ℂ → ℚ := fun w => if h : ∃ q : ℚ, algebraMap ℚ ℂ q = w then h.choose else 0
      with hpsi_def
    have hpsi : ∀ w ∈ critF F, algebraMap ℚ ℂ (psi w) = w := by
      intro w hw
      have h := hgrat w hw
      simp only [hpsi_def]
      rw [dif_pos h]
      exact h.choose_spec
    -- the common value of `F` on `S`
    set r : ℚ := aeval (0 : ℚ) g with hr_def
    have hFS : ∀ s ∈ S, aeval s F = algebraMap ℚ ℂ r := by
      intro s hs
      rw [hF_def, Polynomial.aeval_comp, hf1S s hs, hr_def]
      have : ((0 : ℂ)) = algebraMap ℚ ℂ (0 : ℚ) := by simp
      rw [this, aeval_ratCast]
    -- Step 2: send the (rational) critical values and the value `r` to `{0,1}`.
    set T : Finset ℚ := (critF F).image psi ∪ {r} with hT_def
    obtain ⟨h, hbelyi, hT⟩ := rat_reduction T
    have hrT : r ∈ T := Finset.mem_union_right _ (by simp)
    refine ⟨h.comp F, ⟨?_, ?_⟩, ?_⟩
    · rw [Polynomial.natDegree_comp]
      exact Nat.mul_pos hbelyi.1 hFdeg
    · intro z hz
      rw [aeval_derivative_comp] at hz
      rw [Polynomial.aeval_comp]
      rcases mul_eq_zero.1 hz with h1 | h2
      · have hmem : aeval z F ∈ critF F :=
          (mem_critF (derivative_ne_zero_of_natDegree_pos hFdeg)).2 ⟨z, h1, rfl⟩
        refine aeval_transfer h (psi (aeval z F)) _ (hpsi _ hmem).symm ?_
        exact hT _ (Finset.mem_union_left _ (Finset.mem_image.2 ⟨_, hmem, rfl⟩))
      · exact hbelyi.2 (aeval z F) h2
    · intro s hs
      rw [Polynomial.aeval_comp, hFS s hs]
      exact aeval_transfer h r _ rfl (hT r hrT)
  · rintro ⟨f, ⟨hfdeg, _⟩, hfS⟩ s hs
    have hf0 : f ≠ 0 := fun h => by simp [h] at hfdeg
    rcases hfS s hs with h | h
    · exact ⟨f, hf0, h⟩
    · refine ⟨f - 1, ?_, ?_⟩
      · intro hcon
        have : f = 1 := by linear_combination (norm := ring_nf) hcon
        rw [this] at hfdeg
        simp at hfdeg
      · simp only [map_sub, map_one, h, sub_self]

/-- A Belyi polynomial is unramified above every point other than `0`, `1` (and `∞`):
if `f z = w` with `w ∉ {0, 1}` then `f` is unramified at `z`, i.e. `f' z ≠ 0`. -/
theorem isBelyi_unramified {f : ℚ[X]} (hf : IsBelyi f) {z w : ℂ} (hw0 : w ≠ 0) (hw1 : w ≠ 1)
    (hz : aeval z f = w) : aeval z (derivative f) ≠ 0 := by
  intro hcon
  rcases hf.2 z hcon with h | h <;> rw [hz] at h
  · exact hw0 h
  · exact hw1 h

/-- **Belyi's theorem for a single point**: a complex number is algebraic over `ℚ` if and only if
it is sent into `{0, 1}` by some Belyi map. -/
theorem belyi_theorem_point (s : ℂ) :
    IsAlgebraic ℚ s ↔ ∃ f : ℚ[X], IsBelyi f ∧ (aeval s f = 0 ∨ aeval s f = 1) := by
  have h := belyi_theorem {s}
  simp only [Finset.mem_singleton, forall_eq] at h
  exact h

end

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

