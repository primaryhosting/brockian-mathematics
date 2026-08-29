import Mathlib
/-!
# Belyi Theorem
Category: Frontier Math
Target: Math2.belyi_theorem
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open scoped Classical

set_option maxHeartbeats 1000000

namespace Math2

open Polynomial IntermediateField

noncomputable section

/-! ## Basic notions -/

/-- The set of critical values in `ℂ` of a polynomial with rational coefficients.
Viewing `f ∈ ℚ[X]` as a morphism `ℙ¹ → ℙ¹`, these are the finite branch points of `f`. -/
def critVal (f : ℚ[X]) : Set ℂ :=
  {v | ∃ w : ℂ, aeval w (derivative f) = 0 ∧ aeval w f = v}

/-- `f` is a *Belyi map*: a nonconstant morphism `ℙ¹ → ℙ¹`, defined over `ℚ`, whose branch
locus is contained in `{0, 1, ∞}`.  (A polynomial map is totally ramified over `∞`, so the
only remaining condition is that all finite critical values lie in `{0,1}`.) -/
def IsBelyi (f : ℚ[X]) : Prop := 0 < f.natDegree ∧ critVal f ⊆ ({0, 1} : Set ℂ)

/-- The degree over `ℚ` of a complex number. -/
def degQ (z : ℂ) : ℕ := (minpoly ℚ z).natDegree

lemma aeval_ratCast (q : ℚ) (f : ℚ[X]) : aeval ((q : ℂ)) f = ((f.eval q : ℚ) : ℂ) := by
  have := Polynomial.aeval_algebraMap_apply (R := ℚ) (A := ℚ) ℂ q f
  simpa using this

/-- Critical values of a composite: `CV (g ∘ f) ⊆ g (CV f) ∪ CV g`. -/
lemma critVal_comp (g f : ℚ[X]) :
    critVal (g.comp f) ⊆ (fun v => aeval v g) '' (critVal f) ∪ critVal g := by
  rintro v ⟨w, hw, rfl⟩
  rw [derivative_comp] at hw
  simp only [map_mul, aeval_comp, mul_eq_zero] at hw
  rcases hw with h | h
  · exact Or.inl ⟨aeval w f, ⟨w, h, rfl⟩, by rw [aeval_comp]⟩
  · exact Or.inr ⟨aeval w f, h, by rw [aeval_comp]⟩

lemma critVal_eq_empty_of_derivative_const (f : ℚ[X]) (u : ℚ) (hu : u ≠ 0)
    (h : derivative f = C u) : critVal f = ∅ := by
  ext v
  simp only [critVal, Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false]
  rintro ⟨w, hw, rfl⟩
  rw [h] at hw
  simp only [aeval_C, eq_ratCast, Rat.cast_eq_zero] at hw
  exact hu hw

lemma critVal_X : critVal (X : ℚ[X]) = ∅ :=
  critVal_eq_empty_of_derivative_const X 1 one_ne_zero (by simp)

/-! ## The Belyi polynomials

For `a b : ℕ` the polynomial `belyiPoly a b = c ⬝ x^(a+1) (1-x)^(b+1)` has all its critical
values in `{0, 1}`, and it sends the rational point `belyiPt a b = (a+1)/(a+b+2)` to `1`. -/

/-- The distinguished critical point `(a+1)/(a+b+2) ∈ (0,1)`. -/
def belyiPt (a b : ℕ) : ℚ := ((a : ℚ) + 1) / ((a : ℚ) + b + 2)

/-- Normalising constant. -/
def belyiC (a b : ℕ) : ℚ := ((belyiPt a b) ^ (a + 1) * (1 - belyiPt a b) ^ (b + 1))⁻¹

/-- The Belyi polynomial `c * x^(a+1) * (1-x)^(b+1)`. -/
def belyiPoly (a b : ℕ) : ℚ[X] := C (belyiC a b) * (X ^ (a + 1) * (1 - X) ^ (b + 1))

lemma belyiPt_den_pos (a b : ℕ) : (0 : ℚ) < (a : ℚ) + b + 2 := by positivity

lemma belyiPt_pos (a b : ℕ) : 0 < belyiPt a b :=
  div_pos (by positivity) (belyiPt_den_pos a b)

lemma belyiPt_lt_one (a b : ℕ) : belyiPt a b < 1 := by
  unfold belyiPt
  rw [div_lt_one (belyiPt_den_pos a b)]
  have : (0 : ℚ) ≤ b := by positivity
  linarith

lemma one_sub_belyiPt_pos (a b : ℕ) : 0 < 1 - belyiPt a b := by
  have := belyiPt_lt_one a b; linarith

lemma belyiC_ne_zero (a b : ℕ) : belyiC a b ≠ 0 := by
  unfold belyiC
  have h1 := belyiPt_pos a b
  have h2 := one_sub_belyiPt_pos a b
  positivity

lemma belyiPoly_eval (a b : ℕ) (x : ℚ) :
    (belyiPoly a b).eval x = belyiC a b * (x ^ (a + 1) * (1 - x) ^ (b + 1)) := by
  simp [belyiPoly]

lemma belyiPoly_eval_zero (a b : ℕ) : (belyiPoly a b).eval 0 = 0 := by
  rw [belyiPoly_eval]; simp

lemma belyiPoly_eval_one (a b : ℕ) : (belyiPoly a b).eval 1 = 0 := by
  rw [belyiPoly_eval]; simp

lemma belyiPoly_eval_pt (a b : ℕ) : (belyiPoly a b).eval (belyiPt a b) = 1 := by
  rw [belyiPoly_eval]
  unfold belyiC
  have h1 := belyiPt_pos a b
  have h2 := one_sub_belyiPt_pos a b
  field_simp

lemma derivative_belyiPoly (a b : ℕ) :
    derivative (belyiPoly a b) =
      C (belyiC a b) *
        (X ^ a * ((1 - X) ^ b * (C ((a : ℚ) + 1) - C ((a : ℚ) + b + 2) * X))) := by
  unfold belyiPoly
  simp only [derivative_mul, derivative_C, derivative_pow, derivative_X,
    derivative_one, zero_mul, zero_add, mul_one, zero_sub, Nat.add_sub_cancel,
    map_add, map_sub, map_natCast, C_1, map_ofNat]
  push_cast
  ring

lemma belyiPoly_natDegree_pos (a b : ℕ) : 0 < (belyiPoly a b).natDegree := by
  rcases Nat.eq_zero_or_pos (belyiPoly a b).natDegree with hh | hh
  · exfalso
    have hc := Polynomial.eq_C_of_natDegree_eq_zero hh
    have h0 := belyiPoly_eval_zero a b
    have h1 := belyiPoly_eval_pt a b
    rw [hc] at h0 h1
    simp only [eval_C] at h0 h1
    rw [h0] at h1
    exact absurd h1 (by norm_num)
  · exact hh

lemma critVal_belyiPoly (a b : ℕ) : critVal (belyiPoly a b) ⊆ ({0, 1} : Set ℂ) := by
  rintro v ⟨w, hw, rfl⟩
  rw [derivative_belyiPoly] at hw
  simp only [map_mul, map_sub, map_pow, map_one, aeval_C, aeval_X, mul_eq_zero,
    sub_eq_zero, eq_ratCast] at hw
  have hc : ((belyiC a b : ℚ) : ℂ) ≠ 0 := (Rat.cast_ne_zero (α := ℂ)).mpr (belyiC_ne_zero a b)
  rcases hw with hc' | hw
  · exact absurd hc' hc
  rcases hw with hw | hw
  · have hw0 : w = 0 := (pow_eq_zero_iff'.mp hw).1
    subst hw0
    left
    simp [belyiPoly]
  rcases hw with hw | hw
  · have hw1 : w = 1 := by
      have h := (pow_eq_zero_iff'.mp hw).1
      linear_combination -h
    subst hw1
    left
    simp [belyiPoly]
  · have hden : ((a : ℂ) + b + 2) ≠ 0 := by
      intro hcon
      have h2 : ((a : ℂ) + b + 2).re = 0 := by rw [hcon]; simp
      simp only [Complex.add_re, Complex.natCast_re, Complex.re_ofNat] at h2
      have : (0 : ℝ) < (a : ℝ) + b + 2 := by positivity
      linarith
    have hwv : w = ((belyiPt a b : ℚ) : ℂ) := by
      unfold belyiPt
      push_cast at hw ⊢
      field_simp
      linear_combination -hw
    subst hwv
    right
    rw [aeval_ratCast, belyiPoly_eval_pt]
    norm_num

/-- Every rational number in `(0,1)` is of the form `belyiPt a b`. -/
lemma exists_belyiPt (μ : ℚ) (h0 : 0 < μ) (h1 : μ < 1) : ∃ a b : ℕ, belyiPt a b = μ := by
  have hd : (0 : ℚ) < (μ.den : ℚ) := by exact_mod_cast μ.pos
  have hnum : 0 < μ.num := Rat.num_pos.mpr h0
  have hkey : (μ.num : ℚ) = μ * (μ.den : ℚ) := (div_eq_iff (ne_of_gt hd)).mp (Rat.num_div_den μ)
  have hlt : (μ.num : ℚ) < (μ.den : ℚ) := by rw [hkey]; nlinarith
  have hltZ : μ.num < (μ.den : ℤ) := by exact_mod_cast hlt
  set n : ℕ := μ.num.toNat with hn
  have hnnum : (n : ℤ) = μ.num := Int.toNat_of_nonneg hnum.le
  have hn1 : 1 ≤ n := by omega
  have hnd : n + 1 ≤ μ.den := by omega
  obtain ⟨a, ha⟩ : ∃ a : ℕ, n = a + 1 := ⟨n - 1, by omega⟩
  obtain ⟨b, hb⟩ : ∃ b : ℕ, μ.den = a + b + 2 := ⟨μ.den - n - 1, by omega⟩
  refine ⟨a, b, ?_⟩
  unfold belyiPt
  have e1 : ((a : ℚ) + 1) = (μ.num : ℚ) := by rw [← hnnum, ha]; push_cast; ring
  have e2 : ((a : ℚ) + b + 2) = (μ.den : ℚ) := by rw [hb]; push_cast; ring
  rw [e1, e2, Rat.num_div_den]

/-! ## Step 1 : mapping a finite set of rationals into `{0,1}` -/

lemma exists_two_cover (T : Finset ℚ) (h : T.card ≤ 2) :
    ∃ a b : ℚ, a ≠ b ∧ ∀ t ∈ T, t = a ∨ t = b := by
  interval_cases hc : T.card
  · exact ⟨0, 1, by norm_num, fun t ht => absurd (Finset.card_eq_zero.mp hc ▸ ht) (by simp)⟩
  · obtain ⟨x, hx⟩ := Finset.card_eq_one.mp hc
    exact ⟨x, x + 1, by norm_num, fun t ht => Or.inl (by rw [hx] at ht; simpa using ht)⟩
  · obtain ⟨x, y, hxy, hT⟩ := Finset.card_eq_two.mp hc
    exact ⟨x, y, hxy, fun t ht => by rw [hT] at ht; simpa using ht⟩

/-- The affine map sending `a ↦ 0`, `b ↦ 1`. -/
def affQ (a b : ℚ) : ℚ[X] := C (b - a)⁻¹ * (X - C a)

lemma affQ_eval (a b x : ℚ) : (affQ a b).eval x = (x - a) / (b - a) := by
  simp only [affQ, eval_mul, eval_C, eval_sub, eval_X]; ring

lemma affQ_natDegree (a b : ℚ) (h : a ≠ b) : (affQ a b).natDegree = 1 := by
  have hba : (b - a)⁻¹ ≠ 0 := by
    simp only [ne_eq, inv_eq_zero, sub_eq_zero]
    exact fun hh => h hh.symm
  unfold affQ
  rw [Polynomial.natDegree_C_mul hba]
  compute_degree!

lemma derivative_affQ (a b : ℚ) : derivative (affQ a b) = C (b - a)⁻¹ := by
  unfold affQ
  simp [derivative_mul]

lemma critVal_affQ (a b : ℚ) (h : a ≠ b) : critVal (affQ a b) = ∅ := by
  refine critVal_eq_empty_of_derivative_const _ ((b - a)⁻¹) ?_ (derivative_affQ a b)
  simp only [ne_eq, inv_eq_zero, sub_eq_zero]
  exact fun hh => h hh.symm

lemma belyi_rat_base (T : Finset ℚ) (h : T.card ≤ 2) :
    ∃ f : ℚ[X], 0 < f.natDegree ∧ (∀ t ∈ T, f.eval t = 0 ∨ f.eval t = 1) ∧
      critVal f ⊆ ({0, 1} : Set ℂ) := by
  obtain ⟨a, b, hab, hcov⟩ := exists_two_cover T h
  refine ⟨affQ a b, by rw [affQ_natDegree a b hab]; norm_num, ?_, ?_⟩
  · intro t ht
    rcases hcov t ht with rfl | rfl
    · left; rw [affQ_eval]; simp
    · right; rw [affQ_eval]; exact div_self (sub_ne_zero.mpr (Ne.symm hab))
  · rw [critVal_affQ a b hab]; exact Set.empty_subset _

/-- **Belyi reduction over `ℚ`**: any finite set of rational numbers can be mapped into
`{0,1}` by a polynomial over `ℚ` all of whose critical values also lie in `{0,1}`. -/
lemma exists_belyi_rat (n : ℕ) : ∀ T : Finset ℚ, T.card ≤ n →
    ∃ f : ℚ[X], 0 < f.natDegree ∧ (∀ t ∈ T, f.eval t = 0 ∨ f.eval t = 1) ∧
      critVal f ⊆ ({0, 1} : Set ℂ) := by
  induction n with
  | zero => intro T _; exact belyi_rat_base T (by omega)
  | succ n ih =>
    intro T hT
    by_cases h3 : T.card ≤ 2
    · exact belyi_rat_base T h3
    push_neg at h3
    have hne : T.Nonempty := Finset.card_pos.mp (by omega)
    set a := T.min' hne with hadef
    set b := T.max' hne with hbdef
    have haT : a ∈ T := T.min'_mem hne
    have hbT : b ∈ T := T.max'_mem hne
    have hab : a < b := T.min'_lt_max'_of_card (by omega)
    have hne' : a ≠ b := ne_of_lt hab
    have hsub : T ⊆ (T \ {a, b}) ∪ {a, b} := by
      intro t ht
      by_cases h : t ∈ ({a, b} : Finset ℚ)
      · exact Finset.mem_union_right _ h
      · exact Finset.mem_union_left _ (Finset.mem_sdiff.mpr ⟨ht, h⟩)
    have hcard2 : ({a, b} : Finset ℚ).card ≤ 2 := (Finset.card_insert_le _ _).trans (by simp)
    have hthird : (T \ ({a, b} : Finset ℚ)).Nonempty := by
      rw [← Finset.card_pos]
      by_contra hcon
      push_neg at hcon
      have h1 := Finset.card_le_card hsub
      have h2 := Finset.card_union_le (T \ ({a, b} : Finset ℚ)) ({a, b} : Finset ℚ)
      omega
    obtain ⟨c, hc⟩ := hthird
    have hcT : c ∈ T := (Finset.mem_sdiff.mp hc).1
    have hcab : c ≠ a ∧ c ≠ b := by
      have h := (Finset.mem_sdiff.mp hc).2
      simpa using h
    have hac : a < c := lt_of_le_of_ne (T.min'_le c hcT) (Ne.symm hcab.1)
    have hcb : c < b := lt_of_le_of_ne (T.le_max' c hcT) hcab.2
    set μ := (c - a) / (b - a) with hmu
    have hba : (0 : ℚ) < b - a := by linarith
    have hmu0 : 0 < μ := div_pos (by linarith) hba
    have hmu1 : μ < 1 := by rw [hmu, div_lt_one hba]; linarith
    obtain ⟨p, q, hpq⟩ := exists_belyiPt μ hmu0 hmu1
    set A := affQ a b with hA
    set B := belyiPoly p q with hB
    set F := B.comp A with hF
    have hFa : F.eval a = 0 := by
      rw [hF, eval_comp, affQ_eval]
      simp [hB, belyiPoly_eval_zero]
    have hFb : F.eval b = 0 := by
      rw [hF, eval_comp, affQ_eval, div_self (by linarith : b - a ≠ 0)]
      simp [hB, belyiPoly_eval_one]
    have hFc : F.eval c = 1 := by
      rw [hF, eval_comp, affQ_eval, ← hmu, ← hpq]
      exact belyiPoly_eval_pt p q
    set T' := T.image (fun t => F.eval t) with hT'
    have h0T' : (0 : ℚ) ∈ T' := by rw [hT']; exact Finset.mem_image.mpr ⟨a, haT, hFa⟩
    have h1T' : (1 : ℚ) ∈ T' := by rw [hT']; exact Finset.mem_image.mpr ⟨c, hcT, hFc⟩
    have himg : T' = (T.erase b).image (fun t => F.eval t) := by
      apply Finset.Subset.antisymm
      · intro v hv
        rw [hT'] at hv
        obtain ⟨t, htT, htv⟩ := Finset.mem_image.mp hv
        by_cases hb' : t = b
        · exact Finset.mem_image.mpr ⟨a, Finset.mem_erase.mpr ⟨hne', haT⟩,
            by rw [hFa, ← htv, hb', hFb]⟩
        · exact Finset.mem_image.mpr ⟨t, Finset.mem_erase.mpr ⟨hb', htT⟩, htv⟩
      · intro v hv
        obtain ⟨t, htT, htv⟩ := Finset.mem_image.mp hv
        rw [hT']
        exact Finset.mem_image.mpr ⟨t, (Finset.mem_erase.mp htT).2, htv⟩
    have hcardT' : T'.card ≤ n := by
      rw [himg]
      have h1 := Finset.card_image_le (s := T.erase b) (f := fun t => F.eval t)
      have h2 : (T.erase b).card = T.card - 1 := Finset.card_erase_of_mem hbT
      omega
    obtain ⟨g, hgdeg, hgeval, hgcrit⟩ := ih T' hcardT'
    have hFdeg : 0 < F.natDegree := by
      rw [hF, natDegree_comp, hA, affQ_natDegree a b hne']
      simpa [hB] using belyiPoly_natDegree_pos p q
    have hcritF : critVal F ⊆ ({0, 1} : Set ℂ) := by
      intro v hv
      rcases critVal_comp B A hv with ⟨u, hu, _⟩ | hv'
      · rw [hA, critVal_affQ a b hne'] at hu; exact absurd hu (Set.notMem_empty u)
      · exact critVal_belyiPoly p q hv'
    refine ⟨g.comp F, ?_, ?_, ?_⟩
    · rw [natDegree_comp]; exact Nat.mul_pos hgdeg hFdeg
    · intro t ht
      rw [eval_comp]
      exact hgeval _ (by rw [hT']; exact Finset.mem_image.mpr ⟨t, ht, rfl⟩)
    · intro v hv
      rcases critVal_comp g F hv with ⟨u, hu, huv⟩ | hv'
      · have hu' := hcritF hu
        simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hu'
        have hg0 : aeval (0 : ℂ) g = ((g.eval 0 : ℚ) : ℂ) := by
          simpa using aeval_ratCast (0 : ℚ) g
        have hg1 : aeval (1 : ℂ) g = ((g.eval 1 : ℚ) : ℂ) := by
          simpa using aeval_ratCast (1 : ℚ) g
        rcases hu' with rfl | rfl
        · rw [← huv]
          simp only [hg0]
          rcases hgeval 0 h0T' with h | h <;> rw [h] <;> simp
        · rw [← huv]
          simp only [hg1]
          rcases hgeval 1 h1T' with h | h <;> rw [h] <;> simp
      · exact hgcrit hv'

/-! ## Step 2 : mapping a finite set of algebraic numbers into `ℚ` -/

/-- The (finite) set of critical values of `f`. -/
def critValFinset (f : ℚ[X]) : Finset ℂ :=
  (((derivative f).map (algebraMap ℚ ℂ)).roots.toFinset).image (fun w => aeval w f)

lemma critVal_eq_coe_critValFinset (f : ℚ[X]) (hf : derivative f ≠ 0) :
    critVal f = (critValFinset f : Set ℂ) := by
  have hmap : (derivative f).map (algebraMap ℚ ℂ) ≠ 0 :=
    (Polynomial.map_ne_zero_iff (algebraMap ℚ ℂ).injective).mpr hf
  ext v
  simp only [critVal, critValFinset, Set.mem_setOf_eq, Finset.coe_image, Set.mem_image,
    Finset.mem_coe, Multiset.mem_toFinset, Polynomial.mem_roots hmap, Polynomial.IsRoot,
    Polynomial.eval_map, ← Polynomial.aeval_def]

lemma degQ_pos {z : ℂ} (hz : IsAlgebraic ℚ z) : 0 < degQ z :=
  minpoly.natDegree_pos hz.isIntegral

lemma degQ_zero : degQ (0 : ℂ) = 1 := by
  rw [degQ, minpoly.zero]; simp

lemma degQ_eq_one_iff (z : ℂ) : degQ z = 1 ↔ ∃ q : ℚ, (q : ℂ) = z := by
  rw [degQ, minpoly.natDegree_eq_one_iff]
  constructor
  · rintro ⟨q, hq⟩; exact ⟨q, by simpa using hq⟩
  · rintro ⟨q, hq⟩; exact ⟨q, by simpa using hq⟩

lemma aeval_mem_adjoin_simple (z : ℂ) (f : ℚ[X]) : aeval z f ∈ ℚ⟮z⟯ :=
  IntermediateField.algebra_adjoin_le_adjoin ℚ {z} (Polynomial.aeval_mem_adjoin_singleton ℚ z)

lemma isAlgebraic_aeval {z : ℂ} (hz : IsAlgebraic ℚ z) (f : ℚ[X]) :
    IsAlgebraic ℚ (aeval z f) := by
  haveI := IntermediateField.adjoin.finiteDimensional hz.isIntegral
  haveI : Algebra.IsIntegral ℚ (ℚ⟮z⟯ : IntermediateField ℚ ℂ) := Algebra.IsIntegral.of_finite ℚ _
  have h : IsIntegral ℚ
      (⟨aeval z f, aeval_mem_adjoin_simple z f⟩ : (ℚ⟮z⟯ : IntermediateField ℚ ℂ)) :=
    Algebra.IsIntegral.isIntegral _
  exact (h.map (IntermediateField.val _)).isAlgebraic

lemma degQ_aeval_le {z : ℂ} (hz : IsAlgebraic ℚ z) (f : ℚ[X]) : degQ (aeval z f) ≤ degQ z := by
  haveI := IntermediateField.adjoin.finiteDimensional hz.isIntegral
  have hle : (ℚ⟮aeval z f⟯ : IntermediateField ℚ ℂ) ≤ ℚ⟮z⟯ :=
    IntermediateField.adjoin_simple_le_iff.mpr (aeval_mem_adjoin_simple z f)
  have h1 : Module.finrank ℚ (ℚ⟮aeval z f⟯ : IntermediateField ℚ ℂ) = degQ (aeval z f) :=
    IntermediateField.adjoin.finrank (isAlgebraic_aeval hz f).isIntegral
  have h2 : Module.finrank ℚ (ℚ⟮z⟯ : IntermediateField ℚ ℂ) = degQ z :=
    IntermediateField.adjoin.finrank hz.isIntegral
  rw [← h1, ← h2]
  haveI : FiniteDimensional ℚ
      ↥(Subalgebra.toSubmodule (ℚ⟮z⟯ : IntermediateField ℚ ℂ).toSubalgebra) :=
    inferInstanceAs (FiniteDimensional ℚ (ℚ⟮z⟯ : IntermediateField ℚ ℂ))
  exact Submodule.finrank_mono
    (show (ℚ⟮aeval z f⟯ : IntermediateField ℚ ℂ).toSubalgebra.toSubmodule
      ≤ (ℚ⟮z⟯ : IntermediateField ℚ ℂ).toSubalgebra.toSubmodule from hle)

lemma degQ_root_derivative_minpoly {α : ℂ} (h2 : 2 ≤ degQ α) {w : ℂ}
    (hw : aeval w (derivative (minpoly ℚ α)) = 0) : IsAlgebraic ℚ w ∧ degQ w ≤ degQ α - 1 := by
  have hne : derivative (minpoly ℚ α) ≠ 0 := by
    intro hcon
    have := Polynomial.natDegree_eq_zero_of_derivative_eq_zero hcon
    rw [degQ] at h2; omega
  refine ⟨⟨_, hne, hw⟩, ?_⟩
  have h1 := minpoly.degree_le_of_ne_zero ℚ w hne hw
  have h3 := Polynomial.natDegree_le_natDegree h1
  have h4 := Polynomial.natDegree_derivative_le (minpoly ℚ α)
  simp only [degQ] at *
  omega

/-- **Belyi reduction to `ℚ`**: a finite set of algebraic numbers can be mapped into `ℚ` by a
polynomial over `ℚ` all of whose critical values are also rational.  The induction is on the
maximal degree `D` occurring, and, for fixed `D`, on the number of points of degree `D`. -/
lemma exists_reduce_to_rat : ∀ (D c : ℕ) (T : Finset ℂ), (∀ t ∈ T, IsAlgebraic ℚ t) →
    (∀ t ∈ T, degQ t ≤ D) → (T.filter (fun t => degQ t = D)).card ≤ c →
    ∃ f : ℚ[X], 0 < f.natDegree ∧ (∀ t ∈ T, degQ (aeval t f) = 1) ∧
      (∀ v ∈ critVal f, degQ v = 1) := by
  intro D
  induction D using Nat.strong_induction_on with
  | _ D ihD =>
    intro c
    induction c using Nat.strong_induction_on with
    | _ c ihc =>
      intro T halg hdeg hcard
      by_cases hD : D ≤ 1
      · refine ⟨X, by simp, ?_, ?_⟩
        · intro t ht
          have h1 := degQ_pos (halg t ht)
          have h2 := hdeg t ht
          rw [aeval_X]
          omega
        · intro v hv
          rw [critVal_X] at hv
          exact absurd hv (Set.notMem_empty v)
      push_neg at hD
      rcases Nat.eq_zero_or_pos (T.filter (fun t => degQ t = D)).card with h0 | hpos
      · refine ihD (D - 1) (by omega) T.card T halg ?_ (Finset.card_filter_le _ _)
        intro t ht
        have hnm : t ∉ T.filter (fun t => degQ t = D) := by
          rw [Finset.card_eq_zero] at h0
          simp [h0]
        simp only [Finset.mem_filter, not_and] at hnm
        have h5 := hnm ht
        have h6 := hdeg t ht
        omega
      obtain ⟨α, hαmem⟩ := Finset.card_pos.mp hpos
      rw [Finset.mem_filter] at hαmem
      obtain ⟨hαT, hαD⟩ := hαmem
      have hαalg : IsAlgebraic ℚ α := halg α hαT
      set m := minpoly ℚ α with hm
      have hmdeg : m.natDegree = D := hαD
      have hmder : derivative m ≠ 0 := by
        intro hcon
        have := Polynomial.natDegree_eq_zero_of_derivative_eq_zero hcon
        omega
      have hmzero : aeval α m = 0 := minpoly.aeval ℚ α
      set T' := T.image (fun t => aeval t m) ∪ critValFinset m with hT'
      have hcritmem : ∀ u ∈ critValFinset m, IsAlgebraic ℚ u ∧ degQ u ≤ D - 1 := by
        intro u hu
        have hu' : u ∈ critVal m := by
          rw [critVal_eq_coe_critValFinset m hmder]; exact_mod_cast hu
        obtain ⟨w, hw, rfl⟩ := hu'
        obtain ⟨hwalg, hwdeg⟩ := degQ_root_derivative_minpoly (α := α) (by omega) hw
        exact ⟨isAlgebraic_aeval hwalg m, le_trans (degQ_aeval_le hwalg m) (by omega)⟩
      have halg' : ∀ u ∈ T', IsAlgebraic ℚ u := by
        intro u hu
        rcases Finset.mem_union.mp hu with h | h
        · obtain ⟨t, ht, rfl⟩ := Finset.mem_image.mp h
          exact isAlgebraic_aeval (halg t ht) m
        · exact (hcritmem u h).1
      have hdeg' : ∀ u ∈ T', degQ u ≤ D := by
        intro u hu
        rcases Finset.mem_union.mp hu with h | h
        · obtain ⟨t, ht, rfl⟩ := Finset.mem_image.mp h
          exact le_trans (degQ_aeval_le (halg t ht) m) (hdeg t ht)
        · have := (hcritmem u h).2; omega
      have hsub : T'.filter (fun u => degQ u = D) ⊆
          ((T.filter (fun t => degQ t = D)).erase α).image (fun t => aeval t m) := by
        intro u hu
        rw [Finset.mem_filter] at hu
        obtain ⟨huT', huD⟩ := hu
        rcases Finset.mem_union.mp huT' with h | h
        · obtain ⟨t, ht, htu⟩ := Finset.mem_image.mp h
          have hdt : degQ t = D := by
            have h1 : degQ u ≤ degQ t := htu ▸ degQ_aeval_le (halg t ht) m
            have h2 := hdeg t ht
            omega
          have htα : t ≠ α := by
            intro hcon
            rw [hcon, hmzero] at htu
            rw [← htu, degQ_zero] at huD
            omega
          exact Finset.mem_image.mpr
            ⟨t, Finset.mem_erase.mpr ⟨htα, Finset.mem_filter.mpr ⟨ht, hdt⟩⟩, htu⟩
        · exfalso
          have := (hcritmem u h).2
          omega
      have hcard' : (T'.filter (fun u => degQ u = D)).card ≤ c - 1 := by
        have h1 := Finset.card_le_card hsub
        have h2 := Finset.card_image_le (s := (T.filter (fun t => degQ t = D)).erase α)
          (f := fun t => aeval t m)
        have h3 : ((T.filter (fun t => degQ t = D)).erase α).card =
            (T.filter (fun t => degQ t = D)).card - 1 :=
          Finset.card_erase_of_mem (Finset.mem_filter.mpr ⟨hαT, hαD⟩)
        omega
      obtain ⟨g, hgdeg, hgeval, hgcrit⟩ := ihc (c - 1) (by omega) T' halg' hdeg' hcard'
      refine ⟨g.comp m, ?_, ?_, ?_⟩
      · rw [natDegree_comp]
        exact Nat.mul_pos hgdeg (by omega)
      · intro t ht
        rw [aeval_comp]
        exact hgeval _ (Finset.mem_union_left _ (Finset.mem_image.mpr ⟨t, ht, rfl⟩))
      · intro v hv
        rcases critVal_comp g m hv with ⟨u, hu, huv⟩ | hv'
        · rw [← huv]
          refine hgeval _ (Finset.mem_union_right _ ?_)
          rw [critVal_eq_coe_critValFinset m hmder] at hu
          exact_mod_cast hu
        · exact hgcrit v hv'

/-- The Belyi polynomials really are Belyi maps; in particular `Math2.IsBelyi` is satisfiable. -/
lemma isBelyi_belyiPoly (a b : ℕ) : IsBelyi (belyiPoly a b) :=
  ⟨belyiPoly_natDegree_pos a b, critVal_belyiPoly a b⟩

/-! ## The theorem -/

/-- A choice of rational representative of a rational complex number. -/
def ratOf (z : ℂ) : ℚ := if h : ∃ q : ℚ, (q : ℂ) = z then h.choose else 0

lemma ratOf_spec {z : ℂ} (h : degQ z = 1) : ((ratOf z : ℚ) : ℂ) = z := by
  have hex : ∃ q : ℚ, (q : ℂ) = z := (degQ_eq_one_iff z).mp h
  rw [ratOf, dif_pos hex]
  exact hex.choose_spec

/-- The hard direction of Belyi's theorem: a finite set of algebraic numbers admits a Belyi map
carrying it into `{0, 1}`. -/
lemma exists_belyi_of_algebraic (T : Finset ℂ) (h : ∀ t ∈ T, IsAlgebraic ℚ t) :
    ∃ f : ℚ[X], IsBelyi f ∧ ∀ t ∈ T, aeval t f ∈ ({0, 1} : Set ℂ) := by
  obtain ⟨f₁, hf₁deg, hf₁eval, hf₁crit⟩ :=
    exists_reduce_to_rat (T.sup degQ) T.card T h (fun t ht => Finset.le_sup ht)
      (Finset.card_filter_le _ _)
  have hder : derivative f₁ ≠ 0 := by
    intro hcon
    have := Polynomial.natDegree_eq_zero_of_derivative_eq_zero hcon
    omega
  set U : Finset ℂ := T.image (fun t => aeval t f₁) ∪ critValFinset f₁ with hU
  have hU1 : ∀ u ∈ U, degQ u = 1 := by
    intro u hu
    rcases Finset.mem_union.mp hu with hh | hh
    · obtain ⟨t, ht, rfl⟩ := Finset.mem_image.mp hh
      exact hf₁eval t ht
    · exact hf₁crit u (by rw [critVal_eq_coe_critValFinset f₁ hder]; exact_mod_cast hh)
  set T₂ : Finset ℚ := U.image ratOf with hT₂
  obtain ⟨g, hgdeg, hgeval, hgcrit⟩ := exists_belyi_rat T₂.card T₂ le_rfl
  have key : ∀ u ∈ U, aeval u g ∈ ({0, 1} : Set ℂ) := by
    intro u hu
    have h1 : ((ratOf u : ℚ) : ℂ) = u := ratOf_spec (hU1 u hu)
    have h2 : ratOf u ∈ T₂ := Finset.mem_image.mpr ⟨u, hu, rfl⟩
    rw [← h1, aeval_ratCast]
    rcases hgeval _ h2 with hh | hh <;> rw [hh] <;> simp
  refine ⟨g.comp f₁, ⟨?_, ?_⟩, ?_⟩
  · rw [natDegree_comp]; exact Nat.mul_pos hgdeg hf₁deg
  · intro v hv
    rcases critVal_comp g f₁ hv with ⟨u, hu, huv⟩ | hv'
    · rw [← huv]
      refine key u (Finset.mem_union_right _ ?_)
      rw [critVal_eq_coe_critValFinset f₁ hder] at hu
      exact_mod_cast hu
    · exact hgcrit hv'
  · intro t ht
    rw [aeval_comp]
    exact key _ (Finset.mem_union_left _ (Finset.mem_image.mpr ⟨t, ht, rfl⟩))

/-- **Belyi's theorem** for the projective line with marked points.

A finite set `S` of points of `ℙ¹(ℂ)` is defined over `ℚ̄` — i.e. all of its points are
algebraic numbers — if and only if there is a Belyi map `f : ℙ¹ → ℙ¹`, defined over `ℚ` and
ramified only over `{0, 1, ∞}`, carrying `S` into `{0, 1, ∞}`.

Belyi maps are realised here as polynomials `f ∈ ℚ[X]`.  Such a map is totally ramified over
`∞`, so `f` is ramified only over `{0,1,∞}` exactly when all of its finite critical values lie
in `{0,1}`; this is the content of `Math2.IsBelyi`.

The forward implication is Belyi's construction: first map the marked points into `ℚ` using
minimal polynomials (`Math2.exists_reduce_to_rat`), then map the resulting rational points into
`{0,1}` using the Belyi polynomials `c ⬝ x^p (1-x)^q` (`Math2.exists_belyi_rat`); in both steps
the critical values created along the way are pushed into the target as well.  The reverse
implication is immediate: a point mapped to `0` or `1` by a nonconstant `f ∈ ℚ[X]` is a root of
a nonzero rational polynomial. -/
theorem belyi_theorem (S : Set ℂ) (hS : S.Finite) :
    (∀ z ∈ S, IsAlgebraic ℚ z) ↔
      ∃ f : ℚ[X], IsBelyi f ∧ ∀ z ∈ S, aeval z f ∈ ({0, 1} : Set ℂ) := by
  constructor
  · intro halg
    obtain ⟨f, hf, hfS⟩ := exists_belyi_of_algebraic hS.toFinset
      (fun t ht => halg t (hS.mem_toFinset.mp ht))
    exact ⟨f, hf, fun z hz => hfS z (hS.mem_toFinset.mpr hz)⟩
  · rintro ⟨f, ⟨hfdeg, -⟩, hfS⟩ z hz
    have hval := hfS z hz
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hval
    rcases hval with hv | hv
    · refine ⟨f, ?_, hv⟩
      intro hcon; rw [hcon] at hfdeg; simp at hfdeg
    · refine ⟨f - C 1, ?_, ?_⟩
      · intro hcon
        have hfc : f = C 1 := by linear_combination (norm := ring_nf) hcon
        rw [hfc] at hfdeg; simp at hfdeg
      · simp [hv]

/-- Belyi's theorem for a single marked point: a complex number is algebraic if and only if
some Belyi map defined over `ℚ` sends it into the branch locus `{0, 1, ∞}`. -/
theorem belyi_theorem_point (z : ℂ) :
    IsAlgebraic ℚ z ↔ ∃ f : ℚ[X], IsBelyi f ∧ aeval z f ∈ ({0, 1} : Set ℂ) := by
  simpa using belyi_theorem {z} (Set.finite_singleton z)

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

