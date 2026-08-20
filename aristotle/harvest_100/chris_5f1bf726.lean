import Mathlib

/-!
# Belyi Theorem
Category: Frontier Math
Target: Math2.belyi_theorem
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open scoped BigOperators
open scoped Classical

set_option maxHeartbeats 1000000

open Polynomial IntermediateField

namespace Math2

/-- A complex number is a *rational point* if it lies in the image of `ℚ`. -/
def IsRatPt (x : ℂ) : Prop := ∃ q : ℚ, algebraMap ℚ ℂ q = x

/-- The degree over `ℚ` of an algebraic number. -/
noncomputable def deg (x : ℂ) : ℕ := (minpoly ℚ x).natDegree

/-! ### Basic facts about degrees -/

lemma deg_pos {x : ℂ} (hx : IsIntegral ℚ x) : 0 < deg x := minpoly.natDegree_pos hx

lemma deg_zero : deg 0 = 1 := by simp [deg, minpoly.zero]

lemma isRatPt_of_deg_le_one {x : ℂ} (hx : IsIntegral ℚ x) (h : deg x ≤ 1) : IsRatPt x := by
  have h1 : deg x = 1 := le_antisymm h (deg_pos hx)
  obtain ⟨q, hq⟩ := minpoly.natDegree_eq_one_iff.1 h1
  exact ⟨q, hq⟩

lemma aeval_mem_adjoin_simple (p : ℚ[X]) (x : ℂ) : aeval x p ∈ IntermediateField.adjoin ℚ {x} := by
  have hx : x ∈ ℚ⟮x⟯ := IntermediateField.mem_adjoin_simple_self ℚ x
  have h := Subalgebra.aeval_coe (R := ℚ) (A := ℂ) (S := ℚ⟮x⟯.toSubalgebra) ⟨x, hx⟩ p
  simp only at h
  rw [show ((aeval x) p) = ((aeval (⟨x, hx⟩ : ℚ⟮x⟯) p : ℚ⟮x⟯) : ℂ) by simpa using h]
  exact SetLike.coe_mem _

/-- A polynomial expression in an algebraic number is algebraic. -/
lemma isIntegral_aeval {x : ℂ} (hx : IsIntegral ℚ x) (p : ℚ[X]) : IsIntegral ℚ (aeval x p) := by
  haveI : FiniteDimensional ℚ ℚ⟮x⟯ := IntermediateField.adjoin.finiteDimensional hx
  have hmem : aeval x p ∈ ℚ⟮x⟯ := aeval_mem_adjoin_simple p x
  have h1 : IsIntegral ℚ (⟨aeval x p, hmem⟩ : ℚ⟮x⟯) := IsIntegral.of_finite ℚ _
  exact h1.map ℚ⟮x⟯.val

/-- Applying a rational polynomial cannot increase the degree. -/
lemma deg_aeval_le {x : ℂ} (hx : IsIntegral ℚ x) (p : ℚ[X]) : deg (aeval x p) ≤ deg x := by
  have hiy : IsIntegral ℚ (aeval x p) := isIntegral_aeval hx p
  haveI : FiniteDimensional ℚ ℚ⟮x⟯ := IntermediateField.adjoin.finiteDimensional hx
  have hle : ℚ⟮aeval x p⟯ ≤ ℚ⟮x⟯ := by
    rw [IntermediateField.adjoin_simple_le_iff]
    exact aeval_mem_adjoin_simple p x
  have h2 := finrank_le_of_le_right hle
  rw [IntermediateField.adjoin.finrank hx, IntermediateField.adjoin.finrank hiy] at h2
  exact h2

/-- A root of a nonzero rational polynomial is algebraic. -/
lemma isIntegral_of_aeval_eq_zero {q : ℚ[X]} (hq : q ≠ 0) {c : ℂ} (h : aeval c q = 0) :
    IsIntegral ℚ c :=
  ⟨q * C (q.leadingCoeff)⁻¹, monic_mul_leadingCoeff_inv hq, by
    rw [← aeval_def, map_mul, h, zero_mul]⟩

/-- A root of a nonzero rational polynomial has degree at most the degree of that
polynomial. -/
lemma deg_le_of_aeval_eq_zero {q : ℚ[X]} (hq : q ≠ 0) {c : ℂ} (h : aeval c q = 0) :
    deg c ≤ q.natDegree := by
  have hm : (q * C (q.leadingCoeff)⁻¹).Monic := monic_mul_leadingCoeff_inv hq
  have h0 : aeval c (q * C (q.leadingCoeff)⁻¹) = 0 := by simp [h]
  have hmin := minpoly.min ℚ c hm h0
  have hd : (q * C (q.leadingCoeff)⁻¹).natDegree = q.natDegree := by
    simp [natDegree_mul_leadingCoeff_inv, hq]
  exact (natDegree_le_natDegree hmin).trans_eq hd

/-! ### Critical values of a composition -/

lemma critval_comp {g p : ℚ[X]} {c : ℂ}
    (h : aeval c (derivative (g.comp p)) = 0) :
    aeval c (derivative p) = 0 ∨ aeval (aeval c p) (derivative g) = 0 := by
  rw [derivative_comp, map_mul] at h
  rcases mul_eq_zero.1 h with h1 | h2
  · exact Or.inl h1
  · exact Or.inr (by rwa [aeval_comp] at h2)

/-! ### Phase 1 : killing the irrationality of the critical values -/

/-- If all points of `S` are rational, the identity works. -/
lemma phase1_trivial (S : Finset ℂ) (hint : ∀ β ∈ S, IsIntegral ℚ β) (h : ∀ β ∈ S, deg β ≤ 1) :
    ∃ f : ℚ[X], 0 < f.natDegree ∧ (∀ β ∈ S, IsRatPt (aeval β f)) ∧
      (∀ c : ℂ, aeval c (derivative f) = 0 → IsRatPt (aeval c f)) := by
  refine ⟨X, by simp, fun β hβ => ?_, fun c hc => ?_⟩
  · simpa using isRatPt_of_deg_le_one (hint β hβ) (h β hβ)
  · simp at hc

/-- Belyi's first reduction: for any finite set `S` of algebraic numbers there is a
rational polynomial `f` mapping `S` into `ℚ` and having all its critical values in `ℚ`. -/
lemma phase1 : ∀ d k : ℕ, ∀ S : Finset ℂ, (∀ β ∈ S, IsIntegral ℚ β) →
    (∀ β ∈ S, deg β ≤ d) →
    (S.filter (fun β => deg β = d)).card ≤ k →
    ∃ f : ℚ[X], 0 < f.natDegree ∧ (∀ β ∈ S, IsRatPt (aeval β f)) ∧
      (∀ c : ℂ, aeval c (derivative f) = 0 → IsRatPt (aeval c f)) := by
  intro d
  induction d using Nat.strong_induction_on with
  | _ d IHd =>
    intro k
    induction k with
    | zero =>
      intro S hint hS hcard
      rcases Nat.lt_or_ge d 2 with hd | hd
      · exact phase1_trivial S hint (fun β hβ => by have := hS β hβ; omega)
      · refine IHd (d - 1) (by omega) S.card S hint (fun β hβ => ?_) (Finset.card_filter_le _ _)
        have h1 := hS β hβ
        have h2 : deg β ≠ d := by
          intro he
          have hmem : β ∈ S.filter (fun β => deg β = d) := Finset.mem_filter.2 ⟨hβ, he⟩
          rw [Finset.card_eq_zero.1 (Nat.le_zero.1 hcard)] at hmem
          simp at hmem
        omega
    | succ k IHk =>
      intro S hint hS hcard
      rcases le_or_gt (S.filter (fun β => deg β = d)).card k with hsmall | hbig
      · exact IHk S hint hS hsmall
      rcases Nat.lt_or_ge d 2 with hd | hd
      · exact phase1_trivial S hint (fun β hβ => by have := hS β hβ; omega)
      obtain ⟨α, hα⟩ : (S.filter (fun β => deg β = d)).Nonempty :=
        Finset.card_pos.1 (by omega)
      obtain ⟨hαS, hαd⟩ := Finset.mem_filter.1 hα
      set p : ℚ[X] := minpoly ℚ α with hp
      have hpdeg : p.natDegree = d := hαd
      have hderiv0 : derivative p ≠ 0 := by
        intro hc
        have := Polynomial.natDegree_eq_zero_of_derivative_eq_zero hc
        omega
      set crit : Finset ℂ := ((derivative p).aroots ℂ).toFinset with hcrit
      set S' : Finset ℂ :=
        S.image (fun β => aeval β p) ∪ crit.image (fun c => aeval c p) with hS'def
      have hcritlt : ∀ c ∈ crit, deg (aeval c p) < d := by
        intro c hc
        rw [hcrit, Multiset.mem_toFinset, mem_aroots] at hc
        have hcint : IsIntegral ℚ c := isIntegral_of_aeval_eq_zero hderiv0 hc.2
        have h1 : deg c ≤ (derivative p).natDegree := deg_le_of_aeval_eq_zero hderiv0 hc.2
        have h2 : (derivative p).natDegree < p.natDegree := natDegree_derivative_lt (by omega)
        calc deg (aeval c p) ≤ deg c := deg_aeval_le hcint p
          _ ≤ (derivative p).natDegree := h1
          _ < d := by omega
      have hαimg : aeval α p = 0 := minpoly.aeval ℚ α
      have hbound : ∀ γ ∈ S', deg γ ≤ d := by
        intro γ hγ
        rw [hS'def, Finset.mem_union] at hγ
        rcases hγ with hγ | hγ
        · obtain ⟨β, hβS, rfl⟩ := Finset.mem_image.1 hγ
          exact (deg_aeval_le (hint β hβS) p).trans (hS β hβS)
        · obtain ⟨c, hc, rfl⟩ := Finset.mem_image.1 hγ
          exact le_of_lt (hcritlt c hc)
      have hsub : S'.filter (fun γ => deg γ = d) ⊆
          ((S.filter (fun β => deg β = d)).erase α).image (fun β => aeval β p) := by
        intro γ hγ
        obtain ⟨hγS', hγd⟩ := Finset.mem_filter.1 hγ
        rw [hS'def, Finset.mem_union] at hγS'
        rcases hγS' with hγ1 | hγ1
        · obtain ⟨β, hβS, hβγ⟩ := Finset.mem_image.1 hγ1
          have hdβ : deg β = d := by
            have h1 : deg γ ≤ deg β := by rw [← hβγ]; exact deg_aeval_le (hint β hβS) p
            have := hS β hβS
            omega
          have hβα : β ≠ α := by
            rintro rfl
            rw [hαimg] at hβγ
            rw [← hβγ, deg_zero] at hγd
            omega
          exact Finset.mem_image.2 ⟨β, Finset.mem_erase.2 ⟨hβα, Finset.mem_filter.2 ⟨hβS, hdβ⟩⟩,
            hβγ⟩
        · obtain ⟨c, hc, hcγ⟩ := Finset.mem_image.1 hγ1
          exact absurd hγd (by rw [← hcγ]; exact Nat.ne_of_lt (hcritlt c hc))
      have hcount : (S'.filter (fun γ => deg γ = d)).card ≤ k := by
        have h1 := Finset.card_le_card hsub
        have h2 := Finset.card_image_le (s := (S.filter (fun β => deg β = d)).erase α)
          (f := fun β => aeval β p)
        have h3 : ((S.filter (fun β => deg β = d)).erase α).card =
            (S.filter (fun β => deg β = d)).card - 1 := Finset.card_erase_of_mem hα
        omega
      have hint' : ∀ γ ∈ S', IsIntegral ℚ γ := by
        intro γ hγ
        rw [hS'def, Finset.mem_union] at hγ
        rcases hγ with hγ | hγ
        · obtain ⟨β, hβS, rfl⟩ := Finset.mem_image.1 hγ
          exact isIntegral_aeval (hint β hβS) p
        · obtain ⟨c, hc, rfl⟩ := Finset.mem_image.1 hγ
          rw [hcrit, Multiset.mem_toFinset, mem_aroots] at hc
          exact isIntegral_aeval (isIntegral_of_aeval_eq_zero hderiv0 hc.2) p
      obtain ⟨g, hg1, hg2, hg3⟩ := IHk S' hint' hbound hcount
      have hpS' : ∀ β ∈ S, aeval β p ∈ S' := fun β hβ =>
        Finset.mem_union_left _ (Finset.mem_image.2 ⟨β, hβ, rfl⟩)
      refine ⟨g.comp p, ?_, ?_, ?_⟩
      · rw [natDegree_comp]
        exact Nat.mul_pos hg1 (by omega)
      · intro β hβ
        rw [aeval_comp]
        exact hg2 _ (hpS' β hβ)
      · intro c hc
        rw [aeval_comp]
        rcases critval_comp hc with h1 | h1
        · refine hg2 _ (Finset.mem_union_right _ (Finset.mem_image.2 ⟨c, ?_, rfl⟩))
          rw [hcrit, Multiset.mem_toFinset, mem_aroots]
          exact ⟨hderiv0, h1⟩
        · exact hg3 _ h1

lemma phase1' (S : Finset ℂ) (hint : ∀ β ∈ S, IsIntegral ℚ β) :
    ∃ f : ℚ[X], 0 < f.natDegree ∧ (∀ β ∈ S, IsRatPt (aeval β f)) ∧
      (∀ c : ℂ, aeval c (derivative f) = 0 → IsRatPt (aeval c f)) :=
  phase1 (S.sup deg) S.card S hint (fun _ hβ => Finset.le_sup hβ) (Finset.card_filter_le _ _)

/-! ### The Belyi polynomial `x ↦ c · xᵐ (1-x)ⁿ` -/

/-- The normalising constant `(m+n)^(m+n) / (mᵐ nⁿ)` for `m = a+1`, `n = b+1`. -/
noncomputable def belyiConst (a b : ℕ) : ℚ :=
  ((a + b + 2 : ℚ) ^ (a + b + 2)) / ((a + 1 : ℚ) ^ (a + 1) * (b + 1 : ℚ) ^ (b + 1))

/-- The normalised Belyi polynomial attached to `m = a+1`, `n = b+1`. -/
noncomputable def belyiPoly (a b : ℕ) : ℚ[X] :=
  C (belyiConst a b) * (X ^ (a + 1) * (1 - X) ^ (b + 1))

lemma belyiConst_pos (a b : ℕ) : 0 < belyiConst a b := by
  unfold belyiConst; positivity

lemma belyiConst_ne_zero (a b : ℕ) : belyiConst a b ≠ 0 := ne_of_gt (belyiConst_pos a b)

lemma belyiPoly_natDegree (a b : ℕ) : (belyiPoly a b).natDegree = a + b + 2 := by
  unfold belyiPoly
  compute_degree! <;> first | omega | exact ⟨by omega, belyiConst_ne_zero a b⟩

lemma belyiPoly_eval_zero (a b : ℕ) : (belyiPoly a b).eval 0 = 0 := by simp [belyiPoly]

lemma belyiPoly_eval_one (a b : ℕ) : (belyiPoly a b).eval 1 = 0 := by simp [belyiPoly]

/-- The unique interior critical point of the Belyi polynomial. -/
noncomputable def belyiCrit (a b : ℕ) : ℚ := ((a : ℚ) + 1) / ((a : ℚ) + b + 2)

lemma belyiCrit_mem (a b : ℕ) : 0 < belyiCrit a b ∧ belyiCrit a b < 1 := by
  have h : (0:ℚ) < (a : ℚ) + b + 2 := by positivity
  rw [belyiCrit]
  refine ⟨div_pos (by positivity) h, ?_⟩
  rw [div_lt_one h]
  linarith [Nat.cast_nonneg (α := ℚ) b]

lemma belyiPoly_eval_crit (a b : ℕ) : (belyiPoly a b).eval (belyiCrit a b) = 1 := by
  have hden : ((a:ℚ) + b + 2) ≠ 0 := by positivity
  have h1 : ((a:ℚ) + 1) ≠ 0 := by positivity
  have h2 : ((b:ℚ) + 1) ≠ 0 := by positivity
  simp only [belyiPoly, belyiConst, belyiCrit, eval_mul, eval_C, eval_pow, eval_X, eval_sub,
    eval_one]
  rw [show (1 - ((a:ℚ) + 1) / ((a:ℚ) + b + 2)) = ((b:ℚ) + 1) / ((a:ℚ) + b + 2) by
    field_simp; ring]
  rw [div_pow, div_pow, show a + b + 2 = (a + 1) + (b + 1) by omega, pow_add]
  field_simp

/-- The derivative of the Belyi polynomial, in factored form. -/
lemma belyiPoly_derivative (a b : ℕ) :
    derivative (belyiPoly a b) =
      C (belyiConst a b) *
        (X ^ a * ((1 - X) ^ b * (C ((a : ℚ) + 1) - C ((a : ℚ) + b + 2) * X))) := by
  unfold belyiPoly
  rw [derivative_mul, derivative_C, zero_mul, zero_add, derivative_mul, derivative_X_pow,
    derivative_pow]
  simp only [Nat.add_sub_cancel, derivative_sub, derivative_one, derivative_X, zero_sub,
    Nat.cast_add, Nat.cast_one, C_add, C_1, map_natCast, C_ofNat]
  ring

/-- The critical points of the Belyi polynomial are `0`, `1` and `(a+1)/(a+b+2)`. -/
lemma belyiPoly_critical_points (a b : ℕ) {c : ℂ}
    (h : aeval c (derivative (belyiPoly a b)) = 0) :
    c = 0 ∨ c = 1 ∨ c = algebraMap ℚ ℂ (belyiCrit a b) := by
  rw [belyiPoly_derivative] at h
  simp only [map_mul, map_sub, map_pow, aeval_C, aeval_X, map_one, map_add, map_ofNat,
    map_natCast, mul_eq_zero] at h
  have hbc : (algebraMap ℚ ℂ) (belyiConst a b) ≠ 0 :=
    (map_ne_zero_iff _ (algebraMap ℚ ℂ).injective).2 (belyiConst_ne_zero a b)
  have hden : ((a:ℚ) + b + 2) ≠ 0 := by positivity
  have hneQ : ((a : ℂ) + (b : ℂ) + 2) ≠ 0 := by
    rw [show ((a : ℂ) + (b : ℂ) + 2) = algebraMap ℚ ℂ ((a:ℚ) + b + 2) by
      simp only [map_add, map_natCast, map_ofNat]]
    exact (map_ne_zero_iff _ (algebraMap ℚ ℂ).injective).2 hden
  rcases h with h | h | h | h
  · exact absurd h hbc
  · exact Or.inl (pow_eq_zero_iff'.1 h).1
  · refine Or.inr (Or.inl ?_)
    have h1 : (1 : ℂ) - c = 0 := (pow_eq_zero_iff'.1 h).1
    linear_combination -h1
  · refine Or.inr (Or.inr ?_)
    rw [belyiCrit, map_div₀]
    simp only [map_add, map_natCast, map_ofNat, map_one]
    rw [eq_div_iff hneQ]
    linear_combination -h

/-- Evaluating at a rational point commutes with the embedding `ℚ → ℚ̄`. -/
lemma aeval_ratPoint (q : ℚ) (p : ℚ[X]) :
    aeval (algebraMap ℚ ℂ q) p = algebraMap ℚ ℂ (p.eval q) :=
  (Polynomial.aeval_algebraMap_apply _ _ _).trans (by simp)

/-- All critical values of the Belyi polynomial are `0` or `1`. -/
lemma belyiPoly_critval (a b : ℕ) {c : ℂ}
    (h : aeval c (derivative (belyiPoly a b)) = 0) :
    aeval c (belyiPoly a b) = 0 ∨ aeval c (belyiPoly a b) = 1 := by
  rcases belyiPoly_critical_points a b h with rfl | rfl | rfl
  · left; simp [belyiPoly]
  · left; simp [belyiPoly]
  · right; rw [aeval_ratPoint, belyiPoly_eval_crit, map_one]

/-- The sharp bound `xᵐ (1-x)ⁿ (m+n)^(m+n) ≤ mᵐ nⁿ` on `[0,1]` (weighted AM–GM). -/
lemma amgm_bound (m n : ℕ) (hm : 0 < m) (hn : 0 < n) (x : ℝ) (h0 : 0 ≤ x) (h1 : x ≤ 1) :
    x ^ m * (1 - x) ^ n * ((m : ℝ) + n) ^ (m + n) ≤ (m : ℝ) ^ m * (n : ℝ) ^ n := by
  have hm' : (0:ℝ) < m := by exact_mod_cast hm
  have hn' : (0:ℝ) < n := by exact_mod_cast hn
  set s : ℝ := (m:ℝ) + n with hsdef
  have hs : (0:ℝ) < s := by positivity
  have hx1 : (0:ℝ) ≤ 1 - x := by linarith
  have hp1 : (0:ℝ) ≤ x * s / m := by positivity
  have hp2 : (0:ℝ) ≤ (1 - x) * s / n := by positivity
  have hw : (m:ℝ)/s + (n:ℝ)/s = 1 := by rw [← add_div, hsdef]; field_simp
  have key := Real.geom_mean_le_arith_mean2_weighted (by positivity : (0:ℝ) ≤ (m:ℝ)/s)
    (by positivity : (0:ℝ) ≤ (n:ℝ)/s) hp1 hp2 hw
  have hrhs : ((m:ℝ)/s) * (x * s / m) + ((n:ℝ)/s) * ((1-x) * s / n) = 1 := by
    field_simp
    ring
  rw [hrhs] at key
  have h2 : ((x * s / m) ^ ((m:ℝ)/s) * ((1-x) * s / n) ^ ((n:ℝ)/s)) ^ s ≤ (1:ℝ) ^ s :=
    Real.rpow_le_rpow (by positivity) key (le_of_lt hs)
  rw [Real.mul_rpow (by positivity) (by positivity), ← Real.rpow_mul hp1, ← Real.rpow_mul hp2,
    div_mul_cancel₀ _ (ne_of_gt hs), div_mul_cancel₀ _ (ne_of_gt hs), Real.one_rpow,
    Real.rpow_natCast, Real.rpow_natCast] at h2
  rw [div_pow, div_pow, mul_pow, mul_pow, div_mul_div_comm, div_le_one (by positivity)] at h2
  rw [pow_add]
  calc x ^ m * (1 - x) ^ n * (s ^ m * s ^ n) = x ^ m * s ^ m * ((1 - x) ^ n * s ^ n) := by ring
    _ ≤ (m:ℝ) ^ m * (n:ℝ) ^ n := h2

/-- The Belyi polynomial maps `[0,1]` into `[0,1]`. -/
lemma belyiPoly_maps_unit_interval (a b : ℕ) {x : ℚ} (h0 : 0 ≤ x) (h1 : x ≤ 1) :
    0 ≤ (belyiPoly a b).eval x ∧ (belyiPoly a b).eval x ≤ 1 := by
  have hx1 : (0:ℚ) ≤ 1 - x := by linarith
  have hev : (belyiPoly a b).eval x = belyiConst a b * (x ^ (a+1) * (1-x) ^ (b+1)) := by
    simp [belyiPoly]
  have hcpos : (0:ℚ) < belyiConst a b := belyiConst_pos a b
  refine ⟨by rw [hev]; positivity, ?_⟩
  have hR := amgm_bound (a+1) (b+1) (Nat.succ_pos a) (Nat.succ_pos b) (x:ℝ)
    (by exact_mod_cast h0) (by exact_mod_cast h1)
  push_cast at hR
  have hQ : x ^ (a+1) * (1-x) ^ (b+1) * ((a:ℚ) + b + 2) ^ (a + b + 2) ≤
      ((a:ℚ)+1) ^ (a+1) * ((b:ℚ)+1) ^ (b+1) := by
    have hcast : ((x ^ (a+1) * (1-x) ^ (b+1) * ((a:ℚ) + b + 2) ^ (a + b + 2) : ℚ) : ℝ) ≤
        ((((a:ℚ)+1) ^ (a+1) * ((b:ℚ)+1) ^ (b+1) : ℚ) : ℝ) := by
      push_cast
      calc ((x:ℝ) ^ (a+1) * (1-(x:ℝ)) ^ (b+1) * (((a:ℝ) + b + 2) ^ (a + b + 2)))
          = (x:ℝ) ^ (a+1) * (1-(x:ℝ)) ^ (b+1) * (((a:ℝ)+1) + ((b:ℝ)+1)) ^ ((a+1) + (b+1)) := by
            ring_nf
        _ ≤ ((a:ℝ)+1) ^ (a+1) * ((b:ℝ)+1) ^ (b+1) := hR
    exact_mod_cast hcast
  rw [hev, belyiConst, div_mul_eq_mul_div, div_le_one (by positivity)]
  nlinarith [hQ]


/-! ### Phase 2 : reducing a finite set of rationals to `{0,1}` -/

/-- Every rational number in `(0,1)` is the interior critical point of a Belyi polynomial. -/
lemma exists_belyiCrit {lam : ℚ} (h0 : 0 < lam) (h1 : lam < 1) :
    ∃ a b : ℕ, belyiCrit a b = lam := by
  have hnum : 0 < lam.num := Rat.num_pos.2 h0
  have hlt : lam.num < (lam.den : ℤ) := Rat.lt_one_iff_num_lt_denom.mp h1
  set p : ℕ := lam.num.toNat with hp
  have hpnum : (p : ℤ) = lam.num := Int.toNat_of_nonneg (le_of_lt hnum)
  have hp1 : 1 ≤ p := by omega
  have hpq : p + 1 ≤ lam.den := by omega
  refine ⟨p - 1, lam.den - p - 1, ?_⟩
  have hn1 : (p - 1) + 1 = p := by omega
  have hn2 : (p - 1) + (lam.den - p - 1) + 2 = lam.den := by omega
  have hcast1 : ((p - 1 : ℕ) : ℚ) + 1 = (p : ℚ) := by
    exact_mod_cast congrArg (Nat.cast (R := ℚ)) hn1
  have hcast2 : ((p - 1 : ℕ) : ℚ) + ((lam.den - p - 1 : ℕ) : ℚ) + 2 = (lam.den : ℚ) := by
    exact_mod_cast congrArg (Nat.cast (R := ℚ)) hn2
  rw [belyiCrit, hcast1, hcast2, show (p:ℚ) = (lam.num : ℚ) by exact_mod_cast hpnum]
  exact Rat.num_div_den lam

lemma phase2 : ∀ N : ℕ, ∀ T : Finset ℚ, (∀ q ∈ T, 0 ≤ q ∧ q ≤ 1) → (0 : ℚ) ∈ T →
    (1 : ℚ) ∈ T → T.card ≤ N →
    ∃ g : ℚ[X], 0 < g.natDegree ∧ (∀ q ∈ T, g.eval q = 0 ∨ g.eval q = 1) ∧
      (∀ x : ℚ, 0 ≤ x → x ≤ 1 → 0 ≤ g.eval x ∧ g.eval x ≤ 1) ∧
      (∀ c : ℂ, aeval c (derivative g) = 0 → aeval c g = 0 ∨ aeval c g = 1) := by
  intro N
  induction N with
  | zero =>
    intro T _ h0 _ hcard
    have := Finset.card_pos.2 ⟨0, h0⟩
    omega
  | succ N IH =>
    intro T hT h0 h1 hcard
    by_cases hsmall : T.card ≤ N
    · exact IH T hT h0 h1 hsmall
    by_cases htriv : ∀ q ∈ T, q = 0 ∨ q = 1
    · refine ⟨X, by simp, fun q hq => by simpa using htriv q hq,
        fun x hx0 hx1 => by simpa using ⟨hx0, hx1⟩, fun c hc => by simp at hc⟩
    push_neg at htriv
    obtain ⟨lam, hlamT, hlam0, hlam1⟩ := htriv
    obtain ⟨hlamge, hlamle⟩ := hT lam hlamT
    have hl0 : 0 < lam := lt_of_le_of_ne hlamge (Ne.symm hlam0)
    have hl1 : lam < 1 := lt_of_le_of_ne hlamle hlam1
    obtain ⟨a, b, hab⟩ := exists_belyiCrit hl0 hl1
    set f := belyiPoly a b with hf
    set T' : Finset ℚ := T.image f.eval ∪ {0, 1} with hT'def
    have hev0 : f.eval 0 = 0 := belyiPoly_eval_zero a b
    have hev1 : f.eval 1 = 0 := belyiPoly_eval_one a b
    have hevl : f.eval lam = 1 := by rw [← hab]; exact belyiPoly_eval_crit a b
    have hT'mem : ∀ q ∈ T', 0 ≤ q ∧ q ≤ 1 := by
      intro q hq
      rw [hT'def, Finset.mem_union] at hq
      rcases hq with hq | hq
      · obtain ⟨r, hr, rfl⟩ := Finset.mem_image.1 hq
        exact belyiPoly_maps_unit_interval a b (hT r hr).1 (hT r hr).2
      · simp only [Finset.mem_insert, Finset.mem_singleton] at hq
        rcases hq with rfl | rfl <;> norm_num
    have h0' : (0:ℚ) ∈ T' := Finset.mem_union_right _ (by simp)
    have h1' : (1:ℚ) ∈ T' := Finset.mem_union_right _ (by simp)
    have hcard' : T'.card ≤ N := by
      have hsub : T' ⊆ (T \ {0, 1, lam}).image f.eval ∪ {0, 1} := by
        intro q hq
        rw [hT'def, Finset.mem_union] at hq
        rcases hq with hq | hq
        · obtain ⟨r, hr, rfl⟩ := Finset.mem_image.1 hq
          by_cases hmem : r = 0 ∨ r = 1 ∨ r = lam
          · refine Finset.mem_union_right _ ?_
            rcases hmem with rfl | rfl | rfl
            · simp [hev0]
            · simp [hev1]
            · simp [hevl]
          · push_neg at hmem
            refine Finset.mem_union_left _ (Finset.mem_image.2 ⟨r, ?_, rfl⟩)
            simp only [Finset.mem_sdiff, Finset.mem_insert, Finset.mem_singleton]
            exact ⟨hr, by tauto⟩
        · exact Finset.mem_union_right _ hq
      have hss : ({0, 1, lam} : Finset ℚ) ⊆ T := by
        intro q hq
        simp only [Finset.mem_insert, Finset.mem_singleton] at hq
        rcases hq with rfl | rfl | rfl
        · exact h0
        · exact h1
        · exact hlamT
      have h3 : ({0, 1, lam} : Finset ℚ).card = 3 := by
        rw [Finset.card_insert_of_notMem (by simp [Ne.symm hlam0]),
          Finset.card_insert_of_notMem (by simp [Ne.symm hlam1])]
        simp
      have hsd : (T \ ({0, 1, lam} : Finset ℚ)).card = T.card - 3 := by
        rw [Finset.card_sdiff_of_subset hss, h3]
      have hu := Finset.card_union_le ((T \ ({0, 1, lam} : Finset ℚ)).image f.eval)
        ({0, 1} : Finset ℚ)
      have himg := Finset.card_image_le (s := T \ ({0, 1, lam} : Finset ℚ)) (f := f.eval)
      have h2 : ({0, 1} : Finset ℚ).card ≤ 2 := Finset.card_insert_le _ _ |>.trans (by simp)
      have hmain := Finset.card_le_card hsub
      have hTcard : 3 ≤ T.card := h3 ▸ Finset.card_le_card hss
      omega
    obtain ⟨g, hg1, hg2, hg3, hg4⟩ := IH T' hT'mem h0' h1' hcard'
    have e0 : aeval (0:ℂ) g = algebraMap ℚ ℂ (g.eval 0) := by
      simpa using aeval_ratPoint (0:ℚ) g
    have e1 : aeval (1:ℂ) g = algebraMap ℚ ℂ (g.eval 1) := by
      simpa using aeval_ratPoint (1:ℚ) g
    have hval01 : ∀ q : ℚ, q ∈ T' → algebraMap ℚ ℂ (g.eval q) = 0 ∨
        algebraMap ℚ ℂ (g.eval q) = 1 := by
      intro q hq
      rcases hg2 q hq with he | he
      · exact Or.inl (by rw [he, map_zero])
      · exact Or.inr (by rw [he, map_one])
    refine ⟨g.comp f, ?_, ?_, ?_, ?_⟩
    · rw [natDegree_comp]
      have hfd : 0 < f.natDegree := by rw [hf, belyiPoly_natDegree]; omega
      exact Nat.mul_pos hg1 hfd
    · intro q hq
      rw [eval_comp]
      exact hg2 _ (Finset.mem_union_left _ (Finset.mem_image.2 ⟨q, hq, rfl⟩))
    · intro x hx0 hx1
      rw [eval_comp]
      obtain ⟨hb0, hb1⟩ := belyiPoly_maps_unit_interval a b hx0 hx1
      exact hg3 _ hb0 hb1
    · intro c hc
      rw [aeval_comp]
      rcases critval_comp hc with h | h
      · rcases belyiPoly_critval a b h with hv | hv
        · rw [hv, e0]
          exact hval01 0 h0'
        · rw [hv, e1]
          exact hval01 1 h1'
      · exact hg4 _ h


/-! ### Belyi's theorem for the projective line -/

/-- **Belyi's theorem** (for `ℙ¹`): for every finite set `S` of algebraic numbers there is a
nonconstant map `f : ℙ¹ → ℙ¹` defined over `ℚ` (here a polynomial, so that `∞ ↦ ∞`) which
sends `S` into `{0, 1}` and all of whose finite critical values lie in `{0, 1}`; that is,
`f` is ramified only over `{0, 1, ∞}`. -/
theorem belyi_theorem (S : Finset ℂ) :
    (∀ β ∈ S, IsAlgebraic ℚ β) ↔
      ∃ f : ℚ[X], 0 < f.natDegree ∧
        (∀ β ∈ S, aeval β f = 0 ∨ aeval β f = 1) ∧
        (∀ c : ℂ, aeval c (derivative f) = 0 → aeval c f = 0 ∨ aeval c f = 1) := by
  classical
  constructor
  swap
  · rintro ⟨f, hfdeg, hfS, -⟩ β hβ
    have hf0 : f ≠ 0 := by
      intro hc
      rw [hc] at hfdeg
      simp at hfdeg
    rcases hfS β hβ with h | h
    · exact ⟨f, hf0, h⟩
    · refine ⟨f - 1, ?_, by simp [h]⟩
      intro hc
      rw [sub_eq_zero.1 hc] at hfdeg
      simp at hfdeg
  intro halg
  have hint : ∀ β ∈ S, IsIntegral ℚ β := fun β hβ => (halg β hβ).isIntegral
  obtain ⟨f₁, hf₁deg, hf₁S, hf₁crit⟩ := phase1' S hint
  have hd1 : derivative f₁ ≠ 0 := by
    intro hc
    have := Polynomial.natDegree_eq_zero_of_derivative_eq_zero hc
    omega
  set r : ℂ → ℚ := fun x => Function.invFun (algebraMap ℚ ℂ) x with hrdef
  have hrspec : ∀ x : ℂ, IsRatPt x → algebraMap ℚ ℂ (r x) = x := by
    rintro x ⟨q, hq⟩
    exact Function.invFun_eq ⟨q, hq⟩
  set crit : Finset ℂ := ((derivative f₁).aroots ℂ).toFinset with hcritdef
  set T₀ : Finset ℚ := insert 0 (insert 1
    (S.image (fun β => r (aeval β f₁)) ∪ crit.image (fun c => r (aeval c f₁)))) with hT₀def
  have hT₀ne : T₀.Nonempty := ⟨0, by rw [hT₀def]; exact Finset.mem_insert_self _ _⟩
  set A : ℚ := T₀.min' hT₀ne with hA
  set B : ℚ := T₀.max' hT₀ne with hB
  have h0T₀ : (0:ℚ) ∈ T₀ := by rw [hT₀def]; exact Finset.mem_insert_self _ _
  have h1T₀ : (1:ℚ) ∈ T₀ := by
    rw [hT₀def]; exact Finset.mem_insert_of_mem (Finset.mem_insert_self _ _)
  have hA0 : A ≤ 0 := T₀.min'_le 0 h0T₀
  have hB1 : (1:ℚ) ≤ B := T₀.le_max' 1 h1T₀
  have hAB : 0 < B - A := by linarith
  set φ : ℚ[X] := C (B - A)⁻¹ * (X - C A) with hφ
  have hφeval : ∀ q : ℚ, φ.eval q = (q - A) / (B - A) := by
    intro q
    rw [hφ]
    simp [div_eq_inv_mul]
  have hφdeg : φ.natDegree = 1 := by
    rw [hφ]
    have hne : B - A ≠ 0 := by intro h; rw [h] at hAB; exact lt_irrefl 0 hAB
    compute_degree!
  have hφderiv : derivative φ = C (B - A)⁻¹ := by rw [hφ]; simp
  have hφmaps : ∀ q ∈ T₀, 0 ≤ φ.eval q ∧ φ.eval q ≤ 1 := by
    intro q hq
    rw [hφeval]
    have hq1 : A ≤ q := T₀.min'_le q hq
    have hq2 : q ≤ B := T₀.le_max' q hq
    exact ⟨div_nonneg (by linarith) (le_of_lt hAB), by rw [div_le_one hAB]; linarith⟩
  set T : Finset ℚ := T₀.image φ.eval ∪ {0, 1} with hTdef
  have hTmem : ∀ q ∈ T, 0 ≤ q ∧ q ≤ 1 := by
    intro q hq
    rw [hTdef, Finset.mem_union] at hq
    rcases hq with hq | hq
    · obtain ⟨s, hs, rfl⟩ := Finset.mem_image.1 hq
      exact hφmaps s hs
    · simp only [Finset.mem_insert, Finset.mem_singleton] at hq
      rcases hq with rfl | rfl <;> norm_num
  have h0T : (0:ℚ) ∈ T := Finset.mem_union_right _ (by simp)
  have h1T : (1:ℚ) ∈ T := Finset.mem_union_right _ (by simp)
  obtain ⟨g, hg1, hg2, hg3, hg4⟩ := phase2 T.card T hTmem h0T h1T le_rfl
  have key : ∀ q : ℚ, q ∈ T₀ → aeval (algebraMap ℚ ℂ q) (g.comp φ) = 0 ∨
      aeval (algebraMap ℚ ℂ q) (g.comp φ) = 1 := by
    intro q hq
    rw [aeval_ratPoint, eval_comp]
    rcases hg2 (φ.eval q) (Finset.mem_union_left _ (Finset.mem_image.2 ⟨q, hq, rfl⟩)) with h | h
    · exact Or.inl (by rw [h, map_zero])
    · exact Or.inr (by rw [h, map_one])
  refine ⟨(g.comp φ).comp f₁, ?_, ?_, ?_⟩
  · rw [natDegree_comp, natDegree_comp, hφdeg, mul_one]
    exact Nat.mul_pos hg1 hf₁deg
  · intro β hβ
    rw [aeval_comp, ← hrspec _ (hf₁S β hβ)]
    refine key _ ?_
    rw [hT₀def]
    exact Finset.mem_insert_of_mem (Finset.mem_insert_of_mem
      (Finset.mem_union_left _ (Finset.mem_image.2 ⟨β, hβ, rfl⟩)))
  · intro c hc
    rcases critval_comp hc with h | h
    · rw [aeval_comp, ← hrspec _ (hf₁crit c h)]
      refine key _ ?_
      have hcrit : c ∈ crit := by
        rw [hcritdef, Multiset.mem_toFinset, mem_aroots]
        exact ⟨hd1, h⟩
      rw [hT₀def]
      exact Finset.mem_insert_of_mem (Finset.mem_insert_of_mem
        (Finset.mem_union_right _ (Finset.mem_image.2 ⟨c, hcrit, rfl⟩)))
    · rcases critval_comp h with h2 | h2
      · exfalso
        rw [hφderiv, aeval_C] at h2
        have : (B - A)⁻¹ ≠ 0 := by positivity
        exact this ((map_eq_zero_iff _ (algebraMap ℚ ℂ).injective).1 h2)
      · rw [aeval_comp, aeval_comp]
        exact hg4 _ h2

end Math2

#print axioms Math2.belyi_theorem

