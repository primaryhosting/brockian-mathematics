import Mathlib

/-!
# Additive monotone functions on an interval are linear

An elementary Cauchy-functional-equation argument: a nonnegative function on `[0, π]` which is
additive there is determined by its value at `π`.
-/

open scoped Real

namespace Math

variable {W : ℝ → ℝ}

/-- An additive nonnegative function is monotone. -/

lemma Wfun_add {θ₁ θ₂ : ℝ} (h1 : 0 < θ₁) (h2 : 0 < θ₂) (h : θ₁ + θ₂ ≤ π) :
    Wfun (θ₁ + θ₂) = Wfun θ₁ + Wfun θ₂ := by
  set A := HS (dirv e₀ f₀ (0 + π / 2)) ∩ HS (dirv e₀ f₀ (θ₁ - π / 2)) with hA
  set B := HS (dirv e₀ f₀ (θ₁ + π / 2)) ∩ HS (dirv e₀ f₀ (θ₁ + θ₂ - π / 2)) with hB
  set C := HS (dirv e₀ f₀ (0 + π / 2)) ∩ HS (dirv e₀ f₀ (θ₁ + θ₂ - π / 2)) with hC
  have hAC : A ⊆ C := by
    rintro x ⟨hx1, hx2⟩
    refine ⟨hx1, ?_⟩
    have := HS_dirv_between (e := e₀) (f := f₀) (a := θ₁ - π / 2) (b := 0 + π / 2)
      (c := θ₁ + θ₂ - π / 2) (by linarith) (by linarith) (by linarith)
    exact this ⟨hx2, hx1⟩
  have hBC : B ⊆ C := by
    rintro x ⟨hx1, hx2⟩
    refine ⟨?_, hx2⟩
    have := HS_dirv_between (e := e₀) (f := f₀) (a := θ₁ + θ₂ - π / 2) (b := θ₁ + π / 2)
      (c := 0 + π / 2) (by linarith) (by linarith) (by linarith)
    exact this ⟨hx2, hx1⟩
  have hflip : dirv e₀ f₀ (θ₁ + π / 2) = -dirv e₀ f₀ (θ₁ - π / 2) := by
    rw [← dirv_add_pi]
    ring_nf
  have hunion : A ∪ B = C := by
    refine Set.Subset.antisymm (Set.union_subset hAC hBC) ?_
    rintro x ⟨hx1, hx2⟩
    rcases le_or_gt 0 (⟪x, dirv e₀ f₀ (θ₁ - π / 2)⟫ : ℝ) with hpos | hneg
    · exact Or.inl ⟨hx1, hpos⟩
    · refine Or.inr ⟨?_, hx2⟩
      simp only [mem_HS, hflip, inner_neg_right]
      linarith
  have hnull : volume (A ∩ B) = 0 := by
    refine measure_mono_null ?_
      (hyperplane_null (dirv_ne_zero norm_e₀ norm_f₀ inner_e₀_f₀ (θ₁ - π / 2)))
    rintro x ⟨⟨-, hxa⟩, ⟨hxb, -⟩⟩
    simp only [mem_HS, hflip, inner_neg_right] at hxa hxb
    exact le_antisymm (by linarith) hxa
  have hmeasB : MeasurableSet B :=
    (measurableSet_HS _).inter (measurableSet_HS _)
  have hsum : bvol C = bvol A + bvol B := by
    rw [← hunion]
    exact bvol_union A B hmeasB hnull
  have eA : bvol A = Wfun θ₁ := by
    have := wvol_dirv_eq_Wfun norm_e₀ norm_f₀ inner_e₀_f₀ 0 θ₁
    rw [sub_zero] at this
    exact this
  have eB : bvol B = Wfun θ₂ := by
    have := wvol_dirv_eq_Wfun norm_e₀ norm_f₀ inner_e₀_f₀ θ₁ (θ₁ + θ₂)
    rw [show θ₁ + θ₂ - θ₁ = θ₂ by ring] at this
    exact this
  have eC : bvol C = Wfun (θ₁ + θ₂) := by
    have := wvol_dirv_eq_Wfun norm_e₀ norm_f₀ inner_e₀_f₀ 0 (θ₁ + θ₂)
    rw [sub_zero] at this
    exact this
  rw [← eA, ← eB, ← eC, hsum]

