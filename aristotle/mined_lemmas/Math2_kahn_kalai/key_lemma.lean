import RequestProject.Basic

/-!
# Covers, smallness, and Park–Pham minimum fragments
-/

namespace Math2

open Finset

variable {X : Type*} [DecidableEq X]

/-- `W` contains an edge of the hypergraph `H`, i.e. `W ∈ ⟨H⟩`. -/

theorem key_lemma {V : Finset X} {H : Finset (Finset X)} {ℓ m₀ : ℕ} {p δ : ℝ}
    (hV : ∀ S ∈ H, S ⊆ V) (hbd : ∀ S ∈ H, S.card ≤ ℓ)
    (hp : 0 ≤ p) (hδ0 : 0 < δ) (hδ1 : δ ≤ 1) :
    Exp V δ (fun W => cost p (coverFam H W m₀))
      ≤ ∑ m ∈ Finset.Icc (m₀ + 1) ℓ, 2 ^ ℓ * (p / δ) ^ m := by
  -- split the cover by the size of its members
  have hsplit : ∀ W : Finset X,
      cost p (coverFam H W m₀)
        = ∑ m ∈ Finset.Icc (m₀ + 1) ℓ,
            ∑ U ∈ (coverFam H W m₀).filter (fun U => U.card = m), p ^ U.card := by
    intro W
    show ∑ U ∈ coverFam H W m₀, p ^ U.card = _
    refine (Finset.sum_fiberwise_of_maps_to (g := fun U : Finset X => U.card) ?_ _).symm
    intro U hU
    exact Finset.mem_Icc.mpr ⟨coverFam_card_lt hU, coverFam_card_le hbd hU⟩
  simp only [hsplit]
  rw [Exp_sum]
  refine Finset.sum_le_sum fun m hm => ?_
  -- fix `m` and bound one term
  set cm : Finset X → Finset (Finset X) :=
    fun W => (coverFam H W m₀).filter (fun U => U.card = m) with hcm
  have hcmsub : ∀ W ∈ V.powerset, cm W ⊆ V.powerset := by
    intro W _ U hU
    simp only [hcm, Finset.mem_filter] at hU
    exact Finset.mem_powerset.mpr (coverFam_subset_ground hV hU.1)
  have hstep1 : Exp V δ (fun W => ∑ U ∈ cm W, p ^ U.card)
      = ∑ W ∈ V.powerset, ∑ U ∈ cm W, wt V δ W * p ^ m := by
    unfold Exp
    refine Finset.sum_congr rfl fun W _ => ?_
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun U hU => ?_
    simp only [hcm, Finset.mem_filter] at hU
    rw [hU.2]
  rw [hstep1, sum_nested_eq V cm hcmsub (fun W U => wt V δ W * p ^ m)]
  -- pass to the sets `Z = W ∪ U`
  set P₁ := (V.powerset ×ˢ V.powerset).filter (fun x : Finset X × Finset X => x.2 ∈ cm x.1)
    with hP₁
  set P₂ := (V.powerset ×ˢ V.powerset).filter
    (fun y : Finset X × Finset X => y.2 ⊆ y.1 ∧ y.2 ∈ cm (y.1 \ y.2)) with hP₂
  have hmem₁ : ∀ x ∈ P₁, x.1 ⊆ V ∧ x.2 ∈ cm x.1 := by
    intro x hx
    simp only [hP₁, Finset.mem_filter, Finset.mem_product, Finset.mem_powerset] at hx
    exact ⟨hx.1.1, hx.2⟩
  have hstep2 : ∑ x ∈ P₁, wt V δ x.1 * p ^ m ≤ ∑ x ∈ P₁, wt V δ (x.1 ∪ x.2) * (p / δ) ^ m := by
    refine Finset.sum_le_sum fun x hx => ?_
    obtain ⟨hxV, hxcm⟩ := hmem₁ x hx
    simp only [hcm, Finset.mem_filter] at hxcm
    exact wt_le_wt_union hδ0 hδ1 hp hxV (coverFam_subset_ground hV hxcm.1)
      (coverFam_disjoint hxcm.1) hxcm.2
  have hstep3 : ∑ x ∈ P₁, wt V δ (x.1 ∪ x.2) * (p / δ) ^ m
      = ∑ y ∈ P₂, wt V δ y.1 * (p / δ) ^ m := by
    refine Finset.sum_nbij' (i := fun x : Finset X × Finset X => (x.1 ∪ x.2, x.2))
      (j := fun y : Finset X × Finset X => (y.1 \ y.2, y.2)) ?_ ?_ ?_ ?_ ?_
    · intro x hx
      obtain ⟨hxV, hxcm⟩ := hmem₁ x hx
      have hcm' := hxcm
      simp only [hcm, Finset.mem_filter] at hcm'
      have hdisj : Disjoint x.2 x.1 := coverFam_disjoint hcm'.1
      have hUV : x.2 ⊆ V := coverFam_subset_ground hV hcm'.1
      have hEq : (x.1 ∪ x.2) \ x.2 = x.1 := by
        ext y
        simp only [Finset.mem_sdiff, Finset.mem_union]
        constructor
        · rintro ⟨h1 | h1, h2⟩
          · exact h1
          · exact absurd h1 h2
        · intro h
          exact ⟨Or.inl h, fun hy => (Finset.disjoint_left.mp hdisj hy) h⟩
      simp only [hP₂, Finset.mem_filter, Finset.mem_product, Finset.mem_powerset]
      refine ⟨⟨Finset.union_subset hxV hUV, hUV⟩, Finset.subset_union_right, ?_⟩
      rw [hEq]; exact hxcm
    · intro y hy
      simp only [hP₂, Finset.mem_filter, Finset.mem_product, Finset.mem_powerset] at hy
      simp only [hP₁, Finset.mem_filter, Finset.mem_product, Finset.mem_powerset]
      exact ⟨⟨(Finset.sdiff_subset).trans hy.1.1, hy.1.2⟩, hy.2.2⟩
    · intro x hx
      obtain ⟨_, hxcm⟩ := hmem₁ x hx
      simp only [hcm, Finset.mem_filter] at hxcm
      have hdisj : Disjoint x.2 x.1 := coverFam_disjoint hxcm.1
      have hEq : (x.1 ∪ x.2) \ x.2 = x.1 := by
        ext y
        simp only [Finset.mem_sdiff, Finset.mem_union]
        constructor
        · rintro ⟨h1 | h1, h2⟩
          · exact h1
          · exact absurd h1 h2
        · intro h
          exact ⟨Or.inl h, fun hy => (Finset.disjoint_left.mp hdisj hy) h⟩
      simp [hEq]
    · intro y hy
      simp only [hP₂, Finset.mem_filter, Finset.mem_product, Finset.mem_powerset] at hy
      have : (y.1 \ y.2) ∪ y.2 = y.1 := Finset.sdiff_union_of_subset hy.2.1
      simp [this]
    · intro x _
      rfl
  -- now bound the sum over `P₂`
  have hstep4 : ∑ y ∈ P₂, wt V δ y.1 * (p / δ) ^ m
      ≤ ∑ Z ∈ V.powerset, ∑ U ∈ (pick H Z).powerset, wt V δ Z * (p / δ) ^ m := by
    have hP₂eq : ∑ y ∈ P₂, wt V δ y.1 * (p / δ) ^ m
        = ∑ Z ∈ V.powerset, ∑ U ∈ V.powerset.filter
            (fun U => U ⊆ Z ∧ U ∈ cm (Z \ U)), wt V δ Z * (p / δ) ^ m := by
      rw [hP₂, Finset.sum_filter, Finset.sum_product]
      refine Finset.sum_congr rfl fun Z _ => ?_
      rw [Finset.sum_filter]
    rw [hP₂eq]
    refine Finset.sum_le_sum fun Z hZ => ?_
    refine Finset.sum_le_sum_of_subset_of_nonneg ?_ ?_
    · intro U hU
      simp only [Finset.mem_filter, Finset.mem_powerset] at hU ⊢
      obtain ⟨_, hUZ, hUcm⟩ := hU
      simp only [hcm, Finset.mem_filter] at hUcm
      have hsub : U ⊆ pick H ((Z \ U) ∪ U) := coverFam_subset_pick hUcm.1
      rwa [Finset.sdiff_union_of_subset hUZ] at hsub
    · intro U _ _
      have : (0:ℝ) ≤ wt V δ Z := wt_nonneg (le_of_lt hδ0) hδ1 Z
      have h2 : (0:ℝ) ≤ (p / δ) ^ m := by positivity
      positivity
  refine le_trans hstep2 (le_trans (le_of_eq hstep3) (le_trans hstep4 ?_))
  -- finally: each fiber has at most `2 ^ ℓ` elements
  have hfin : ∀ Z ∈ V.powerset,
      ∑ U ∈ (pick H Z).powerset, wt V δ Z * (p / δ) ^ m
        ≤ 2 ^ ℓ * ((p / δ) ^ m * wt V δ Z) := by
    intro Z _
    rw [Finset.sum_const, Finset.card_powerset, nsmul_eq_mul]
    push_cast
    have hcard : ((2:ℝ) ^ (pick H Z).card) ≤ 2 ^ ℓ := by
      apply pow_le_pow_right₀ (by norm_num)
      exact pick_card_le hbd Z
    have hnn : (0:ℝ) ≤ wt V δ Z * (p / δ) ^ m := by
      have := wt_nonneg (le_of_lt hδ0) hδ1 (V := V) (p := δ) Z
      have h2 : (0:ℝ) ≤ (p / δ) ^ m := by positivity
      positivity
    calc ((2:ℝ) ^ (pick H Z).card) * (wt V δ Z * (p / δ) ^ m)
        ≤ 2 ^ ℓ * (wt V δ Z * (p / δ) ^ m) := by
          exact mul_le_mul_of_nonneg_right hcard hnn
      _ = 2 ^ ℓ * ((p / δ) ^ m * wt V δ Z) := by ring
  calc ∑ Z ∈ V.powerset, ∑ U ∈ (pick H Z).powerset, wt V δ Z * (p / δ) ^ m
      ≤ ∑ Z ∈ V.powerset, 2 ^ ℓ * ((p / δ) ^ m * wt V δ Z) := Finset.sum_le_sum hfin
    _ = 2 ^ ℓ * (p / δ) ^ m := by
        rw [← Finset.mul_sum, ← Finset.mul_sum, sum_wt, mul_one]

end Math2

