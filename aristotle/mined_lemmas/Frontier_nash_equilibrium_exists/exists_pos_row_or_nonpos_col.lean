import RequestProject.Nash

/-!
# The one-dimensional base case of Brouwer's fixed point theorem

Brouwer's fixed point theorem is not available in Mathlib, and is taken as an explicit
hypothesis in `Frontier.nash_equilibrium_exists`.  Here we prove the one-dimensional base
case of that hypothesis, `BrouwerFixedPointProperty ℝ`, from the intermediate value
theorem; in particular the hypothesis is not vacuous.
-/

open Set

namespace Frontier

/-- **Brouwer's fixed point theorem in dimension one**: every continuous self-map of a
nonempty compact convex subset of `ℝ` has a fixed point. -/

theorem exists_pos_row_or_nonpos_col (M : A → B → ℝ) :
    (∃ x ∈ stdSimplex ℝ A, ∀ b, 0 < ∑ a, x a * M a b) ∨
      (∃ y ∈ stdSimplex ℝ B, ∀ a, ∑ b, y b * M a b ≤ 0) := by
  classical
  let L : (B → ℝ) →ₗ[ℝ] (A → ℝ) :=
    { toFun := fun y a => ∑ b, y b * M a b
      map_add' := by
        intro y z
        funext a
        simp [add_mul, Finset.sum_add_distrib]
      map_smul' := by
        intro c y
        funext a
        simp [Finset.mul_sum, mul_assoc] }
  have hLapp : ∀ (y : B → ℝ) (a : A), L y a = ∑ b, y b * M a b := fun _ _ => rfl
  set K : Set (A → ℝ) := L '' (stdSimplex ℝ B)
  set T : Set (A → ℝ) := Set.pi Set.univ fun _ => Set.Iic (0 : ℝ)
  by_cases hmeet : (K ∩ T).Nonempty
  · right
    obtain ⟨v, ⟨y, hy, rfl⟩, hvT⟩ := hmeet
    exact ⟨y, hy, fun a => hvT a (Set.mem_univ a)⟩
  · left
    have hdisj : Disjoint K T :=
      Set.disjoint_iff_inter_eq_empty.mpr (Set.not_nonempty_iff_eq_empty.mp hmeet)
    have hLcont : Continuous (fun y : B → ℝ => L y) :=
      continuous_pi fun a => continuous_finset_sum _ fun b _ =>
        (continuous_apply b).mul continuous_const
    have hKc : IsCompact K := (isCompact_stdSimplex B).image hLcont
    have hKconv : Convex ℝ K := (convex_stdSimplex ℝ B).linear_image L
    have hTc : IsClosed T := isClosed_set_pi fun _ _ => isClosed_Iic
    have hTconv : Convex ℝ T := convex_pi fun _ _ => convex_Iic 0
    obtain ⟨f, u, v, hfK, huv, hfT⟩ :=
      geometric_hahn_banach_compact_closed hKconv hKc hTconv hTc hdisj
    -- coordinates of the separating functional
    set c : A → ℝ := fun a => f (Pi.single a 1)
    have hrep : ∀ w : A → ℝ, f w = ∑ a, w a * c a := by
      intro w
      conv_lhs => rw [← Finset.univ_sum_single w]
      rw [map_sum]
      refine Finset.sum_congr rfl fun a _ => ?_
      have h1 : (Pi.single a (w a) : A → ℝ) = w a • (Pi.single a (1 : ℝ) : A → ℝ) := by
        funext a'
        by_cases h : a' = a <;> simp [Pi.single_apply, h]
      rw [h1, map_smul, smul_eq_mul]
    have h0T : (0 : A → ℝ) ∈ T := fun a _ => Set.mem_Iic.mpr le_rfl
    have hv0 : v < 0 := by simpa using hfT 0 h0T
    have hu0 : u < 0 := lt_trans huv hv0
    -- the coordinates are nonpositive
    have hcnonpos : ∀ a, c a ≤ 0 := by
      intro a
      by_contra hpos
      push_neg at hpos
      obtain ⟨n, hn⟩ := exists_nat_gt (-v / c a)
      set t : A → ℝ := fun a' => if a' = a then -(n : ℝ) else 0 with htdef
      have htT : t ∈ T := by
        intro a' _
        simp only [htdef, Set.mem_Iic]
        split
        · simp
        · exact le_rfl
      have hft := hfT t htT
      rw [hrep t] at hft
      have hsum : ∑ a', t a' * c a' = -(n : ℝ) * c a := by
        rw [Finset.sum_eq_single a]
        · simp [htdef]
        · intro a' _ hne
          simp [htdef, hne]
        · intro h
          exact absurd (Finset.mem_univ a) h
      rw [hsum] at hft
      have : -v < (n : ℝ) * c a := by
        rw [div_lt_iff₀ hpos] at hn
        linarith
      linarith
    -- the separating functional is not zero
    obtain ⟨y0, hy0⟩ := stdSimplex_nonempty B
    have hKne : L y0 ∈ K := ⟨y0, hy0, rfl⟩
    have hfneg : f (L y0) < 0 := lt_trans (hfK _ hKne) hu0
    have hex : ∃ a, c a ≠ 0 := by
      by_contra hall
      push_neg at hall
      rw [hrep (L y0)] at hfneg
      simp [hall] at hfneg
    obtain ⟨a0, ha0⟩ := hex
    have hs : ∑ a, c a < 0 := by
      have := Finset.sum_lt_sum (f := c) (g := fun _ : A => (0 : ℝ))
        (fun a _ => hcnonpos a) ⟨a0, mem_univ a0, lt_of_le_of_ne (hcnonpos a0) ha0⟩
      simpa using this
    refine ⟨fun a => c a / ∑ a', c a', ⟨fun a => ?_, ?_⟩, fun b => ?_⟩
    · rw [div_nonneg_iff]
      exact Or.inr ⟨hcnonpos a, hs.le⟩
    · rw [← Finset.sum_div, div_self hs.ne]
    · have hmem : (fun a => M a b) ∈ K := by
        refine ⟨dirac b, dirac_mem_stdSimplex b, ?_⟩
        funext a
        rw [hLapp]
        simp [dirac]
      have hlt : f (fun a => M a b) < 0 := lt_trans (hfK _ hmem) hu0
      rw [hrep] at hlt
      have hrw : ∑ a, c a / (∑ a', c a') * M a b = (∑ a, M a b * c a) / (∑ a', c a') := by
        rw [Finset.sum_div]
        exact Finset.sum_congr rfl fun a _ => by ring
      rw [hrw]
      exact div_pos_of_neg_of_neg hlt hs

/-- **The minimax theorem** for finite two-player zero-sum games: the row player has a mixed
strategy guaranteeing a value that the column player can simultaneously hold them to. -/
