import Mathlib
open Finset Matrix
namespace Frontier.Sensitivity

/-- Vertices of the n-dimensional Boolean hypercube. -/
abbrev Q (n : ℕ) := Fin n → Bool

/-- Two vertices are adjacent iff they differ in exactly one coordinate. -/

lemma sgnAdj_mul_self {n : ℕ} :
    (sgnAdj (n := n)) * (sgnAdj (n := n)) = (n : ℝ) • (1 : Matrix (Q n) (Q n) ℝ) := by
  ext u w
  rw [Matrix.mul_apply]
  have hstep1 : ∑ v : Q n, sgnAdj u v * sgnAdj v w
      = ∑ v ∈ Finset.image (fun k : Fin n => flipAt k u) Finset.univ, sgnAdj u v * sgnAdj v w := by
    refine (Finset.sum_subset (Finset.subset_univ _) ?_).symm
    intro v _ hv
    have h : ∀ k : Fin n, v ≠ flipAt k u := by
      intro k hk
      exact hv (Finset.mem_image.2 ⟨k, Finset.mem_univ k, hk.symm⟩)
    rw [sgnAdj_eq_zero_of_forall h, zero_mul]
  have hstep2 : ∑ v ∈ Finset.image (fun k : Fin n => flipAt k u) Finset.univ,
      sgnAdj u v * sgnAdj v w
      = ∑ k : Fin n, eps u k * sgnAdj (flipAt k u) w := by
    rw [Finset.sum_image (by intro a _ b _ h; exact flipAt_inj h)]
    exact Finset.sum_congr rfl fun k _ => by rw [sgnAdj_apply_flipAt]
  rw [hstep1, hstep2]
  set F : Fin n × Fin n → ℝ := fun p =>
    if w = flipAt p.2 (flipAt p.1 u) then eps u p.1 * eps (flipAt p.1 u) p.2 else 0 with hF
  have hexp : ∑ k : Fin n, eps u k * sgnAdj (flipAt k u) w
      = ∑ p ∈ (Finset.univ : Finset (Fin n)) ×ˢ (Finset.univ : Finset (Fin n)), F p := by
    rw [Finset.sum_product]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [sgnAdj]
    simp only [Matrix.of_apply, Finset.mul_sum, hF]
    refine Finset.sum_congr rfl fun l _ => ?_
    split_ifs <;> simp
  rw [hexp, ← Finset.diag_union_offDiag, Finset.sum_union (Finset.disjoint_diag_offDiag _),
    Finset.sum_diag]
  have hoff : ∑ p ∈ (Finset.univ : Finset (Fin n)).offDiag, F p = 0 := by
    refine Finset.sum_involution (fun p _ => (p.2, p.1)) ?_ ?_ ?_ ?_
    · rintro ⟨k, l⟩ hp
      simp only [Finset.mem_offDiag] at hp
      have hkl : k ≠ l := hp.2.2
      simp only [hF]
      rw [flipAt_comm l k u]
      rcases lt_or_gt_of_ne hkl with h | h
      · rw [eps_flipAt_of_lt u h, eps_flipAt_of_le u (le_of_lt h)]
        split_ifs <;> ring
      · rw [eps_flipAt_of_lt u h, eps_flipAt_of_le u (le_of_lt h)]
        split_ifs <;> ring
    · rintro ⟨k, l⟩ hp _
      simp only [Finset.mem_offDiag] at hp
      simp only [ne_eq, Prod.mk.injEq, not_and]
      intro h
      exact absurd h.symm hp.2.2
    · rintro ⟨k, l⟩ hp
      simp only [Finset.mem_offDiag] at hp ⊢
      exact ⟨hp.2.1, hp.1, hp.2.2.symm⟩
    · rintro ⟨k, l⟩ _; rfl
  rw [hoff, add_zero]
  have hdiag : ∀ k : Fin n, F (k, k) = if w = u then (1 : ℝ) else 0 := by
    intro k
    simp only [hF, flipAt_flipAt, eps_flipAt_of_le u (le_refl k), eps_mul_self]
  simp only [hdiag, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul,
    Matrix.smul_apply, Matrix.one_apply, smul_eq_mul]
  split_ifs with h1 h2 h2
  · ring
  · exact absurd h1.symm h2
  · exact absurd h2.symm h1
  · ring

/-! ### Linear algebra -/

