/-
# Mordell Finite Generation
Category: Frontier — Prime Numbers
Target: Frontier.Mordell_finite_generation
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

open scoped Classical

namespace Frontier

/-! ## The multiplication-by-`m` subgroup and its quotient -/

/-- Multiplication by `m` as an endomorphism of an additive commutative group. -/

theorem descent_theorem {A : Type*} [AddCommGroup A] (m : ℕ) (hm : 2 ≤ m) (h : A → ℝ)
    (H1 : ∀ Q : A, ∃ C : ℝ, ∀ P : A, h (P + Q) ≤ 2 * h P + C)
    (H2 : ∃ C : ℝ, ∀ P : A, (m : ℝ) ^ 2 * h P ≤ h (m • P) + C)
    (H3 : ∀ C : ℝ, {P : A | h P ≤ C}.Finite)
    [Finite (A ⧸ smulSubgroup m A)] : AddGroup.FG A := by
  classical
  obtain ⟨S, hS⟩ := exists_finset_reps (smulSubgroup m A)
  -- reformulate the coset representatives
  have hS' : ∀ P : A, ∃ Q ∈ S, ∃ P' : A, P = m • P' + Q := by
    intro P
    obtain ⟨Q, hQ, hmem⟩ := hS P
    obtain ⟨P', hP'⟩ := hmem
    exact ⟨Q, hQ, P', by rw [nsmulHom_apply] at hP'; rw [hP']; abel⟩
  -- a uniform constant for `H1` over the (finitely many) representatives
  obtain ⟨C₂, hC₂⟩ := H2
  set f : A → ℝ := fun Q => Classical.choose (H1 (-Q)) with hf
  have hfspec : ∀ Q : A, ∀ P : A, h (P + -Q) ≤ 2 * h P + f Q :=
    fun Q => Classical.choose_spec (H1 (-Q))
  set c₁ : ℝ := (insert (0 : ℝ) (S.image f)).max' ⟨0, Finset.mem_insert_self _ _⟩ with hc₁
  have hc₁le : ∀ Q ∈ S, f Q ≤ c₁ := by
    intro Q hQ
    exact Finset.le_max' _ _ (Finset.mem_insert_of_mem (Finset.mem_image_of_mem _ hQ))
  set c : ℝ := c₁ + C₂ with hc
  -- the basic descent inequality
  have key : ∀ P : A, ∀ Q ∈ S, ∀ P' : A, P = m • P' + Q →
      (m : ℝ) ^ 2 * h P' ≤ 2 * h P + c := by
    intro P Q hQ P' hP'
    have h1 : (m : ℝ) ^ 2 * h P' ≤ h (m • P') + C₂ := hC₂ P'
    have h2 : m • P' = P + -Q := by rw [hP']; abel
    have h3 : h (P + -Q) ≤ 2 * h P + f Q := hfspec Q P
    have h4 : f Q ≤ c₁ := hc₁le Q hQ
    rw [h2] at h1
    linarith
  have hm2 : (2 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm
  have hmsq : (4 : ℝ) ≤ (m : ℝ) ^ 2 := by nlinarith
  have hmpos : (0 : ℝ) < (m : ℝ) ^ 2 := by linarith
  set T : ℝ := c / ((m : ℝ) ^ 2 - 2) with hT
  -- the generating set
  set K : AddSubgroup A := AddSubgroup.closure ((S : Set A) ∪ {P : A | h P ≤ T}) with hK
  have hsmall : ∀ P : A, h P ≤ T → P ∈ K := by
    intro P hP
    exact AddSubgroup.subset_closure (Or.inr hP)
  have hSK : ∀ Q ∈ S, Q ∈ K := by
    intro Q hQ
    exact AddSubgroup.subset_closure (Or.inl hQ)
  have htop : K = ⊤ := by
    by_contra hne
    obtain ⟨P₀, hP₀⟩ : ∃ P₀ : A, P₀ ∉ K := by
      by_contra hall
      push_neg at hall
      exact hne (eq_top_iff.mpr fun x _ => hall x)
    set F : Set A := {x : A | x ∉ K ∧ h x ≤ h P₀} with hF
    have hFfin : F.Finite := (H3 (h P₀)).subset (fun x hx => hx.2)
    have hFne : F.Nonempty := ⟨P₀, hP₀, le_rfl⟩
    obtain ⟨x, hxF, hxmin⟩ := Set.exists_min_image F h hFfin hFne
    have hxK : x ∉ K := hxF.1
    have hxT : T < h x := by
      by_contra hle
      push_neg at hle
      exact hxK (hsmall x hle)
    obtain ⟨Q, hQ, x', hx'⟩ := hS' x
    have hx'K : x' ∉ K := by
      intro hmem
      apply hxK
      rw [hx']
      exact AddSubgroup.add_mem _ (AddSubgroup.nsmul_mem _ hmem _) (hSK Q hQ)
    have hkey : (m : ℝ) ^ 2 * h x' ≤ 2 * h x + c := key x Q hQ x' hx'
    have hcx : c < ((m : ℝ) ^ 2 - 2) * h x := by
      have hpos : (0 : ℝ) < (m : ℝ) ^ 2 - 2 := by linarith
      rw [hT, div_lt_iff₀ hpos] at hxT
      linarith
    have hlt : h x' < h x := by nlinarith
    have hx'F : x' ∈ F := ⟨hx'K, le_trans hlt.le hxF.2⟩
    exact absurd (hxmin x' hx'F) (not_le.mpr hlt)
  refine AddGroup.fg_iff.mpr ⟨(S : Set A) ∪ {P : A | h P ≤ T}, htop, ?_⟩
  exact (S.finite_toSet).union (H3 T)

/-! ## The Mordell–Weil theorem for elliptic curves over `ℚ` -/

/-- The full statement of the Mordell–Weil theorem over `ℚ`: for every elliptic curve `E`
over `ℚ`, the group `E(ℚ)` of rational points is finitely generated. -/
