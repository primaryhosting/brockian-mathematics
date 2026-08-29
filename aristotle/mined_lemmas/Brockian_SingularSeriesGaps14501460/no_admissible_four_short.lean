import Mathlib

/-!
# Singular Series Gaps 14501460
Category: Brockian Corpus
Target: Brockian.SingularSeriesGaps14501460
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open scoped BigOperators

set_option maxHeartbeats 4000000
set_option maxRecDepth 10000

namespace Brockian

/-- The gap window: the integers of the range `[1450, 1460]`. -/

lemma no_admissible_four_short (K : Finset ℤ) (c : ℤ)
    (hsub : K ⊆ Finset.Icc c (c + 6)) (hcard : K.card = 4) : ¬ Admissible K := by
  intro hadm
  obtain ⟨r2, hr2⟩ := hadm 2 Nat.prime_two
  have hsame : ∀ h₁ ∈ K, ∀ h₂ ∈ K, (2:ℤ) ∣ (h₁ - h₂) := by
    intro h₁ hh₁ h₂ hh₂
    have d : ∀ z x y : ZMod 2, x ≠ z → y ≠ z → x = y := by decide
    have e : ((h₁ : ℤ) : ZMod 2) = ((h₂ : ℤ) : ZMod 2) := d r2 _ _ (hr2 _ hh₁) (hr2 _ hh₂)
    have hmod := (ZMod.intCast_eq_intCast_iff h₁ h₂ 2).mp e
    have := Int.ModEq.dvd hmod.symm
    exact_mod_cast this
  by_cases hall : ∀ h ∈ K, (2:ℤ) ∣ (h - c)
  · have hsubT : K ⊆ Finset.image (fun j => c + j) ({0, 2, 4, 6} : Finset ℤ) := by
      intro h hh
      have hb := Finset.mem_Icc.mp (hsub hh)
      have hd := hall h hh
      simp only [Finset.mem_image, Finset.mem_insert, Finset.mem_singleton]
      exact ⟨h - c, by omega, by ring⟩
    have hTcard : (Finset.image (fun j => c + j) ({0, 2, 4, 6} : Finset ℤ)).card = 4 := by
      rw [Finset.card_image_of_injective _ (add_right_injective c)]
      decide
    have hKT : K = Finset.image (fun j => c + j) ({0, 2, 4, 6} : Finset ℤ) :=
      Finset.eq_of_subset_of_card_le hsubT (by rw [hTcard, hcard])
    obtain ⟨r3, hr3⟩ := hadm 3 (by norm_num)
    have hex : ∀ x : ZMod 3, ∃ j ∈ ({0, 2, 4, 6} : Finset ℤ), ((c + j : ℤ) : ZMod 3) = x := by
      intro x
      have h3 : ∀ z : ZMod 3, z = 0 ∨ z = 1 ∨ z = 2 := by decide
      rcases h3 (x - ((c : ℤ) : ZMod 3)) with h | h | h
      · refine ⟨0, by decide, ?_⟩
        have hx : x = ((c : ℤ) : ZMod 3) := by linear_combination h
        push_cast
        rw [hx]; ring
      · refine ⟨4, by decide, ?_⟩
        have hx : x = ((c : ℤ) : ZMod 3) + 1 := by linear_combination h
        have h4 : (4 : ZMod 3) = 1 := by decide
        push_cast
        rw [hx, h4]
      · refine ⟨2, by decide, ?_⟩
        have hx : x = ((c : ℤ) : ZMod 3) + 2 := by linear_combination h
        push_cast
        rw [hx]
    obtain ⟨j, hj, hjx⟩ := hex r3
    have hmem : (c + j) ∈ K := by
      rw [hKT]; exact Finset.mem_image_of_mem _ hj
    exact hr3 _ hmem hjx
  · push_neg at hall
    obtain ⟨h₀, hh₀, hodd⟩ := hall
    have hsub3 : K ⊆ Finset.image (fun j => c + j) ({1, 3, 5} : Finset ℤ) := by
      intro h hh
      have hb := Finset.mem_Icc.mp (hsub hh)
      have hd := hsame h hh h₀ hh₀
      have hb0 := Finset.mem_Icc.mp (hsub hh₀)
      simp only [Finset.mem_image, Finset.mem_insert, Finset.mem_singleton]
      exact ⟨h - c, by omega, by ring⟩
    have hle := Finset.card_le_card hsub3
    have h3 : (Finset.image (fun j => c + j) ({1, 3, 5} : Finset ℤ)).card ≤ 3 :=
      le_trans Finset.card_image_le (by decide)
    omega

/-! ## Main theorem -/

/-- **Singular series gaps, window `[1450, 1460]`.**
The four integers of the range `1450 … 1460` that are coprime to `210` form an admissible
4-tuple of diameter `8` (the least possible diameter for an admissible 4-tuple), and the
associated Hardy–Littlewood singular series has strictly positive partial products which
converge to a strictly positive limit. -/
