/-
# Furstenberg Szemeredi
Category: Frontier Abel
Target: Frontier.furstenberg_szemeredi
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Furstenberg Szemeredi
Category: Frontier Abel
Target: Frontier.furstenberg_szemeredi
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open Filter Finset

namespace Frontier

open scoped Classical in
/-- The number of elements of `A` below `n`. -/

theorem hasAP_of_upperDensity_gt (A : Set ℕ) (k : ℕ) (hk : 0 < k)
    (hA : 1 - 1 / (2 * k) < upperDensity A) : HasAP A k := by
  classical
  set c : ℝ := 1 - 1 / (2 * k) with hc
  obtain ⟨n, hn, hbig⟩ :=
    ((frequently_lt_countUpTo hA).and_eventually (eventually_gt_atTop (2 * k))).exists
  have hkR : (0:ℝ) < k := by exact_mod_cast hk
  have hkn : k ≤ n := by omega
  have hnR : (0:ℝ) < n := by
    have : 0 < n := lt_of_le_of_lt (Nat.zero_le _) hbig
    exact_mod_cast this
  have hbigR : 2 * (k:ℝ) < n := by exact_mod_cast hbig
  set s : Finset ℕ := (Finset.range n).filter (· ∈ A) with hs
  set B : Finset ℕ := (Finset.range n).filter (fun x => x ∉ A) with hB
  have hcards : (s.card : ℝ) = (countUpTo A n : ℝ) := by simp [hs, countUpTo]
  have hsplit : s.card + B.card = n := by
    rw [hs, hB]
    simpa using Finset.card_filter_add_card_filter_not (s := Finset.range n) (p := fun x => x ∈ A)
  have h2 : c * n < (s.card : ℝ) := hcards ▸ hn
  have h1 : (B.card : ℝ) = n - s.card := by
    have : ((s.card + B.card : ℕ) : ℝ) = (n : ℝ) := by exact_mod_cast hsplit
    push_cast at this; linarith
  have hexp : c * (n:ℝ) = n - n / (2 * k) := by rw [hc]; field_simp
  have hBcard : (B.card : ℝ) < n / (2 * k) := by rw [h1]; linarith
  -- the "bad" starting points are those `a` for which some `a + i`, `i < k`, misses `A`
  set bad : Finset ℕ := (Finset.range (n - k)).filter (fun a => ∃ i < k, a + i ∉ A) with hbad
  have hsubimg : bad ⊆ (B ×ˢ Finset.range k).image (fun p => p.1 - p.2) := by
    intro a ha
    rw [hbad, Finset.mem_filter, Finset.mem_range] at ha
    obtain ⟨hlt, i, hik, hmem⟩ := ha
    refine Finset.mem_image.2 ⟨(a + i, i), ?_, by simp⟩
    refine Finset.mem_product.2 ⟨?_, Finset.mem_range.2 hik⟩
    rw [hB, Finset.mem_filter, Finset.mem_range]
    exact ⟨by omega, hmem⟩
  have hbadcard : (bad.card : ℝ) < (n : ℝ) / 2 := by
    have h3 : bad.card ≤ B.card * k := by
      calc bad.card ≤ ((B ×ˢ Finset.range k).image (fun p => p.1 - p.2)).card :=
            Finset.card_le_card hsubimg
        _ ≤ (B ×ˢ Finset.range k).card := Finset.card_image_le
        _ = B.card * k := by simp
    have h4 : (bad.card : ℝ) ≤ (B.card : ℝ) * k := by exact_mod_cast h3
    have h5 : (B.card : ℝ) * k < (n / (2 * k)) * k := mul_lt_mul_of_pos_right hBcard hkR
    have h6 : (n / (2 * (k:ℝ))) * k = n / 2 := by field_simp
    linarith
  have hrange : ((n - k : ℕ) : ℝ) > (n : ℝ) / 2 := by
    have hcast : ((n - k : ℕ) : ℝ) = (n : ℝ) - k := by
      have := Nat.cast_sub (R := ℝ) hkn
      simpa using this
    rw [hcast]; linarith
  have hex : ∃ a ∈ Finset.range (n - k), a ∉ bad := by
    by_contra hcon
    push_neg at hcon
    have hsubb : Finset.range (n - k) ⊆ bad := fun a ha => hcon a ha
    have hle := Finset.card_le_card hsubb
    rw [Finset.card_range] at hle
    have : ((n - k : ℕ) : ℝ) ≤ (bad.card : ℝ) := by exact_mod_cast hle
    linarith
  obtain ⟨a, haR, hanot⟩ := hex
  rw [hbad, Finset.mem_filter] at hanot
  push_neg at hanot
  have hgood : ∀ i < k, a + i ∈ A := by
    intro i hi
    have := hanot haR i hi
    simpa using this
  exact ⟨a, 1, one_pos, fun i hi => by simpa using hgood i hi⟩

/-! ### Sanity checks: the density hypothesis is satisfiable -/

