/-
# Pcp Pigeon Bound
Category: Computer Science
Target: CS.pcp_pigeon_bound
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

namespace CS

open Finset

/-- The finite set of all binary strings of length `n`. -/

theorem kraft_nat {S : Finset (List Bool)} (hS : PrefixFree S) {n : ℕ}
    (hn : ∀ w ∈ S, w.length ≤ n) :
    ∑ w ∈ S, 2 ^ (n - w.length) ≤ 2 ^ n := by
  classical
  -- the length-`n` extensions of a codeword `w`
  set F : List Bool → Finset (List Bool) := fun w => (binWords (n - w.length)).image (w ++ ·)
    with hF
  have hcard : ∀ w ∈ S, (F w).card = 2 ^ (n - w.length) := by
    intro w _
    rw [hF]
    simp only
    rw [Finset.card_image_of_injective _ (List.append_right_injective w), card_binWords]
  have hdisj : (S : Set (List Bool)).PairwiseDisjoint F := by
    intro w hw v hv hne
    simp only [Function.onFun]
    rw [Finset.disjoint_left]
    rintro l hlw hlv
    simp only [hF, Finset.mem_image] at hlw hlv
    obtain ⟨t, -, rfl⟩ := hlw
    obtain ⟨t', -, ht'⟩ := hlv
    have hwp : w <+: w ++ t := ⟨t, rfl⟩
    have hvp : v <+: w ++ t := ⟨t', ht'⟩
    rcases le_total w.length v.length with h | h
    · exact hne (hS w hw v hv (List.prefix_of_prefix_length_le hwp hvp h))
    · exact hne (hS v hv w hw (List.prefix_of_prefix_length_le hvp hwp h)).symm
  have hsub : S.biUnion F ⊆ binWords n := by
    intro l hl
    simp only [Finset.mem_biUnion] at hl
    obtain ⟨w, hw, hlw⟩ := hl
    simp only [hF, Finset.mem_image] at hlw
    obtain ⟨t, ht, rfl⟩ := hlw
    have hwn := hn w hw
    rw [mem_binWords] at ht ⊢
    simp only [List.length_append, ht]
    omega
  calc ∑ w ∈ S, 2 ^ (n - w.length) = ∑ w ∈ S, (F w).card := (Finset.sum_congr rfl hcard).symm
    _ = (S.biUnion F).card := (Finset.card_biUnion (fun x hx y hy hxy =>
          hdisj hx hy hxy)).symm
    _ ≤ (binWords n).card := Finset.card_le_card hsub
    _ = 2 ^ n := card_binWords n

/-- **Kraft's inequality**: any prefix-free binary code satisfies `∑ᵢ 2 ^ (-ℓᵢ) ≤ 1`,
where `ℓᵢ` are the lengths of the codewords. -/
