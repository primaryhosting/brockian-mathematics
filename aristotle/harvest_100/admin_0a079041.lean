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
noncomputable def binWords (n : ℕ) : Finset (List Bool) :=
  (Finset.univ : Finset (Fin n → Bool)).image List.ofFn

lemma mem_binWords {n : ℕ} {l : List Bool} : l ∈ binWords n ↔ l.length = n := by
  constructor
  · rintro h
    simp only [binWords, Finset.mem_image] at h
    obtain ⟨f, -, rfl⟩ := h
    simp
  · rintro rfl
    simp only [binWords, Finset.mem_image, Finset.mem_univ, true_and]
    exact ⟨fun i => l[(i : ℕ)], List.ofFn_getElem l⟩

lemma card_binWords (n : ℕ) : (binWords n).card = 2 ^ n := by
  rw [binWords, Finset.card_image_of_injective _ List.ofFn_injective]
  simp

/-- A finite set of binary strings is *prefix-free* if no member is a prefix of a
different member. -/
def PrefixFree (S : Finset (List Bool)) : Prop :=
  ∀ w ∈ S, ∀ v ∈ S, w <+: v → w = v

/-- Counting form of Kraft's inequality: if all codewords of a prefix-free code have
length at most `n`, then `∑ 2 ^ (n - ℓ i) ≤ 2 ^ n`, by a pigeonhole/counting argument
on the length-`n` extensions of the codewords. -/
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
theorem pcp_pigeon_bound (S : Finset (List Bool)) (hS : PrefixFree S) :
    ∑ w ∈ S, (2 : ℝ) ^ (-(w.length : ℤ)) ≤ 1 := by
  classical
  set n := S.sup List.length with hn
  have hle : ∀ w ∈ S, w.length ≤ n := fun w hw => Finset.le_sup (f := List.length) hw
  have key := kraft_nat hS hle
  have hpos : (0 : ℝ) < 2 ^ n := by positivity
  have hterm : ∀ w ∈ S, (2 : ℝ) ^ (-(w.length : ℤ))
      = (2 : ℝ) ^ (n - w.length) / (2 : ℝ) ^ n := by
    intro w hw
    have h := hle w hw
    rw [eq_div_iff (ne_of_gt hpos), ← zpow_natCast (2 : ℝ) (n - w.length),
      ← zpow_natCast (2 : ℝ) n, ← zpow_add₀ (two_ne_zero : (2 : ℝ) ≠ 0)]
    congr 1
    omega
  rw [Finset.sum_congr rfl hterm, ← Finset.sum_div, div_le_one hpos]
  exact_mod_cast key

end CS

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

