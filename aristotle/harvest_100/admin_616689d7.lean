/-
# Pcp Pigeon Bound
Category: Computer Science
Target: CS.pcp_pigeon_bound
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

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

set_option grind.warning false

namespace CS

/-- The finite set of all boolean lists of a given length. -/
def boolLists (k : ℕ) : Finset (List Bool) :=
  Finset.image Subtype.val (Finset.univ : Finset (List.Vector Bool k))

lemma mem_boolLists {k : ℕ} {l : List Bool} : l ∈ boolLists k ↔ l.length = k := by
  constructor
  · rintro h
    simp only [boolLists, Finset.mem_image, Finset.mem_univ, true_and] at h
    obtain ⟨v, hv⟩ := h
    rw [← hv]
    exact v.2
  · intro h
    simp only [boolLists, Finset.mem_image, Finset.mem_univ, true_and]
    exact ⟨⟨l, h⟩, rfl⟩

lemma card_boolLists (k : ℕ) : (boolLists k).card = 2 ^ k := by
  have h : (Finset.univ : Finset (List.Vector Bool k)).card = 2 ^ k := by
    rw [Finset.card_univ, card_vector]; simp
  rw [boolLists, Finset.card_image_of_injective _ Subtype.val_injective, h]

/-- The set of length-`n` extensions of a word `w`. -/
def extensions (n : ℕ) (w : List Bool) : Finset (List Bool) :=
  Finset.image (fun y => w ++ y) (boolLists (n - w.length))

lemma card_extensions (n : ℕ) (w : List Bool) :
    (extensions n w).card = 2 ^ (n - w.length) := by
  rw [extensions, Finset.card_image_of_injective _ (fun a b h => by
    simpa using (List.append_cancel_left h)), card_boolLists]

lemma extensions_subset {n : ℕ} {w : List Bool} (h : w.length ≤ n) :
    extensions n w ⊆ boolLists n := by
  intro x hx
  simp only [extensions, Finset.mem_image] at hx
  obtain ⟨y, hy, rfl⟩ := hx
  rw [mem_boolLists] at hy ⊢
  simp [hy]
  omega

lemma prefix_of_mem_extensions {n : ℕ} {w x : List Bool} (hx : x ∈ extensions n w) :
    w <+: x := by
  simp only [extensions, Finset.mem_image] at hx
  obtain ⟨y, _, rfl⟩ := hx
  exact ⟨y, rfl⟩

/-- **Kraft's inequality**: any prefix-free binary code (a finite set `S` of binary words
such that no word of `S` is a proper prefix of another word of `S`) satisfies
`∑ w ∈ S, 2 ^ (-|w|) ≤ 1`. -/
theorem pcp_pigeon_bound (S : Finset (List Bool))
    (hpf : ∀ u ∈ S, ∀ v ∈ S, u <+: v → u = v) :
    ∑ w ∈ S, (2 : ℝ) ^ (-(w.length : ℤ)) ≤ 1 := by
  set n := S.sup List.length with hn
  have hlen : ∀ w ∈ S, w.length ≤ n := fun w hw => Finset.le_sup (f := List.length) hw
  -- disjointness of the extension families
  have hdisj : (S : Set (List Bool)).PairwiseDisjoint (extensions n) := by
    intro u hu v hv huv
    simp only [Function.onFun]
    rw [Finset.disjoint_left]
    intro x hxu hxv
    have h1 : u <+: x := prefix_of_mem_extensions hxu
    have h2 : v <+: x := prefix_of_mem_extensions hxv
    rcases List.prefix_or_prefix_of_prefix h1 h2 with h | h
    · exact huv (hpf u hu v hv h)
    · exact huv (hpf v hv u hu h).symm
  -- counting
  have hcard : ∑ w ∈ S, 2 ^ (n - w.length) ≤ 2 ^ n := by
    have h1 : ∑ w ∈ S, (extensions n w).card = (S.biUnion (extensions n)).card := by
      rw [Finset.card_biUnion]
      intro u hu v hv huv
      exact hdisj hu hv huv
    have h2 : (S.biUnion (extensions n)).card ≤ (boolLists n).card := by
      apply Finset.card_le_card
      intro x hx
      simp only [Finset.mem_biUnion] at hx
      obtain ⟨w, hw, hxw⟩ := hx
      exact extensions_subset (hlen w hw) hxw
    calc ∑ w ∈ S, 2 ^ (n - w.length)
        = ∑ w ∈ S, (extensions n w).card := by
          exact Finset.sum_congr rfl fun w _ => (card_extensions n w).symm
      _ = (S.biUnion (extensions n)).card := h1
      _ ≤ (boolLists n).card := h2
      _ = 2 ^ n := card_boolLists n
  -- transfer to the real-valued statement
  have hR : ∑ w ∈ S, (2 : ℝ) ^ (n - w.length) ≤ 2 ^ n := by
    have := (Nat.cast_le (α := ℝ)).2 hcard
    push_cast at this
    exact this
  have hkey : ∀ w ∈ S, (2 : ℝ) ^ (-(w.length : ℤ)) = (2 : ℝ) ^ (n - w.length) / 2 ^ n := by
    intro w hw
    have hle := hlen w hw
    have key : (2 : ℝ) ^ (n - w.length) * 2 ^ w.length = 2 ^ n := by
      rw [← pow_add, Nat.sub_add_cancel hle]
    rw [zpow_neg, zpow_natCast]
    field_simp
    linarith [key]
  rw [Finset.sum_congr rfl hkey, ← Finset.sum_div, div_le_one (by positivity)]
  exact hR

end CS

