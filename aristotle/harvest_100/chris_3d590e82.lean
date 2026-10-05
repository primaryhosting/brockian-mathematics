import Mathlib
/-!
# Pcp Pigeon Bound
Category: Computer Science
Target: CS.pcp_pigeon_bound
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace CS

/-- The finset of all boolean words (lists) of length `n`. -/
def words (n : ℕ) : Finset (List Bool) :=
  (Finset.univ : Finset (Fin n → Bool)).image (fun f => List.ofFn f)

lemma mem_words {n : ℕ} {w : List Bool} : w ∈ words n ↔ w.length = n := by
  constructor
  · rintro hw
    simp only [words, Finset.mem_image, Finset.mem_univ, true_and] at hw
    obtain ⟨f, rfl⟩ := hw
    simp
  · intro hw
    subst hw
    simp only [words, Finset.mem_image, Finset.mem_univ, true_and]
    exact ⟨fun i => w.get i, by simp⟩

lemma card_words (n : ℕ) : (words n).card = 2 ^ n := by
  rw [words, Finset.card_image_of_injective _ List.ofFn_injective]
  simp

/-- The set of length-`L` extensions of a codeword `c`. -/
def ext (L : ℕ) (c : List Bool) : Finset (List Bool) :=
  (words (L - c.length)).image (fun w => c ++ w)

lemma card_ext (L : ℕ) (c : List Bool) : (ext L c).card = 2 ^ (L - c.length) := by
  rw [ext, Finset.card_image_of_injective _ (List.append_right_injective c), card_words]

lemma ext_subset (L : ℕ) (c : List Bool) (hc : c.length ≤ L) : ext L c ⊆ words L := by
  intro w hw
  simp only [ext, Finset.mem_image] at hw
  obtain ⟨u, hu, rfl⟩ := hw
  rw [mem_words] at hu ⊢
  simp [hu]
  omega

lemma prefix_of_mem_ext {L : ℕ} {c w : List Bool} (hw : w ∈ ext L c) : c <+: w := by
  simp only [ext, Finset.mem_image] at hw
  obtain ⟨u, _, rfl⟩ := hw
  exact List.prefix_append c u

/-- Kraft's inequality, natural-number form: for a prefix-free set `S` of binary
codewords, all of length at most `L`, we have `∑ 2 ^ (L - ℓ c) ≤ 2 ^ L`. -/
lemma kraft_nat (S : Finset (List Bool)) (L : ℕ)
    (hL : ∀ c ∈ S, c.length ≤ L)
    (hpf : ∀ a ∈ S, ∀ b ∈ S, a <+: b → a = b) :
    ∑ c ∈ S, 2 ^ (L - c.length) ≤ 2 ^ L := by
  have hdisj : (S : Set (List Bool)).PairwiseDisjoint (ext L) := by
    intro a ha b hb hab
    simp only [Finset.mem_coe] at ha hb
    refine Finset.disjoint_left.mpr ?_
    intro w hwa hwb
    have h1 : a <+: w := prefix_of_mem_ext hwa
    have h2 : b <+: w := prefix_of_mem_ext hwb
    rcases List.prefix_or_prefix_of_prefix h1 h2 with h | h
    · exact hab (hpf a ha b hb h)
    · exact hab (hpf b hb a ha h).symm
  calc ∑ c ∈ S, 2 ^ (L - c.length)
      = ∑ c ∈ S, (ext L c).card := by
        exact Finset.sum_congr rfl fun c _ => (card_ext L c).symm
    _ = (S.biUnion (ext L)).card := (Finset.card_biUnion (fun a ha b hb hab =>
        hdisj (by simpa using ha) (by simpa using hb) hab)).symm
    _ ≤ (words L).card := Finset.card_le_card (by
        intro w hw
        simp only [Finset.mem_biUnion] at hw
        obtain ⟨c, hc, hwc⟩ := hw
        exact ext_subset L c (hL c hc) hwc)
    _ = 2 ^ L := card_words L

/-- **Kraft's inequality.** Any prefix-free binary code (a finite set `S` of codewords,
no one of which is a prefix of another) satisfies `∑ 2 ^ (-ℓ i) ≤ 1`. -/
theorem pcp_pigeon_bound (S : Finset (List Bool))
    (hpf : ∀ a ∈ S, ∀ b ∈ S, a <+: b → a = b) :
    ∑ c ∈ S, (1 / 2 : ℝ) ^ c.length ≤ 1 := by
  set L : ℕ := S.sup List.length with hLdef
  have hL : ∀ c ∈ S, c.length ≤ L := fun c hc => Finset.le_sup hc
  have hnat := kraft_nat S L hL hpf
  have key : ∀ c ∈ S, (1 / 2 : ℝ) ^ c.length = (2 ^ (L - c.length) : ℕ) / 2 ^ L := by
    intro c hc
    have hcL : c.length ≤ L := hL c hc
    have h : (2 : ℝ) ^ (L - c.length) * 2 ^ c.length = 2 ^ L := by
      rw [← pow_add]
      congr 1
      omega
    have hLpos : (0 : ℝ) < 2 ^ L := by positivity
    rw [div_pow, one_pow, eq_div_iff (ne_of_gt hLpos)]
    push_cast
    field_simp
    linarith [h]
  rw [Finset.sum_congr rfl key, ← Finset.sum_div]
  rw [div_le_one (by positivity)]
  calc (∑ c ∈ S, ((2 ^ (L - c.length) : ℕ) : ℝ)) = ((∑ c ∈ S, 2 ^ (L - c.length) : ℕ) : ℝ) := by
        push_cast; ring
    _ ≤ ((2 ^ L : ℕ) : ℝ) := by exact_mod_cast hnat
    _ = (2 : ℝ) ^ L := by push_cast; ring

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

