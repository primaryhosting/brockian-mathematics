import Mathlib

/-!
# Pcp Pigeon Bound
Category: Computer Science
Target: CS.pcp_pigeon_bound
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace CS

/-- The finset of all binary words of a given length. -/
def wordsOfLen : ℕ → Finset (List Bool)
  | 0 => {[]}
  | (n + 1) => Finset.univ.biUnion (fun b : Bool => (wordsOfLen n).image (b :: ·))

@[simp] lemma mem_wordsOfLen {n : ℕ} {t : List Bool} :
    t ∈ wordsOfLen n ↔ t.length = n := by
  induction n generalizing t with
  | zero =>
      simp [wordsOfLen, List.length_eq_zero_iff]
  | succ n ih =>
      cases t with
      | nil => simp [wordsOfLen]
      | cons b t =>
          simp only [wordsOfLen, Finset.mem_biUnion, Finset.mem_univ, Finset.mem_image,
            true_and, List.length_cons, ih, Nat.add_right_cancel_iff]
          constructor
          · rintro ⟨b', l, hl, h⟩
            simpa using (List.cons_eq_cons.mp h).2 ▸ hl
          · intro h
            exact ⟨b, t, h, rfl⟩

lemma card_wordsOfLen (n : ℕ) : (wordsOfLen n).card = 2 ^ n := by
  induction n with
  | zero => simp [wordsOfLen]
  | succ n ih =>
      classical
      have : (wordsOfLen (n + 1)) =
          Finset.univ.biUnion (fun b : Bool => (wordsOfLen n).image (b :: ·)) := rfl
      have hinj : ∀ b : Bool, Function.Injective (fun l : List Bool => b :: l) :=
        fun b x y h => by simpa using h
      rw [this, Finset.card_biUnion]
      · rw [Fintype.sum_bool, Finset.card_image_of_injective _ (hinj true),
          Finset.card_image_of_injective _ (hinj false), ih, pow_succ]
        ring
      · intro x _ y _ hxy
        simp only [Finset.disjoint_left, Finset.mem_image]
        rintro a ⟨l, -, rfl⟩ ⟨l', -, h⟩
        exact hxy ((List.cons_eq_cons.mp h).1).symm

/-- Words of length `n` extending a fixed prefix `w`. -/
lemma filter_prefix_eq_image {n : ℕ} {w : List Bool} (hw : w.length ≤ n) :
    (wordsOfLen n).filter (fun t => w <+: t) =
      (wordsOfLen (n - w.length)).image (fun s => w ++ s) := by
  classical
  ext t
  simp only [Finset.mem_filter, Finset.mem_image, mem_wordsOfLen]
  constructor
  · rintro ⟨hlen, s, rfl⟩
    exact ⟨s, by simp at hlen ⊢; omega, rfl⟩
  · rintro ⟨s, hs, rfl⟩
    exact ⟨by simp [hs]; omega, ⟨s, rfl⟩⟩

lemma card_filter_prefix {n : ℕ} {w : List Bool} (hw : w.length ≤ n) :
    ((wordsOfLen n).filter (fun t => w <+: t)).card = 2 ^ (n - w.length) := by
  classical
  rw [filter_prefix_eq_image hw,
    Finset.card_image_of_injective _ (fun x y h => List.append_cancel_left h),
    card_wordsOfLen]

/-- Counting form of Kraft's inequality: for a prefix-free finite set of binary words all of
length at most `n`, the number of length-`n` extensions is at most `2 ^ n`. -/
lemma kraft_nat (S : Finset (List Bool)) (n : ℕ)
    (hlen : ∀ w ∈ S, w.length ≤ n)
    (hpf : ∀ u ∈ S, ∀ v ∈ S, u <+: v → u = v) :
    ∑ w ∈ S, 2 ^ (n - w.length) ≤ 2 ^ n := by
  classical
  have hdisj : (S : Set (List Bool)).PairwiseDisjoint
      (fun w => (wordsOfLen n).filter (fun t => w <+: t)) := by
    intro u hu v hv huv
    simp only [Function.onFun, Finset.disjoint_left, Finset.mem_filter]
    rintro t ⟨-, hut⟩ ⟨-, hvt⟩
    rcases List.prefix_or_prefix_of_prefix hut hvt with h | h
    · exact huv (hpf u hu v hv h)
    · exact huv (hpf v hv u hu h).symm
  calc ∑ w ∈ S, 2 ^ (n - w.length)
      = ∑ w ∈ S, ((wordsOfLen n).filter (fun t => w <+: t)).card := by
        refine Finset.sum_congr rfl fun w hw => ?_
        rw [card_filter_prefix (hlen w hw)]
    _ = (S.biUnion (fun w => (wordsOfLen n).filter (fun t => w <+: t))).card := by
        rw [Finset.card_biUnion (fun x hx y hy hxy => hdisj hx hy hxy)]
    _ ≤ (wordsOfLen n).card := by
        refine Finset.card_le_card ?_
        intro t ht
        simp only [Finset.mem_biUnion, Finset.mem_filter] at ht
        obtain ⟨-, -, h, -⟩ := ht
        exact h
    _ = 2 ^ n := card_wordsOfLen n

/-- **Kraft's inequality.** Any prefix-free binary code `S` (a finite set of binary words in
which no word is a prefix of another) satisfies `∑ 2 ^ (-ℓ_i) ≤ 1`. -/
theorem pcp_pigeon_bound (S : Finset (List Bool))
    (hpf : ∀ u ∈ S, ∀ v ∈ S, u <+: v → u = v) :
    ∑ w ∈ S, (1 / 2 : ℝ) ^ w.length ≤ 1 := by
  classical
  set n := S.sup (fun w => w.length) with hn
  have hlen : ∀ w ∈ S, w.length ≤ n := fun w hw => Finset.le_sup (f := fun w : List Bool => w.length) hw
  have hnat := kraft_nat S n hlen hpf
  have hcast : ((∑ w ∈ S, 2 ^ (n - w.length) : ℕ) : ℝ) ≤ ((2 ^ n : ℕ) : ℝ) :=
    Nat.cast_le.mpr hnat
  push_cast at hcast
  have hkey : ∀ w ∈ S, (2 : ℝ) ^ (n - w.length) = 2 ^ n * (1 / 2 : ℝ) ^ w.length := by
    intro w hw
    have hle := hlen w hw
    have h : (2 : ℝ) ^ (n - w.length) * 2 ^ w.length = 2 ^ n := by
      rw [← pow_add]
      congr 1
      omega
    have h2 : ((2 : ℝ) ^ w.length) ≠ 0 := by positivity
    have hrw : (2 : ℝ) ^ n * (1 / 2 : ℝ) ^ w.length = 2 ^ n / 2 ^ w.length := by
      rw [div_pow, one_pow]
      ring
    rw [hrw, eq_div_iff h2]
    exact h
  rw [Finset.sum_congr rfl hkey, ← Finset.mul_sum] at hcast
  have hpos : (0 : ℝ) < 2 ^ n := by positivity
  nlinarith [hcast, hpos]

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

