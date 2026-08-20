/-
# Euler Pentagonal
Category: Pure Mathematics
Target: Math.euler_pentagonal
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Euler Pentagonal
Category: Pure Mathematics
Target: Math.euler_pentagonal
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

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

/-!
Euler's pentagonal number theorem.

We prove that the coefficient of `q^n` in the (truncated) product `∏_{i=1}^{N} (1 - q^i)`
(for any `N ≥ n`, so that the coefficient has already stabilised) equals
`∑_{k ∈ ℤ} (-1)^k [n = k(3k-1)/2]`.

The proof is Franklin's involution on partitions into distinct parts.
-/

namespace Math

open Finset

/-! ### Basic combinatorial gadgets -/

/-- `runLen s t` is the length of the maximal run `t, t-1, t-2, …` of consecutive
elements of `s` ending at `t`. -/
def runLen (s : Finset ℕ) : ℕ → ℕ
  | 0 => 0
  | t + 1 => if (t + 1) ∈ s then runLen s t + 1 else 0

/-- The largest element of `s` (junk value `0` for `s = ∅`). -/
noncomputable def mxf (s : Finset ℕ) : ℕ := if h : s.Nonempty then s.max' h else 0

/-- The smallest element of `s` (junk value `0` for `s = ∅`). -/
noncomputable def mnf (s : Finset ℕ) : ℕ := if h : s.Nonempty then s.min' h else 0

/-- The length of the maximal run of consecutive elements at the top of `s`. -/
noncomputable def df (s : Finset ℕ) : ℕ := runLen s (mxf s)

/-- Franklin's map in the case `min ≤ run`: delete the smallest part and add `1` to each
of the `min` largest parts. -/
noncomputable def b1img (s : Finset ℕ) : Finset ℕ :=
  insert (mxf s + 1) ((s.erase (mnf s)).erase (mxf s - mnf s + 1))

/-- Franklin's map in the case `run < min`: subtract `1` from each of the `run` largest
parts and create a new part equal to `run`. -/
noncomputable def b2img (s : Finset ℕ) : Finset ℕ :=
  insert (df s) (insert (mxf s - df s) (s.erase (mxf s)))

/-- Franklin's involution on partitions into distinct parts, encoded as finite sets of
positive integers. -/
noncomputable def franklin (s : Finset ℕ) : Finset ℕ :=
  if mnf s ≤ df s then b1img s else b2img s

/-- The exceptional (non-cancelling) sets of Franklin's involution. -/
def IsExc (s : Finset ℕ) : Prop :=
  (mnf s ≤ df s ∧ mxf s + 1 = 2 * mnf s) ∨ (df s < mnf s ∧ mxf s = 2 * df s)

/-- Sets fixed by (i.e. excluded from) the cancellation argument. -/
def IsFixed (s : Finset ℕ) : Prop := s = ∅ ∨ IsExc s

/-- Partitions of `n` into distinct parts, encoded as finite sets of positive integers
summing to `n`. -/
def distinctParts (n : ℕ) : Finset (Finset ℕ) :=
  (Finset.Icc 1 n).powerset.filter (fun s => ∑ i ∈ s, i = n)

/-- The right-hand side of the pentagonal number theorem: `∑_{k ∈ ℤ} (-1)^k [2n = k(3k-1)]`. -/
noncomputable def pentagonalSign (n : ℕ) : ℤ :=
  ∑ k ∈ Finset.Icc (-(n : ℤ)) (n : ℤ), if 2 * (n : ℤ) = k * (3 * k - 1) then (-1) ^ k.natAbs else 0

/-! ### Elementary lemmas -/

lemma mxf_mem {s : Finset ℕ} (h : s.Nonempty) : mxf s ∈ s := by
  simp only [mxf, dif_pos h]; exact s.max'_mem h

lemma le_mxf {s : Finset ℕ} {a : ℕ} (h : a ∈ s) : a ≤ mxf s := by
  have hne : s.Nonempty := ⟨a, h⟩
  simp only [mxf, dif_pos hne]; exact s.le_max' a h

lemma mnf_mem {s : Finset ℕ} (h : s.Nonempty) : mnf s ∈ s := by
  simp only [mnf, dif_pos h]; exact s.min'_mem h

lemma mnf_le {s : Finset ℕ} {a : ℕ} (h : a ∈ s) : mnf s ≤ a := by
  have hne : s.Nonempty := ⟨a, h⟩
  simp only [mnf, dif_pos hne]; exact s.min'_le a h

lemma mxf_eq_of {s : Finset ℕ} {a : ℕ} (hmem : a ∈ s) (hle : ∀ b ∈ s, b ≤ a) : mxf s = a :=
  le_antisymm (by
    have hne : s.Nonempty := ⟨a, hmem⟩
    exact hle _ (mxf_mem hne)) (le_mxf hmem)

lemma mnf_eq_of {s : Finset ℕ} {a : ℕ} (hmem : a ∈ s) (hge : ∀ b ∈ s, a ≤ b) : mnf s = a :=
  le_antisymm (mnf_le hmem) (by
    have hne : s.Nonempty := ⟨a, hmem⟩
    exact hge _ (mnf_mem hne))

lemma runLen_le (s : Finset ℕ) (t : ℕ) : runLen s t ≤ t := by
  induction t with
  | zero => simp [runLen]
  | succ t ih =>
      simp only [runLen]
      split
      · omega
      · omega

lemma runLen_mem (s : Finset ℕ) (t : ℕ) : ∀ i < runLen s t, t - i ∈ s := by
  induction t with
  | zero => intro i hi; simp [runLen] at hi
  | succ t ih =>
      intro i hi
      simp only [runLen] at hi
      split at hi
      · rename_i hmem
        rcases Nat.eq_zero_or_pos i with rfl | hpos
        · simpa using hmem
        · have : t + 1 - i = t - (i - 1) := by omega
          rw [this]
          exact ih _ (by omega)
      · omega

lemma runLen_not_mem {s : Finset ℕ} (h0 : 0 ∉ s) (t : ℕ) : t - runLen s t ∉ s := by
  induction t with
  | zero => simpa [runLen] using h0
  | succ t ih =>
      simp only [runLen]
      split
      · have : t + 1 - (runLen s t + 1) = t - runLen s t := by omega
        rw [this]; exact ih
      · simpa using ‹t + 1 ∉ s›

lemma le_runLen {s : Finset ℕ} (h0 : 0 ∉ s) (t j : ℕ) (h : ∀ i < j, t - i ∈ s) :
    j ≤ runLen s t := by
  induction t generalizing j with
  | zero =>
      by_contra hc
      have : (0 : ℕ) - 0 ∈ s := h 0 (by omega)
      simp at this; exact h0 this
  | succ t ih =>
      rcases Nat.eq_zero_or_pos j with rfl | hpos
      · omega
      · have hmem : t + 1 ∈ s := by simpa using h 0 (by omega)
        simp only [runLen, if_pos hmem]
        have : j - 1 ≤ runLen s t := by
          refine ih (j - 1) ?_
          intro i hi
          have : t - i = t + 1 - (i + 1) := by omega
          rw [this]
          exact h (i + 1) (by omega)
        omega

lemma runLen_eq_of {s : Finset ℕ} (h0 : 0 ∉ s) {t r : ℕ} (h1 : ∀ i < r, t - i ∈ s)
    (h2 : t - r ∉ s) : runLen s t = r := by
  have hle : r ≤ runLen s t := le_runLen h0 t r h1
  by_contra hne
  have : r < runLen s t := lt_of_le_of_ne hle (Ne.symm hne)
  exact h2 (runLen_mem s t r this)

/-! ### Basic facts about `df` -/

lemma one_le_mnf {s : Finset ℕ} (h0 : 0 ∉ s) (hne : s.Nonempty) : 1 ≤ mnf s := by
  rcases Nat.eq_zero_or_pos (mnf s) with h | h
  · exact absurd (h ▸ mnf_mem hne) h0
  · exact h

lemma one_le_mxf {s : Finset ℕ} (h0 : 0 ∉ s) (hne : s.Nonempty) : 1 ≤ mxf s :=
  le_trans (one_le_mnf h0 hne) (mnf_le (mxf_mem hne))

lemma one_le_df {s : Finset ℕ} (h0 : 0 ∉ s) (hne : s.Nonempty) : 1 ≤ df s := by
  have h1 : 1 ≤ mxf s := one_le_mxf h0 hne
  have := mxf_mem hne
  unfold df
  obtain ⟨t, ht⟩ : ∃ t, mxf s = t + 1 := ⟨mxf s - 1, by omega⟩
  rw [ht] at this ⊢
  simp only [runLen, if_pos this]
  omega

lemma df_le_mxf (s : Finset ℕ) : df s ≤ mxf s := runLen_le _ _

lemma df_run (s : Finset ℕ) : ∀ i < df s, mxf s - i ∈ s := runLen_mem _ _

lemma df_not_mem {s : Finset ℕ} (h0 : 0 ∉ s) : mxf s - df s ∉ s := runLen_not_mem h0 _

lemma df_eq_of {s : Finset ℕ} (h0 : 0 ∉ s) {r : ℕ} (h1 : ∀ i < r, mxf s - i ∈ s)
    (h2 : mxf s - r ∉ s) : df s = r := runLen_eq_of h0 h1 h2

lemma le_df_of {s : Finset ℕ} (h0 : 0 ∉ s) {r : ℕ} (h1 : ∀ i < r, mxf s - i ∈ s) :
    r ≤ df s := le_runLen h0 _ _ h1

lemma mnf_add_df_le {s : Finset ℕ} (h0 : 0 ∉ s) (hne : s.Nonempty) :
    mnf s + df s ≤ mxf s + 1 := by
  have hd : 1 ≤ df s := one_le_df h0 hne
  have hmem : mxf s - (df s - 1) ∈ s := df_run s _ (by omega)
  have := mnf_le hmem
  have := df_le_mxf s
  omega

/-! ### Branch 1 of Franklin's involution: `min ≤ run` -/

section Branch1

variable {s : Finset ℕ}

lemma b1_two_mul_mnf_le (h0 : 0 ∉ s) (hne : s.Nonempty) (hb : mnf s ≤ df s)
    (hexc : ¬ IsExc s) : 2 * mnf s ≤ mxf s := by
  have h1 := mnf_add_df_le h0 hne
  have h2 : mxf s + 1 ≠ 2 * mnf s := fun h => hexc (Or.inl ⟨hb, h⟩)
  omega

lemma b1_top_mem (h0 : 0 ∉ s) (hne : s.Nonempty) (hb : mnf s ≤ df s) :
    mxf s - mnf s + 1 ∈ s := by
  have hm1 : 1 ≤ mnf s := one_le_mnf h0 hne
  have hmx : mnf s ≤ mxf s := mnf_le (mxf_mem hne)
  have hmem := df_run s (mnf s - 1) (by omega)
  have heq : mxf s - (mnf s - 1) = mxf s - mnf s + 1 := by omega
  rwa [heq] at hmem

lemma b1_mnf_lt_top (h0 : 0 ∉ s) (hne : s.Nonempty) (hb : mnf s ≤ df s)
    (hexc : ¬ IsExc s) : mnf s < mxf s - mnf s + 1 := by
  have := b1_two_mul_mnf_le h0 hne hb hexc
  omega

lemma mem_b1img {a : ℕ} :
    a ∈ b1img s ↔ (a = mxf s + 1 ∨ (a ∈ s ∧ a ≠ mnf s ∧ a ≠ mxf s - mnf s + 1)) := by
  simp only [b1img, Finset.mem_insert, Finset.mem_erase]
  tauto

lemma b1_zero_not_mem (h0 : 0 ∉ s) : 0 ∉ b1img s := by
  intro h
  rcases mem_b1img.1 h with h | ⟨h, _⟩
  · omega
  · exact h0 h

lemma b1_nonempty : (b1img s).Nonempty := ⟨_, Finset.mem_insert_self _ _⟩

lemma b1_mxf : mxf (b1img s) = mxf s + 1 := by
  refine mxf_eq_of (mem_b1img.2 (Or.inl rfl)) ?_
  intro b hb
  rcases mem_b1img.1 hb with h | ⟨h, _⟩
  · omega
  · have := le_mxf h; omega

lemma b1_mnf_gt (hne : s.Nonempty) : mnf s < mnf (b1img s) := by
  have hne' : (b1img s).Nonempty := b1_nonempty
  have hm := mnf_mem hne'
  rcases mem_b1img.1 hm with h | ⟨h, hne1, _⟩
  · have : mnf s ≤ mxf s := mnf_le (mxf_mem hne)
    omega
  · have := mnf_le h
    omega

lemma b1_df (h0 : 0 ∉ s) (hne : s.Nonempty) (hb : mnf s ≤ df s) (hexc : ¬ IsExc s) :
    df (b1img s) = mnf s := by
  have h2 := b1_two_mul_mnf_le h0 hne hb hexc
  have hm1 : 1 ≤ mnf s := one_le_mnf h0 hne
  have hmx : mnf s ≤ mxf s := mnf_le (mxf_mem hne)
  refine df_eq_of (b1_zero_not_mem h0) ?_ ?_
  · intro i hi
    rw [b1_mxf]
    rcases Nat.eq_zero_or_pos i with rfl | hpos
    · exact mem_b1img.2 (Or.inl (by omega))
    · refine mem_b1img.2 (Or.inr ⟨?_, by omega, by omega⟩)
      have hmem := df_run s (i - 1) (by omega)
      have heq : mxf s - (i - 1) = mxf s + 1 - i := by omega
      rwa [heq] at hmem
  · rw [b1_mxf]
    intro hmem
    rcases mem_b1img.1 hmem with h | ⟨_, _, h⟩
    · omega
    · omega

lemma b1_branch (h0 : 0 ∉ s) (hne : s.Nonempty) (hb : mnf s ≤ df s) (hexc : ¬ IsExc s) :
    df (b1img s) < mnf (b1img s) := by
  rw [b1_df h0 hne hb hexc]
  exact b1_mnf_gt hne

lemma b1_not_exc (h0 : 0 ∉ s) (hne : s.Nonempty) (hb : mnf s ≤ df s) (hexc : ¬ IsExc s) :
    ¬ IsExc (b1img s) := by
  have hbr := b1_branch h0 hne hb hexc
  have h2 := b1_two_mul_mnf_le h0 hne hb hexc
  rintro (⟨h, _⟩ | ⟨_, h⟩)
  · omega
  · rw [b1_mxf, b1_df h0 hne hb hexc] at h
    omega

lemma b1_sum (h0 : 0 ∉ s) (hne : s.Nonempty) (hb : mnf s ≤ df s) (hexc : ¬ IsExc s) :
    ∑ i ∈ b1img s, i = ∑ i ∈ s, i := by
  classical
  have hmx : mnf s ≤ mxf s := mnf_le (mxf_mem hne)
  have hmem : mnf s ∈ s := mnf_mem hne
  have htop : mxf s - mnf s + 1 ∈ s := b1_top_mem h0 hne hb
  have hlt : mnf s < mxf s - mnf s + 1 := b1_mnf_lt_top h0 hne hb hexc
  have htop' : mxf s - mnf s + 1 ∈ s.erase (mnf s) :=
    Finset.mem_erase.2 ⟨by omega, htop⟩
  have hnot : mxf s + 1 ∉ (s.erase (mnf s)).erase (mxf s - mnf s + 1) := by
    intro h
    have hs : mxf s + 1 ∈ s := Finset.mem_of_mem_erase (Finset.mem_of_mem_erase h)
    have := le_mxf hs
    omega
  have h1 : ∑ i ∈ b1img s, i
      = (mxf s + 1) + ∑ i ∈ (s.erase (mnf s)).erase (mxf s - mnf s + 1), i := by
    rw [b1img, Finset.sum_insert hnot]
  have h2 : ∑ i ∈ s.erase (mnf s), i
      = (mxf s - mnf s + 1) + ∑ i ∈ (s.erase (mnf s)).erase (mxf s - mnf s + 1), i :=
    (Finset.add_sum_erase _ _ htop').symm
  have h3 : ∑ i ∈ s, i = mnf s + ∑ i ∈ s.erase (mnf s), i :=
    (Finset.add_sum_erase _ _ hmem).symm
  omega

lemma b1_card (h0 : 0 ∉ s) (hne : s.Nonempty) (hb : mnf s ≤ df s) (hexc : ¬ IsExc s) :
    (b1img s).card + 1 = s.card := by
  classical
  have hmx : mnf s ≤ mxf s := mnf_le (mxf_mem hne)
  have hmem : mnf s ∈ s := mnf_mem hne
  have htop : mxf s - mnf s + 1 ∈ s := b1_top_mem h0 hne hb
  have hlt : mnf s < mxf s - mnf s + 1 := b1_mnf_lt_top h0 hne hb hexc
  have htop' : mxf s - mnf s + 1 ∈ s.erase (mnf s) :=
    Finset.mem_erase.2 ⟨by omega, htop⟩
  have hnot : mxf s + 1 ∉ (s.erase (mnf s)).erase (mxf s - mnf s + 1) := by
    intro h
    have hs : mxf s + 1 ∈ s := Finset.mem_of_mem_erase (Finset.mem_of_mem_erase h)
    have := le_mxf hs
    omega
  have h1 : (b1img s).card = ((s.erase (mnf s)).erase (mxf s - mnf s + 1)).card + 1 := by
    rw [b1img, Finset.card_insert_of_notMem hnot]
  have h2 : ((s.erase (mnf s)).erase (mxf s - mnf s + 1)).card + 1 = (s.erase (mnf s)).card :=
    Finset.card_erase_add_one htop'
  have h3 : (s.erase (mnf s)).card + 1 = s.card := Finset.card_erase_add_one hmem
  omega

lemma b1_inv (h0 : 0 ∉ s) (hne : s.Nonempty) (hb : mnf s ≤ df s) (hexc : ¬ IsExc s) :
    franklin (b1img s) = s := by
  classical
  have hmx : mnf s ≤ mxf s := mnf_le (mxf_mem hne)
  have hmem : mnf s ∈ s := mnf_mem hne
  have htop : mxf s - mnf s + 1 ∈ s := b1_top_mem h0 hne hb
  have hlt : mnf s < mxf s - mnf s + 1 := b1_mnf_lt_top h0 hne hb hexc
  have htop' : mxf s - mnf s + 1 ∈ s.erase (mnf s) :=
    Finset.mem_erase.2 ⟨by omega, htop⟩
  have hnot : mxf s + 1 ∉ (s.erase (mnf s)).erase (mxf s - mnf s + 1) := by
    intro h
    have hs : mxf s + 1 ∈ s := Finset.mem_of_mem_erase (Finset.mem_of_mem_erase h)
    have := le_mxf hs
    omega
  have hbr := b1_branch h0 hne hb hexc
  rw [franklin, if_neg (by omega), b2img, b1_df h0 hne hb hexc, b1_mxf]
  have herase : (b1img s).erase (mxf s + 1) = (s.erase (mnf s)).erase (mxf s - mnf s + 1) := by
    rw [b1img, Finset.erase_insert hnot]
  rw [herase]
  have heq : mxf s + 1 - mnf s = mxf s - mnf s + 1 := by omega
  rw [heq, Finset.insert_erase htop', Finset.insert_erase hmem]

end Branch1

/-! ### Branch 2 of Franklin's involution: `run < min` -/

section Branch2

variable {s : Finset ℕ}

lemma b2_two_mul_df_lt (h0 : 0 ∉ s) (hne : s.Nonempty) (hb : df s < mnf s)
    (hexc : ¬ IsExc s) : 2 * df s < mxf s := by
  have h1 := mnf_add_df_le h0 hne
  have h2 : mxf s ≠ 2 * df s := fun h => hexc (Or.inr ⟨hb, h⟩)
  omega

lemma mem_b2img {a : ℕ} :
    a ∈ b2img s ↔ (a = df s ∨ a = mxf s - df s ∨ (a ∈ s ∧ a ≠ mxf s)) := by
  simp only [b2img, Finset.mem_insert, Finset.mem_erase]
  tauto

lemma b2_df_not_mem (hb : df s < mnf s) : df s ∉ s := by
  intro h
  have := mnf_le h
  omega

lemma b2_zero_not_mem (h0 : 0 ∉ s) (hne : s.Nonempty) (hb : df s < mnf s)
    (hexc : ¬ IsExc s) : 0 ∉ b2img s := by
  have hd1 : 1 ≤ df s := one_le_df h0 hne
  have h2 := b2_two_mul_df_lt h0 hne hb hexc
  intro h
  rcases mem_b2img.1 h with h | h | ⟨h, _⟩
  · omega
  · omega
  · exact h0 h

lemma b2_nonempty : (b2img s).Nonempty := ⟨_, Finset.mem_insert_self _ _⟩

lemma b2_mxf (h0 : 0 ∉ s) (hne : s.Nonempty) (hb : df s < mnf s) (hexc : ¬ IsExc s) :
    mxf (b2img s) = mxf s - 1 := by
  have hd1 : 1 ≤ df s := one_le_df h0 hne
  have h2 := b2_two_mul_df_lt h0 hne hb hexc
  have hmM : mnf s ≤ mxf s := mnf_le (mxf_mem hne)
  refine mxf_eq_of ?_ ?_
  · rcases Nat.lt_or_ge 1 (df s) with hd | hd
    · exact mem_b2img.2 (Or.inr (Or.inr ⟨df_run s 1 hd, by omega⟩))
    · exact mem_b2img.2 (Or.inr (Or.inl (by omega)))
  · intro b hbm
    rcases mem_b2img.1 hbm with h | h | ⟨h, hne'⟩
    · omega
    · omega
    · have := le_mxf h; omega

lemma b2_mnf (h0 : 0 ∉ s) (hne : s.Nonempty) (hb : df s < mnf s) (hexc : ¬ IsExc s) :
    mnf (b2img s) = df s := by
  have h2 := b2_two_mul_df_lt h0 hne hb hexc
  refine mnf_eq_of (mem_b2img.2 (Or.inl rfl)) ?_
  intro b hbm
  rcases mem_b2img.1 hbm with h | h | ⟨h, _⟩
  · omega
  · omega
  · have := mnf_le h; omega

lemma b2_le_df (h0 : 0 ∉ s) (hne : s.Nonempty) (hb : df s < mnf s) (hexc : ¬ IsExc s) :
    df s ≤ df (b2img s) := by
  have hd1 : 1 ≤ df s := one_le_df h0 hne
  have h2 := b2_two_mul_df_lt h0 hne hb hexc
  refine le_df_of (b2_zero_not_mem h0 hne hb hexc) ?_
  intro i hi
  rw [b2_mxf h0 hne hb hexc]
  rcases Nat.lt_or_ge (i + 1) (df s) with hc | hc
  · refine mem_b2img.2 (Or.inr (Or.inr ⟨?_, by omega⟩))
    have hmem := df_run s (i + 1) hc
    have heq : mxf s - (i + 1) = mxf s - 1 - i := by omega
    rwa [heq] at hmem
  · exact mem_b2img.2 (Or.inr (Or.inl (by omega)))

lemma b2_branch (h0 : 0 ∉ s) (hne : s.Nonempty) (hb : df s < mnf s) (hexc : ¬ IsExc s) :
    mnf (b2img s) ≤ df (b2img s) := by
  rw [b2_mnf h0 hne hb hexc]
  exact b2_le_df h0 hne hb hexc

lemma b2_not_exc (h0 : 0 ∉ s) (hne : s.Nonempty) (hb : df s < mnf s) (hexc : ¬ IsExc s) :
    ¬ IsExc (b2img s) := by
  have hd1 : 1 ≤ df s := one_le_df h0 hne
  have h2 := b2_two_mul_df_lt h0 hne hb hexc
  have hbr := b2_branch h0 hne hb hexc
  rintro (⟨_, h⟩ | ⟨h, _⟩)
  · rw [b2_mxf h0 hne hb hexc, b2_mnf h0 hne hb hexc] at h
    omega
  · omega

lemma b2_sum (h0 : 0 ∉ s) (hne : s.Nonempty) (hb : df s < mnf s) (hexc : ¬ IsExc s) :
    ∑ i ∈ b2img s, i = ∑ i ∈ s, i := by
  classical
  have hd1 : 1 ≤ df s := one_le_df h0 hne
  have h2 := b2_two_mul_df_lt h0 hne hb hexc
  have hMmem : mxf s ∈ s := mxf_mem hne
  have hdn : df s ∉ s := b2_df_not_mem hb
  have hMdn : mxf s - df s ∉ s := df_not_mem h0
  have hn1 : mxf s - df s ∉ s.erase (mxf s) := fun h => hMdn (Finset.mem_of_mem_erase h)
  have hn2 : df s ∉ insert (mxf s - df s) (s.erase (mxf s)) := by
    simp only [Finset.mem_insert, Finset.mem_erase, not_or]
    exact ⟨by omega, fun h => hdn h.2⟩
  have e1 : ∑ i ∈ b2img s, i
      = df s + ((mxf s - df s) + ∑ i ∈ s.erase (mxf s), i) := by
    rw [b2img, Finset.sum_insert hn2, Finset.sum_insert hn1]
  have e2 : ∑ i ∈ s, i = mxf s + ∑ i ∈ s.erase (mxf s), i :=
    (Finset.add_sum_erase _ _ hMmem).symm
  omega

lemma b2_card (h0 : 0 ∉ s) (hne : s.Nonempty) (hb : df s < mnf s) (hexc : ¬ IsExc s) :
    (b2img s).card = s.card + 1 := by
  classical
  have hd1 : 1 ≤ df s := one_le_df h0 hne
  have h2 := b2_two_mul_df_lt h0 hne hb hexc
  have hMmem : mxf s ∈ s := mxf_mem hne
  have hdn : df s ∉ s := b2_df_not_mem hb
  have hMdn : mxf s - df s ∉ s := df_not_mem h0
  have hn1 : mxf s - df s ∉ s.erase (mxf s) := fun h => hMdn (Finset.mem_of_mem_erase h)
  have hn2 : df s ∉ insert (mxf s - df s) (s.erase (mxf s)) := by
    simp only [Finset.mem_insert, Finset.mem_erase, not_or]
    exact ⟨by omega, fun h => hdn h.2⟩
  have e1 : (b2img s).card = (s.erase (mxf s)).card + 2 := by
    rw [b2img, Finset.card_insert_of_notMem hn2, Finset.card_insert_of_notMem hn1]
  have e2 : (s.erase (mxf s)).card + 1 = s.card := Finset.card_erase_add_one hMmem
  omega

lemma b2_inv (h0 : 0 ∉ s) (hne : s.Nonempty) (hb : df s < mnf s) (hexc : ¬ IsExc s) :
    franklin (b2img s) = s := by
  classical
  have hd1 : 1 ≤ df s := one_le_df h0 hne
  have h2 := b2_two_mul_df_lt h0 hne hb hexc
  have hMmem : mxf s ∈ s := mxf_mem hne
  have hdn : df s ∉ s := b2_df_not_mem hb
  have hMdn : mxf s - df s ∉ s := df_not_mem h0
  have hn1 : mxf s - df s ∉ s.erase (mxf s) := fun h => hMdn (Finset.mem_of_mem_erase h)
  have hn2 : df s ∉ insert (mxf s - df s) (s.erase (mxf s)) := by
    simp only [Finset.mem_insert, Finset.mem_erase, not_or]
    exact ⟨by omega, fun h => hdn h.2⟩
  have hbr := b2_branch h0 hne hb hexc
  rw [franklin, if_pos hbr, b1img, b2_mnf h0 hne hb hexc, b2_mxf h0 hne hb hexc]
  have herase : (b2img s).erase (df s) = insert (mxf s - df s) (s.erase (mxf s)) := by
    rw [b2img, Finset.erase_insert hn2]
  rw [herase]
  have heq : mxf s - 1 - df s + 1 = mxf s - df s := by omega
  rw [heq, Finset.erase_insert hn1]
  have heq2 : mxf s - 1 + 1 = mxf s := by omega
  rw [heq2, Finset.insert_erase hMmem]

end Branch2

/-! ### The involution -/

section Franklin

variable {s : Finset ℕ} (h0 : 0 ∉ s) (hne : s.Nonempty) (hexc : ¬ IsExc s)

include h0 hne hexc

lemma franklin_sum : ∑ i ∈ franklin s, i = ∑ i ∈ s, i := by
  unfold franklin
  split
  · exact b1_sum h0 hne ‹_› hexc
  · exact b2_sum h0 hne (by omega) hexc

lemma franklin_zero_not_mem : 0 ∉ franklin s := by
  unfold franklin
  split
  · exact b1_zero_not_mem h0
  · exact b2_zero_not_mem h0 hne (by omega) hexc

omit h0 hne hexc in
lemma franklin_nonempty : (franklin s).Nonempty := by
  unfold franklin
  split
  · exact b1_nonempty
  · exact b2_nonempty

lemma franklin_not_exc : ¬ IsExc (franklin s) := by
  unfold franklin
  split
  · exact b1_not_exc h0 hne ‹_› hexc
  · exact b2_not_exc h0 hne (by omega) hexc

lemma franklin_franklin : franklin (franklin s) = s := by
  unfold franklin
  split
  · exact b1_inv h0 hne ‹_› hexc
  · exact b2_inv h0 hne (by omega) hexc

lemma franklin_sign : (-1 : ℤ) ^ (franklin s).card = -(-1 : ℤ) ^ s.card := by
  have h : (franklin s).card + 1 = s.card ∨ (franklin s).card = s.card + 1 := by
    unfold franklin
    split
    · exact Or.inl (b1_card h0 hne ‹_› hexc)
    · exact Or.inr (b2_card h0 hne (by omega) hexc)
  rcases h with h | h
  · rw [← h, pow_succ]; ring
  · rw [h, pow_succ]; ring

end Franklin

/-! ### The exceptional sets -/

lemma mnf_Ico {a b : ℕ} (h : a < b) : mnf (Finset.Ico a b) = a := by
  refine mnf_eq_of (Finset.mem_Ico.2 ⟨le_refl _, h⟩) ?_
  intro x hx
  exact (Finset.mem_Ico.1 hx).1

lemma mxf_Ico {a b : ℕ} (h : a < b) : mxf (Finset.Ico a b) = b - 1 := by
  refine mxf_eq_of (Finset.mem_Ico.2 ⟨by omega, by omega⟩) ?_
  intro x hx
  have := Finset.mem_Ico.1 hx
  omega

lemma zero_not_mem_Ico {a b : ℕ} (h : 1 ≤ a) : 0 ∉ Finset.Ico a b := by
  intro hx
  have := Finset.mem_Ico.1 hx
  omega

lemma df_Ico1 {k : ℕ} (hk : 1 ≤ k) : df (Finset.Ico k (2 * k)) = k := by
  refine df_eq_of (zero_not_mem_Ico hk) ?_ ?_ <;> rw [mxf_Ico (by omega : k < 2 * k)]
  · intro i hi
    exact Finset.mem_Ico.2 ⟨by omega, by omega⟩
  · intro hx
    have := Finset.mem_Ico.1 hx
    omega

lemma df_Ico2 {k : ℕ} (hk : 1 ≤ k) : df (Finset.Ico (k + 1) (2 * k + 1)) = k := by
  refine df_eq_of (zero_not_mem_Ico (by omega)) ?_ ?_ <;>
    rw [mxf_Ico (by omega : k + 1 < 2 * k + 1)]
  · intro i hi
    exact Finset.mem_Ico.2 ⟨by omega, by omega⟩
  · intro hx
    have := Finset.mem_Ico.1 hx
    omega

lemma isExc_iff {s : Finset ℕ} (h0 : 0 ∉ s) (hne : s.Nonempty) :
    IsExc s ↔ ∃ k, 1 ≤ k ∧ (s = Finset.Ico k (2 * k) ∨ s = Finset.Ico (k + 1) (2 * k + 1)) := by
  constructor
  · rintro (⟨hb, hM⟩ | ⟨hb, hM⟩)
    · have hm1 : 1 ≤ mnf s := one_le_mnf h0 hne
      have hsum := mnf_add_df_le h0 hne
      have hdf : df s = mnf s := by omega
      refine ⟨mnf s, hm1, Or.inl ?_⟩
      apply Finset.ext
      intro a
      constructor
      · intro ha
        have h1 := mnf_le ha
        have h2 := le_mxf ha
        exact Finset.mem_Ico.2 ⟨h1, by omega⟩
      · intro ha
        have := Finset.mem_Ico.1 ha
        have hmem := df_run s (mxf s - a) (by omega)
        have heq : mxf s - (mxf s - a) = a := by omega
        rwa [heq] at hmem
    · have hm1 : 1 ≤ mnf s := one_le_mnf h0 hne
      have hd1 : 1 ≤ df s := one_le_df h0 hne
      have hsum := mnf_add_df_le h0 hne
      have hmn : mnf s = df s + 1 := by omega
      refine ⟨df s, hd1, Or.inr ?_⟩
      apply Finset.ext
      intro a
      constructor
      · intro ha
        have h1 := mnf_le ha
        have h2 := le_mxf ha
        exact Finset.mem_Ico.2 ⟨by omega, by omega⟩
      · intro ha
        have := Finset.mem_Ico.1 ha
        have hmem := df_run s (mxf s - a) (by omega)
        have heq : mxf s - (mxf s - a) = a := by omega
        rwa [heq] at hmem
  · rintro ⟨k, hk, rfl | rfl⟩
    · left
      rw [mnf_Ico (by omega : k < 2 * k), mxf_Ico (by omega : k < 2 * k), df_Ico1 hk]
      omega
    · right
      rw [mnf_Ico (by omega : k + 1 < 2 * k + 1), mxf_Ico (by omega : k + 1 < 2 * k + 1),
        df_Ico2 hk]
      omega

/-- The index set of the pentagonal numbers attached to `n`. -/
noncomputable def pentIdx (n : ℕ) : Finset ℤ :=
  (Finset.Icc (-(n : ℤ)) (n : ℤ)).filter (fun k => 2 * (n : ℤ) = k * (3 * k - 1))

/-- The finite set of positive integers attached to a pentagonal index. -/
noncomputable def pentSet (k : ℤ) : Finset ℕ :=
  if 0 ≤ k then Finset.Ico k.toNat (2 * k.toNat)
  else Finset.Ico (k.natAbs + 1) (2 * k.natAbs + 1)

/-- The pentagonal index attached to a fixed set. -/
noncomputable def pentIdxOf (s : Finset ℕ) : ℤ :=
  if s.card = 0 then 0 else if mnf s = s.card then (s.card : ℤ) else -(s.card : ℤ)

/-! ### From the product to the signed count -/

lemma mem_distinctParts {n : ℕ} {s : Finset ℕ} :
    s ∈ distinctParts n ↔ (0 ∉ s ∧ ∑ i ∈ s, i = n) := by
  classical
  simp only [distinctParts, Finset.mem_filter, Finset.mem_powerset]
  constructor
  · rintro ⟨hsub, hsum⟩
    refine ⟨fun h0 => ?_, hsum⟩
    have := hsub h0
    simp at this
  · rintro ⟨h0, hsum⟩
    refine ⟨fun a ha => ?_, hsum⟩
    have h1 : 1 ≤ a := by
      rcases Nat.eq_zero_or_pos a with rfl | h
      · exact absurd ha h0
      · exact h
    have h2 : a ≤ n := by
      rw [← hsum]; exact Finset.single_le_sum (f := fun i => i) (fun i _ => Nat.zero_le i) ha
    simp [Finset.mem_Icc, h1, h2]

lemma card_Ico1 (k : ℕ) : (Finset.Ico k (2 * k)).card = k := by
  rw [Nat.card_Ico]; omega

lemma card_Ico2 (k : ℕ) : (Finset.Ico (k + 1) (2 * k + 1)).card = k := by
  rw [Nat.card_Ico]; omega

lemma sum_Ico1 (k : ℕ) : 2 * (∑ i ∈ Finset.Ico k (2 * k), i) + k = 3 * k * k := by
  have h3 : (∑ i ∈ Finset.range k, i) + ∑ i ∈ Finset.Ico k (2 * k), i
      = ∑ i ∈ Finset.range (2 * k), i := by
    simp only [Finset.range_eq_Ico]
    exact Finset.sum_Ico_consecutive _ (Nat.zero_le _) (by omega)
  have h1 : (∑ i ∈ Finset.range k, i) * 2 = k * (k - 1) := Finset.sum_range_id_mul_two k
  have h2 : (∑ i ∈ Finset.range (2 * k), i) * 2 = (2 * k) * (2 * k - 1) :=
    Finset.sum_range_id_mul_two (2 * k)
  rcases Nat.eq_zero_or_pos k with rfl | hk
  · simp
  · obtain ⟨t, rfl⟩ : ∃ t, k = t + 1 := ⟨k - 1, by omega⟩
    have e1 : (t + 1) - 1 = t := by omega
    have e2 : 2 * (t + 1) - 1 = 2 * t + 1 := by omega
    rw [e1] at h1
    rw [e2] at h2
    nlinarith [h1, h2, h3]

lemma sum_Ico2 (k : ℕ) : 2 * (∑ i ∈ Finset.Ico (k + 1) (2 * k + 1), i) = 3 * k * k + k := by
  have h3 : (∑ i ∈ Finset.range (k + 1), i) + ∑ i ∈ Finset.Ico (k + 1) (2 * k + 1), i
      = ∑ i ∈ Finset.range (2 * k + 1), i := by
    simp only [Finset.range_eq_Ico]
    exact Finset.sum_Ico_consecutive _ (Nat.zero_le _) (by omega)
  have h1 : (∑ i ∈ Finset.range (k + 1), i) * 2 = (k + 1) * k := by
    have := Finset.sum_range_id_mul_two (k + 1)
    simpa using this
  have h2 : (∑ i ∈ Finset.range (2 * k + 1), i) * 2 = (2 * k + 1) * (2 * k) := by
    have := Finset.sum_range_id_mul_two (2 * k + 1)
    simpa using this
  nlinarith [h1, h2, h3]

lemma pentSet_ofNat {k : ℕ} (hk : 1 ≤ k) : pentSet (k : ℤ) = Finset.Ico k (2 * k) := by
  rw [pentSet, if_pos (by positivity)]
  norm_num

lemma pentSet_neg {k : ℕ} (hk : 1 ≤ k) :
    pentSet (-(k : ℤ)) = Finset.Ico (k + 1) (2 * k + 1) := by
  rw [pentSet, if_neg (by omega)]
  norm_num

lemma pentIdxOf_Ico1 {k : ℕ} (hk : 1 ≤ k) : pentIdxOf (Finset.Ico k (2 * k)) = (k : ℤ) := by
  rw [pentIdxOf, card_Ico1, if_neg (by omega), if_pos (mnf_Ico (by omega : k < 2 * k))]

lemma pentIdxOf_Ico2 {k : ℕ} (hk : 1 ≤ k) :
    pentIdxOf (Finset.Ico (k + 1) (2 * k + 1)) = -(k : ℤ) := by
  rw [pentIdxOf, card_Ico2, if_neg (by omega),
    if_neg (by rw [mnf_Ico (by omega : k + 1 < 2 * k + 1)]; omega)]



lemma mem_F_iff (n : ℕ) (hn : 1 ≤ n) (s : Finset ℕ) :
    s ∈ (distinctParts n).filter (fun s => IsFixed s) ↔
      ∃ k : ℕ, 1 ≤ k ∧ ((s = Finset.Ico k (2 * k) ∧ 2 * n + k = 3 * k * k) ∨
                        (s = Finset.Ico (k + 1) (2 * k + 1) ∧ 2 * n = 3 * k * k + k)) := by
  classical
  simp only [Finset.mem_filter, mem_distinctParts]
  constructor
  · rintro ⟨⟨h0, hsum⟩, hfix⟩
    have hne : s.Nonempty := by
      rcases Finset.eq_empty_or_nonempty s with rfl | h
      · simp at hsum; omega
      · exact h
    have hexc : IsExc s := by
      rcases hfix with rfl | h
      · simp at hsum; omega
      · exact h
    obtain ⟨k, hk, hcase⟩ := (isExc_iff h0 hne).1 hexc
    refine ⟨k, hk, ?_⟩
    rcases hcase with rfl | rfl
    · left
      refine ⟨rfl, ?_⟩
      have := sum_Ico1 k
      omega
    · right
      refine ⟨rfl, ?_⟩
      have := sum_Ico2 k
      omega
  · rintro ⟨k, hk, ⟨rfl, harith⟩ | ⟨rfl, harith⟩⟩
    · have h0 : (0 : ℕ) ∉ Finset.Ico k (2 * k) := zero_not_mem_Ico hk
      have hne : (Finset.Ico k (2 * k)).Nonempty := ⟨k, Finset.mem_Ico.2 ⟨le_refl _, by omega⟩⟩
      refine ⟨⟨h0, ?_⟩, Or.inr ((isExc_iff h0 hne).2 ⟨k, hk, Or.inl rfl⟩)⟩
      have := sum_Ico1 k
      omega
    · have h0 : (0 : ℕ) ∉ Finset.Ico (k + 1) (2 * k + 1) := zero_not_mem_Ico (by omega)
      have hne : (Finset.Ico (k + 1) (2 * k + 1)).Nonempty :=
        ⟨k + 1, Finset.mem_Ico.2 ⟨le_refl _, by omega⟩⟩
      refine ⟨⟨h0, ?_⟩, Or.inr ((isExc_iff h0 hne).2 ⟨k, hk, Or.inr rfl⟩)⟩
      have := sum_Ico2 k
      omega

lemma mem_pentIdx_iff (n : ℕ) (hn : 1 ≤ n) (k : ℤ) :
    k ∈ pentIdx n ↔ ∃ j : ℕ, 1 ≤ j ∧ ((k = (j : ℤ) ∧ 2 * n + j = 3 * j * j) ∨
                                        (k = -(j : ℤ) ∧ 2 * n = 3 * j * j + j)) := by
  classical
  simp only [pentIdx, Finset.mem_filter, Finset.mem_Icc]
  constructor
  · rintro ⟨⟨hlo, hhi⟩, heq⟩
    have hk0 : k ≠ 0 := by
      intro h
      rw [h] at heq
      simp at heq
      omega
    rcases lt_or_gt_of_ne hk0 with hneg | hpos
    · refine ⟨k.natAbs, by omega, Or.inr ⟨by omega, ?_⟩⟩
      have hkk : k = -(k.natAbs : ℤ) := by omega
      have : 2 * (n : ℤ) = 3 * (k.natAbs : ℤ) * (k.natAbs : ℤ) + (k.natAbs : ℤ) := by
        rw [hkk] at heq; linarith [heq]
      exact_mod_cast this
    · refine ⟨k.toNat, by omega, Or.inl ⟨by omega, ?_⟩⟩
      have hkk : k = (k.toNat : ℤ) := by omega
      have : 2 * (n : ℤ) + (k.toNat : ℤ) = 3 * (k.toNat : ℤ) * (k.toNat : ℤ) := by
        rw [hkk] at heq; linarith [heq]
      exact_mod_cast this
  · rintro ⟨j, hj, ⟨rfl, harith⟩ | ⟨rfl, harith⟩⟩
    · have harith' : 2 * (n : ℤ) + (j : ℤ) = 3 * (j : ℤ) * (j : ℤ) := by exact_mod_cast harith
      have hjn : (j : ℤ) ≤ (n : ℤ) := by nlinarith [harith', (by exact_mod_cast hj : (1:ℤ) ≤ (j:ℤ))]
      exact ⟨⟨by omega, hjn⟩, by linarith⟩
    · have harith' : 2 * (n : ℤ) = 3 * (j : ℤ) * (j : ℤ) + (j : ℤ) := by exact_mod_cast harith
      have hjn : (j : ℤ) ≤ (n : ℤ) := by nlinarith [harith', (by exact_mod_cast hj : (1:ℤ) ≤ (j:ℤ))]
      exact ⟨⟨by omega, by omega⟩, by linarith⟩



lemma pentagonalSign_eq (n : ℕ) : pentagonalSign n = ∑ k ∈ pentIdx n, (-1 : ℤ) ^ k.natAbs := by
  rw [pentagonalSign, pentIdx, Finset.sum_filter]

lemma sum_fixed (n : ℕ) :
    ∑ s ∈ (distinctParts n).filter (fun s => IsFixed s), (-1 : ℤ) ^ s.card
      = pentagonalSign n := by
  classical
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · have h : (distinctParts 0).filter (fun s => IsFixed s) = {∅} := by
      ext s
      simp only [Finset.mem_filter, mem_distinctParts, Finset.mem_singleton]
      constructor
      · rintro ⟨⟨h0, hsum⟩, -⟩
        by_contra hcon
        obtain ⟨a, ha⟩ := Finset.nonempty_iff_ne_empty.2 hcon
        have hle : a ≤ 0 := by
          rw [← hsum]
          exact Finset.single_le_sum (f := fun i => i) (fun i _ => Nat.zero_le i) ha
        exact h0 (by simpa [Nat.le_zero.1 hle] using ha)
      · rintro rfl
        exact ⟨⟨by simp, by simp⟩, Or.inl rfl⟩
    rw [h, pentagonalSign_eq]
    have h2 : pentIdx 0 = {(0 : ℤ)} := by
      ext k
      simp only [pentIdx, Finset.mem_filter, Finset.mem_Icc, Finset.mem_singleton]
      constructor
      · rintro ⟨-, heq⟩
        have h0 : k * (3 * k - 1) = 0 := by push_cast at heq; linarith
        rcases mul_eq_zero.1 h0 with h | h
        · exact h
        · omega
      · rintro rfl
        norm_num
    rw [h2]
    simp
  · rw [pentagonalSign_eq]
    refine Finset.sum_nbij' pentIdxOf pentSet ?_ ?_ ?_ ?_ ?_
    · intro s hs
      obtain ⟨k, hk, hc⟩ := (mem_F_iff n hn s).1 hs
      rcases hc with ⟨rfl, ha⟩ | ⟨rfl, ha⟩
      · rw [pentIdxOf_Ico1 hk]
        exact (mem_pentIdx_iff n hn _).2 ⟨k, hk, Or.inl ⟨rfl, ha⟩⟩
      · rw [pentIdxOf_Ico2 hk]
        exact (mem_pentIdx_iff n hn _).2 ⟨k, hk, Or.inr ⟨rfl, ha⟩⟩
    · intro k hk
      obtain ⟨j, hj1, hc⟩ := (mem_pentIdx_iff n hn k).1 hk
      rcases hc with ⟨rfl, ha⟩ | ⟨rfl, ha⟩
      · rw [pentSet_ofNat hj1]
        exact (mem_F_iff n hn _).2 ⟨j, hj1, Or.inl ⟨rfl, ha⟩⟩
      · rw [pentSet_neg hj1]
        exact (mem_F_iff n hn _).2 ⟨j, hj1, Or.inr ⟨rfl, ha⟩⟩
    · intro s hs
      obtain ⟨k, hk, hc⟩ := (mem_F_iff n hn s).1 hs
      rcases hc with ⟨rfl, ha⟩ | ⟨rfl, ha⟩
      · rw [pentIdxOf_Ico1 hk, pentSet_ofNat hk]
      · rw [pentIdxOf_Ico2 hk, pentSet_neg hk]
    · intro k hk
      obtain ⟨j, hj1, hc⟩ := (mem_pentIdx_iff n hn k).1 hk
      rcases hc with ⟨rfl, ha⟩ | ⟨rfl, ha⟩
      · rw [pentSet_ofNat hj1, pentIdxOf_Ico1 hj1]
      · rw [pentSet_neg hj1, pentIdxOf_Ico2 hj1]
    · intro s hs
      obtain ⟨k, hk, hc⟩ := (mem_F_iff n hn s).1 hs
      rcases hc with ⟨rfl, ha⟩ | ⟨rfl, ha⟩
      · rw [pentIdxOf_Ico1 hk, card_Ico1]
        simp
      · rw [pentIdxOf_Ico2 hk, card_Ico2]
        simp

lemma sum_not_fixed (n : ℕ) :
    ∑ s ∈ (distinctParts n).filter (fun s => ¬ IsFixed s), (-1 : ℤ) ^ s.card = 0 := by
  classical
  refine Finset.sum_involution (fun s _ => franklin s) ?_ ?_ ?_ ?_
  · intro a ha
    simp only [Finset.mem_filter, mem_distinctParts, IsFixed, not_or] at ha
    obtain ⟨⟨h0, hsum⟩, hne0, hexc⟩ := ha
    have hne : a.Nonempty := Finset.nonempty_iff_ne_empty.2 hne0
    rw [franklin_sign h0 hne hexc]; ring
  · intro a ha _
    simp only [Finset.mem_filter, mem_distinctParts, IsFixed, not_or] at ha
    obtain ⟨⟨h0, hsum⟩, hne0, hexc⟩ := ha
    have hne : a.Nonempty := Finset.nonempty_iff_ne_empty.2 hne0
    intro hcon
    have h := franklin_sign h0 hne hexc
    simp only at hcon
    rw [hcon] at h
    have hp : (-1 : ℤ) ^ a.card ≠ 0 := by positivity
    exact hp (by linarith)
  · intro a ha
    simp only [Finset.mem_filter, mem_distinctParts, IsFixed, not_or] at ha ⊢
    obtain ⟨⟨h0, hsum⟩, hne0, hexc⟩ := ha
    have hne : a.Nonempty := Finset.nonempty_iff_ne_empty.2 hne0
    refine ⟨⟨franklin_zero_not_mem h0 hne hexc, by rw [franklin_sum h0 hne hexc, hsum]⟩,
      Finset.nonempty_iff_ne_empty.1 franklin_nonempty,
      franklin_not_exc h0 hne hexc⟩
  · intro a ha
    simp only [Finset.mem_filter, mem_distinctParts, IsFixed, not_or] at ha
    obtain ⟨⟨h0, hsum⟩, hne0, hexc⟩ := ha
    have hne : a.Nonempty := Finset.nonempty_iff_ne_empty.2 hne0
    exact franklin_franklin h0 hne hexc

lemma sum_distinctParts (n : ℕ) :
    ∑ s ∈ distinctParts n, (-1 : ℤ) ^ s.card = pentagonalSign n := by
  classical
  rw [← Finset.sum_filter_add_sum_filter_not (distinctParts n) (fun s => IsFixed s),
    sum_fixed n, sum_not_fixed n, add_zero]

lemma coeff_prod (n N : ℕ) (h : n ≤ N) :
    (PowerSeries.coeff n) (∏ i ∈ Finset.Icc 1 N, (1 - (PowerSeries.X : PowerSeries ℤ) ^ i))
      = ∑ s ∈ distinctParts n, (-1 : ℤ) ^ s.card := by
  classical
  have hprod : (∏ i ∈ Finset.Icc 1 N, (1 - (PowerSeries.X : PowerSeries ℤ) ^ i))
      = ∑ t ∈ (Finset.Icc 1 N).powerset,
          ((-1 : ℤ) ^ t.card) • ((PowerSeries.X : PowerSeries ℤ) ^ (∑ i ∈ t, i)) := by
    have hrw : ∀ i, (1 - (PowerSeries.X : PowerSeries ℤ) ^ i)
        = (-(PowerSeries.X : PowerSeries ℤ) ^ i) + 1 := by
      intro i; ring
    simp only [hrw]
    rw [Finset.prod_add]
    refine Finset.sum_congr rfl ?_
    intro t _
    simp only [Finset.prod_const_one, mul_one]
    rw [Finset.prod_neg, Finset.prod_pow_eq_pow_sum, zsmul_eq_mul]
    push_cast; ring
  rw [hprod, map_sum]
  simp only [map_smul, PowerSeries.coeff_X_pow, smul_eq_mul, mul_ite, mul_one, mul_zero]
  rw [← Finset.sum_filter]
  refine Finset.sum_congr ?_ (fun _ _ => rfl)
  ext x
  simp only [Finset.mem_filter, Finset.mem_powerset, mem_distinctParts]
  constructor
  · rintro ⟨hsub, hsum⟩
    refine ⟨fun h0 => ?_, hsum.symm⟩
    have := hsub h0; simp at this
  · rintro ⟨h0, hsum⟩
    refine ⟨fun a ha => ?_, hsum.symm⟩
    have h1 : 1 ≤ a := by
      rcases Nat.eq_zero_or_pos a with rfl | hp
      · exact absurd ha h0
      · exact hp
    have h2 : a ≤ n := by
      rw [← hsum]; exact Finset.single_le_sum (f := fun i => i) (fun i _ => Nat.zero_le i) ha
    simp only [Finset.mem_Icc, h1, true_and]
    omega

/-- **Euler's pentagonal number theorem**. For `n ≤ N`, the coefficient of `q^n` in the
product `∏_{i=1}^N (1 - q^i)` equals `∑_{k ∈ ℤ} (-1)^k [n = k(3k-1)/2]`. -/
theorem euler_pentagonal (n N : ℕ) (h : n ≤ N) :
    (PowerSeries.coeff n) (∏ i ∈ Finset.Icc 1 N, (1 - (PowerSeries.X : PowerSeries ℤ) ^ i))
      = ∑ k ∈ Finset.Icc (-(n : ℤ)) (n : ℤ),
          if 2 * (n : ℤ) = k * (3 * k - 1) then (-1 : ℤ) ^ k.natAbs else 0 := by
  rw [coeff_prod n N h, sum_distinctParts n]
  rfl

end Math

#print axioms Math.euler_pentagonal

