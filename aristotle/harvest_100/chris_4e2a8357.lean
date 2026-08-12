import RequestProject.HuffmanKraft

/-!
# Weighted depth multisets, the Huffman merging process, and the optimality bound
-/

namespace CS

/-- A *weighted depth multiset*: a finite multiset of pairs `(weight, codeword length)`. -/
abbrev WD := Multiset (ℝ × ℕ)

/-- The expected codeword length associated to a weighted depth multiset. -/
noncomputable def cost (D : WD) : ℝ := (D.map fun p => p.1 * (p.2 : ℝ)).sum

/-- The Kraft sum of a weighted depth multiset. -/
noncomputable def kraft (D : WD) : ℝ := (D.map fun p => (1 / 2 : ℝ) ^ p.2).sum

/-- The multiset of weights. -/
def wts (D : WD) : Multiset ℝ := D.map Prod.fst

/-- The multiset of codeword lengths. -/
def dps (D : WD) : Multiset ℕ := D.map Prod.snd

@[simp] theorem cost_zero : cost 0 = 0 := by simp [cost]
@[simp] theorem kraft_zero : kraft 0 = 0 := by simp [kraft]
@[simp] theorem wts_zero : wts 0 = 0 := by simp [wts]
@[simp] theorem dps_zero : dps 0 = 0 := by simp [dps]

@[simp] theorem cost_cons (p : ℝ × ℕ) (D : WD) :
    cost (p ::ₘ D) = p.1 * (p.2 : ℝ) + cost D := by simp [cost]
@[simp] theorem kraft_cons (p : ℝ × ℕ) (D : WD) :
    kraft (p ::ₘ D) = (1 / 2 : ℝ) ^ p.2 + kraft D := by simp [kraft]
@[simp] theorem wts_cons (p : ℝ × ℕ) (D : WD) : wts (p ::ₘ D) = p.1 ::ₘ wts D := by simp [wts]
@[simp] theorem dps_cons (p : ℝ × ℕ) (D : WD) : dps (p ::ₘ D) = p.2 ::ₘ dps D := by simp [dps]

theorem card_wts (D : WD) : (wts D).card = D.card := by simp [wts]

theorem cost_nonneg {D : WD} (h : ∀ p ∈ D, 0 ≤ p.1) : 0 ≤ cost D := by
  refine Multiset.sum_nonneg ?_
  intro x hx
  obtain ⟨p, hp, rfl⟩ := Multiset.mem_map.1 hx
  exact mul_nonneg (h p hp) (Nat.cast_nonneg _)

/-- Existence of a maximal element of a nonempty multiset in a linear order. -/
theorem exists_max_mem {α : Type*} [LinearOrder α] (s : Multiset α) (hs : s ≠ 0) :
    ∃ m ∈ s, ∀ x ∈ s, x ≤ m := by
  induction s using Multiset.induction with
  | empty => exact absurd rfl hs
  | cons a s ih =>
    rcases eq_or_ne s 0 with rfl | hne
    · exact ⟨a, by simp, by simp⟩
    · obtain ⟨m, hm, hmax⟩ := ih hne
      rcases le_total a m with hle | hle
      · refine ⟨m, Multiset.mem_cons_of_mem hm, ?_⟩
        intro x hx
        rcases Multiset.mem_cons.1 hx with rfl | hx
        · exact hle
        · exact hmax x hx
      · refine ⟨a, Multiset.mem_cons_self _ _, ?_⟩
        intro x hx
        rcases Multiset.mem_cons.1 hx with rfl | hx
        · exact le_refl _
        · exact le_trans (hmax x hx) hle

/-- Existence of a minimal element of a nonempty multiset in a linear order. -/
theorem exists_min_mem {α : Type*} [LinearOrder α] (s : Multiset α) (hs : s ≠ 0) :
    ∃ m ∈ s, ∀ x ∈ s, m ≤ x := by
  induction s using Multiset.induction with
  | empty => exact absurd rfl hs
  | cons a s ih =>
    rcases eq_or_ne s 0 with rfl | hne
    · exact ⟨a, by simp, by simp⟩
    · obtain ⟨m, hm, hmin⟩ := ih hne
      rcases le_total a m with hle | hle
      · refine ⟨a, Multiset.mem_cons_self _ _, ?_⟩
        intro x hx
        rcases Multiset.mem_cons.1 hx with rfl | hx
        · exact le_refl _
        · exact le_trans hle (hmin x hx)
      · refine ⟨m, Multiset.mem_cons_of_mem hm, ?_⟩
        intro x hx
        rcases Multiset.mem_cons.1 hx with rfl | hx
        · exact hle
        · exact hmin x hx

/-- The Kraft sum scaled by `2 ^ M`, as a natural number. -/
def kn (M : ℕ) (D : WD) : ℕ := (D.map fun p => 2 ^ (M - p.2)).sum

@[simp] theorem kn_zero (M : ℕ) : kn M 0 = 0 := by simp [kn]
@[simp] theorem kn_cons (M : ℕ) (p : ℝ × ℕ) (D : WD) :
    kn M (p ::ₘ D) = 2 ^ (M - p.2) + kn M D := by simp [kn]

theorem kraft_eq_kn (M : ℕ) (D : WD) (h : ∀ p ∈ D, p.2 ≤ M) :
    kraft D * 2 ^ M = (kn M D : ℝ) := by
  induction D using Multiset.induction with
  | empty => simp
  | cons a D ih =>
    have ha : a.2 ≤ M := h a (Multiset.mem_cons_self _ _)
    have ih' := ih fun p hp => h p (Multiset.mem_cons_of_mem hp)
    have hsplit : (2 : ℝ) ^ M = 2 ^ (M - a.2) * 2 ^ a.2 := by
      rw [← pow_add]; congr 1; omega
    rw [kn_cons, kraft_cons, add_mul, ih']
    push_cast
    rw [hsplit]
    have : (1 / 2 : ℝ) ^ a.2 * (2 ^ (M - a.2) * 2 ^ a.2) = 2 ^ (M - a.2) := by
      rw [mul_comm ((2:ℝ) ^ (M - a.2)), ← mul_assoc, ← mul_pow]
      norm_num
    rw [this]

theorem kn_parity (M : ℕ) (D : WD) (h : ∀ p ∈ D, p.2 ≤ M) :
    ∃ t : ℕ, kn M D = D.countP (fun p => p.2 = M) + 2 * t := by
  classical
  induction D using Multiset.induction with
  | empty => exact ⟨0, by simp⟩
  | cons a D ih =>
    obtain ⟨t, ht⟩ := ih fun p hp => h p (Multiset.mem_cons_of_mem hp)
    have ha : a.2 ≤ M := h a (Multiset.mem_cons_self _ _)
    rw [Multiset.countP_cons, kn_cons, ht]
    by_cases hd : a.2 = M
    · refine ⟨t, ?_⟩
      simp [hd]
      omega
    · have h1 : 1 ≤ M - a.2 := by omega
      obtain ⟨k, hk⟩ : ∃ k, M - a.2 = k + 1 := ⟨M - a.2 - 1, by omega⟩
      refine ⟨2 ^ k + t, ?_⟩
      simp only [hd, if_false, hk, pow_succ]
      ring_nf

/-- From a multiset with at least two elements satisfying `P`, extract two such elements. -/
theorem exists_two_of_countP {P : ℝ × ℕ → Prop} [DecidablePred P] {D : WD}
    (h : 2 ≤ D.countP P) : ∃ p q D₀, P p ∧ P q ∧ D = p ::ₘ q ::ₘ D₀ := by
  rw [Multiset.countP_eq_card_filter] at h
  obtain ⟨p, hp⟩ := (Multiset.card_pos_iff_exists_mem (s := D.filter P)).1 (by omega)
  have hcard2 : 0 < ((D.filter P).erase p).card := by
    rw [Multiset.card_erase_of_mem hp]; omega
  obtain ⟨q, hq⟩ := (Multiset.card_pos_iff_exists_mem (s := (D.filter P).erase p)).1 hcard2
  have hpD : p ∈ D := Multiset.mem_of_mem_filter hp
  have hPp : P p := Multiset.of_mem_filter hp
  have hPq : P q := Multiset.of_mem_filter (Multiset.mem_of_mem_erase hq)
  have hqD : q ∈ D.erase p :=
    Multiset.mem_of_le (Multiset.erase_le_erase p (Multiset.filter_le P D)) hq
  refine ⟨p, q, (D.erase p).erase q, hPp, hPq, ?_⟩
  rw [Multiset.cons_erase hqD, Multiset.cons_erase hpD]

theorem kraft_of_depths_zero {D : WD} (h : ∀ p ∈ D, p.2 = 0) : kraft D = D.card := by
  induction D using Multiset.induction with
  | empty => simp
  | cons a D ih =>
    rw [kraft_cons, h a (Multiset.mem_cons_self _ _),
      ih fun p hp => h p (Multiset.mem_cons_of_mem hp)]
    simp
    ring

/-- If the Kraft sum equals `1` and the maximal length `M` is positive, then at least two
codewords have length `M`. -/
theorem two_le_count_max {D : WD} {M : ℕ} (hmax : ∀ p ∈ D, p.2 ≤ M) (hM : 1 ≤ M)
    (hk : kraft D = 1) (hex : ∃ p ∈ D, p.2 = M) :
    2 ≤ D.countP (fun p => p.2 = M) := by
  classical
  obtain ⟨t, ht⟩ := kn_parity M D hmax
  have h1 : kraft D * 2 ^ M = (kn M D : ℝ) := kraft_eq_kn M D hmax
  rw [hk, one_mul] at h1
  have h2 : kn M D = 2 ^ M := by exact_mod_cast h1.symm
  have hpos : 0 < D.countP (fun p => p.2 = M) := by
    obtain ⟨p, hp, hpM⟩ := hex
    rw [Multiset.countP_pos]; exact ⟨p, hp, hpM⟩
  obtain ⟨k, rfl⟩ : ∃ k, M = k + 1 := ⟨M - 1, by omega⟩
  have hdvd : 2 ∣ kn (k + 1) D := ⟨2 ^ k, by rw [h2, pow_succ]; ring⟩
  omega

/-- Any weighted depth multiset with Kraft sum `≤ 1` can be replaced by one with the same
weights, Kraft sum exactly `1`, and no larger cost. -/
theorem normalize_aux : ∀ (n : ℕ) (D : WD), (dps D).sum = n → (∀ p ∈ D, 0 ≤ p.1) → D ≠ 0 →
    kraft D ≤ 1 → ∃ D' : WD, wts D' = wts D ∧ kraft D' = 1 ∧ cost D' ≤ cost D := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro D hsum hw hD hk
    rcases eq_or_lt_of_le hk with heq | hlt
    · exact ⟨D, rfl, heq, le_refl _⟩
    obtain ⟨M, hM, hMmax⟩ := exists_max_mem (dps D) (by simpa [dps] using hD)
    have hmax : ∀ q ∈ D, q.2 ≤ M := fun q hq => hMmax q.2 (Multiset.mem_map_of_mem _ hq)
    obtain ⟨p, hp, hpM⟩ := Multiset.mem_map.1 hM
    rcases Nat.eq_zero_or_pos M with hM0 | hM1
    · exfalso
      have hz : ∀ q ∈ D, q.2 = 0 := fun q hq => Nat.le_zero.1 (hM0 ▸ hmax q hq)
      rw [kraft_of_depths_zero hz] at hlt
      have h1 : 1 ≤ D.card := Multiset.card_pos.2 hD
      have h2 : (1 : ℝ) ≤ (D.card : ℝ) := by exact_mod_cast h1
      linarith
    have hnum : kraft D * 2 ^ M = (kn M D : ℝ) := kraft_eq_kn M D hmax
    have hpow : (0 : ℝ) < 2 ^ M := by positivity
    have hlt' : (kn M D : ℝ) < 2 ^ M := by
      rw [← hnum]
      calc kraft D * 2 ^ M < 1 * 2 ^ M := mul_lt_mul_of_pos_right hlt hpow
        _ = 2 ^ M := one_mul _
    have hknle : kn M D + 1 ≤ 2 ^ M := by
      have : kn M D < 2 ^ M := by exact_mod_cast hlt'
      omega
    have hbound : kraft D + (1 / 2 : ℝ) ^ M ≤ 1 := by
      have h1 : (kn M D : ℝ) + 1 ≤ 2 ^ M := by exact_mod_cast hknle
      have h2 : kraft D * 2 ^ M + 1 ≤ 2 ^ M := by rw [hnum]; exact h1
      have h3 : (1 / 2 : ℝ) ^ M = 1 / 2 ^ M := by rw [div_pow, one_pow]
      rw [h3, ← sub_nonneg]
      have h4 : 1 - (kraft D + 1 / 2 ^ M) = (2 ^ M - kraft D * 2 ^ M - 1) / 2 ^ M := by
        field_simp
        ring
      rw [h4]
      apply div_nonneg _ (le_of_lt hpow)
      linarith
    set E : WD := D.erase p with hE
    have hDeq : D = p ::ₘ E := (Multiset.cons_erase hp).symm
    set D' : WD := (p.1, M - 1) ::ₘ E with hD'
    have hcastM : ((M - 1 : ℕ) : ℝ) = (M : ℝ) - 1 := by
      have h1 : (1 : ℕ) ≤ M := hM1
      push_cast [Nat.cast_sub h1]
      ring
    have hkraftE : kraft D = (1 / 2 : ℝ) ^ M + kraft E := by
      conv_lhs => rw [hDeq]
      rw [kraft_cons, hpM]
    have hpowsub : (1 / 2 : ℝ) ^ (M - 1) = 2 * (1 / 2 : ℝ) ^ M := by
      obtain ⟨k, rfl⟩ : ∃ k, M = k + 1 := ⟨M - 1, by omega⟩
      simp [pow_succ]
      ring
    have hkD' : kraft D' = kraft D + (1 / 2 : ℝ) ^ M := by
      rw [hD', kraft_cons, hpowsub, hkraftE]
      ring
    have hcostD' : cost D' ≤ cost D := by
      have hcD : cost D = p.1 * (M : ℝ) + cost E := by
        conv_lhs => rw [hDeq]
        rw [cost_cons, hpM]
      rw [hD', cost_cons, hcD, hcastM]
      have hp1 : 0 ≤ p.1 := hw p hp
      nlinarith
    have hwD' : wts D' = wts D := by
      conv_rhs => rw [hDeq]
      rw [hD', wts_cons, wts_cons]
    have hsum' : (dps D').sum < n := by
      have h1 : (dps D).sum = M + (dps E).sum := by
        conv_lhs => rw [hDeq]
        rw [dps_cons, Multiset.sum_cons, hpM]
      have h2 : (dps D').sum = (M - 1) + (dps E).sum := by
        rw [hD', dps_cons, Multiset.sum_cons]
      omega
    obtain ⟨D'', hw'', hk'', hc''⟩ := ih _ hsum' D' rfl
      (by
        intro q hq
        rcases Multiset.mem_cons.1 hq with rfl | hq
        · exact hw p hp
        · exact hw q (by rw [hDeq]; exact Multiset.mem_cons_of_mem hq))
      (by simp [hD'])
      (by rw [hkD']; exact hbound)
    exact ⟨D'', by rw [hw'', hwD'], hk'', le_trans hc'' hcostD'⟩

theorem normalize (D : WD) (hw : ∀ p ∈ D, 0 ≤ p.1) (hD : D ≠ 0) (hk : kraft D ≤ 1) :
    ∃ D' : WD, wts D' = wts D ∧ kraft D' = 1 ∧ cost D' ≤ cost D :=
  normalize_aux _ D rfl hw hD hk

end CS

import Mathlib

/-!
# Kraft's inequality for finite prefix-free codes

A finite list of binary codewords is *prefix-free* if no codeword is a prefix of another.
For such a list, `∑ (1/2)^(length u) ≤ 1`.
-/

namespace CS

open scoped BigOperators

/-- A list of binary codewords is prefix-free if no codeword is a prefix of another one.
Note that this forces the codewords to be pairwise distinct. -/
def PrefixFree (cs : List (List Bool)) : Prop :=
  cs.Pairwise fun u v => ¬ u <+: v ∧ ¬ v <+: u

theorem PrefixFree.nodup {cs : List (List Bool)} (h : PrefixFree cs) : cs.Nodup := by
  refine List.Pairwise.imp (fun {a b} hab => ?_) h
  rintro rfl
  exact hab.1 (List.prefix_refl a)

theorem PrefixFree.symm : Symmetric fun u v : List Bool => ¬ u <+: v ∧ ¬ v <+: u :=
  fun _ _ hxy => ⟨hxy.2, hxy.1⟩

/-- The finset of all boolean lists of length `n`. -/
def allLists : ℕ → Finset (List Bool)
  | 0 => {[]}
  | n + 1 => Finset.image (fun p : Bool × List Bool => p.1 :: p.2)
      (Finset.univ ×ˢ allLists n)

theorem mem_allLists {n : ℕ} {x : List Bool} : x ∈ allLists n ↔ x.length = n := by
  induction n generalizing x with
  | zero => simp [allLists, List.length_eq_zero_iff]
  | succ n ih =>
    simp only [allLists, Finset.mem_image, Finset.mem_product, Finset.mem_univ, true_and,
      Prod.exists]
    constructor
    · rintro ⟨b, l, hl, rfl⟩
      simp [ih.1 hl]
    · intro hx
      cases x with
      | nil => simp at hx
      | cons b l => exact ⟨b, l, ih.2 (by simpa using hx), rfl⟩

theorem card_allLists (n : ℕ) : (allLists n).card = 2 ^ n := by
  induction n with
  | zero => simp [allLists]
  | succ n ih =>
    rw [allLists, Finset.card_image_of_injective _ (by
      rintro ⟨b, l⟩ ⟨b', l'⟩ h
      simp only [List.cons.injEq] at h
      simp [h.1, h.2])]
    simp [ih, pow_succ, mul_comm]

/-- The finset of extensions of `u` to a word of length `M`. -/
def exts (M : ℕ) (u : List Bool) : Finset (List Bool) :=
  (allLists M).filter (fun x => u <+: x)

theorem card_exts {M : ℕ} {u : List Bool} (h : u.length ≤ M) :
    (exts M u).card = 2 ^ (M - u.length) := by
  have himg : exts M u = (allLists (M - u.length)).image (fun y => u ++ y) := by
    ext x
    simp only [exts, Finset.mem_filter, mem_allLists, Finset.mem_image]
    constructor
    · rintro ⟨hx, hpre⟩
      obtain ⟨t, rfl⟩ := hpre
      refine ⟨t, ?_, rfl⟩
      simp only [List.length_append] at hx
      omega
    · rintro ⟨y, hy, rfl⟩
      refine ⟨?_, ⟨y, rfl⟩⟩
      simp only [List.length_append]
      omega
  rw [himg, Finset.card_image_of_injective _ (fun a b hab => List.append_cancel_left hab),
    card_allLists]

/-- Kraft's inequality: for a prefix-free list of binary codewords,
`∑ (1/2)^(length u) ≤ 1`. -/
theorem kraft_inequality (cs : List (List Bool)) (h : PrefixFree cs) :
    (cs.map fun u => (1 / 2 : ℝ) ^ u.length).sum ≤ 1 := by
  classical
  obtain ⟨M, hM⟩ : ∃ M, ∀ u ∈ cs, u.length ≤ M := by
    induction cs with
    | nil => exact ⟨0, by simp⟩
    | cons a l ih =>
      obtain ⟨M, hM⟩ := ih h.of_cons
      exact ⟨max M a.length, by
        intro u hu
        rcases List.mem_cons.1 hu with rfl | hu
        · exact le_max_right _ _
        · exact le_trans (hM u hu) (le_max_left _ _)⟩
  have hnd : cs.Nodup := h.nodup
  have hpair := h.forall PrefixFree.symm
  -- the extension sets are pairwise disjoint
  have hdisj : (cs.toFinset : Set (List Bool)).PairwiseDisjoint (exts M) := by
    intro u hu v hv huv
    simp only [Finset.mem_coe, List.mem_toFinset] at hu hv
    rw [Function.onFun, Finset.disjoint_left]
    rintro x hx hx'
    simp only [exts, Finset.mem_filter] at hx hx'
    rcases List.prefix_or_prefix_of_prefix hx.2 hx'.2 with hc | hc
    · exact (hpair hu hv huv).1 hc
    · exact (hpair hu hv huv).2 hc
  have hcard : ∑ u ∈ cs.toFinset, (exts M u).card ≤ 2 ^ M := by
    rw [← Finset.card_biUnion hdisj]
    calc (cs.toFinset.biUnion (exts M)).card ≤ (allLists M).card :=
          Finset.card_le_card (by
            intro x hx
            simp only [Finset.mem_biUnion] at hx
            obtain ⟨u, _, hu⟩ := hx
            exact (Finset.mem_filter.1 hu).1)
      _ = 2 ^ M := card_allLists M
  have key : ∀ u ∈ cs.toFinset, (1 / 2 : ℝ) ^ u.length = ((exts M u).card : ℝ) / 2 ^ M := by
    intro u hu
    rw [List.mem_toFinset] at hu
    have hle := hM u hu
    have hsplit : (2 : ℝ) ^ M = 2 ^ (M - u.length) * 2 ^ u.length := by
      rw [← pow_add]; congr 1; omega
    rw [card_exts hle]
    push_cast
    rw [hsplit, eq_div_iff (by positivity), mul_comm ((2:ℝ) ^ (M - u.length)),
      ← mul_assoc, ← mul_pow]
    norm_num
  rw [← List.sum_toFinset _ hnd, Finset.sum_congr rfl key, ← Finset.sum_div,
    div_le_one (by positivity)]
  calc (∑ u ∈ cs.toFinset, ((exts M u).card : ℝ))
      = ((∑ u ∈ cs.toFinset, (exts M u).card : ℕ) : ℝ) := by push_cast; ring
    _ ≤ ((2 ^ M : ℕ) : ℝ) := by exact_mod_cast hcard
    _ = 2 ^ M := by push_cast; ring

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

