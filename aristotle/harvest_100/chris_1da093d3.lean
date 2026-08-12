import RequestProject.Huffman

/-!
# Achievability of the Huffman cost

Companion to `RequestProject.Huffman`.  Here we show that the Huffman cost is *attained*:
there really is a prefix code whose expected codeword length equals `CS.huffCost`.

Combined with the optimality bound `CS.huffman_optimal`, this gives
`CS.huffman_isLeast`: the Huffman cost is the least expected codeword length among all
prefix codes.
-/

namespace CS

open scoped BigOperators

noncomputable section

/-- A multiset of binary codewords is prefix-free: the codewords are pairwise distinct and
none is a prefix of another. -/
def PrefixFreeMultiset (V : Multiset (List Bool)) : Prop :=
  V.Nodup ∧ ∀ u ∈ V, ∀ v ∈ V, u ≠ v → ¬ u <+: v

/-- Expected codeword length of a multiset of (weight, codeword) pairs. -/
noncomputable def codeCost (S : Multiset (ℝ × List Bool)) : ℝ :=
  (S.map fun p => p.1 * (p.2.length : ℝ)).sum

/-- Replacing a codeword `v` of a prefix-free family by its two extensions `v0` and `v1`
again yields a prefix-free family. -/
theorem prefixFree_split (v : List Bool) (V : Multiset (List Bool))
    (h : PrefixFreeMultiset (v ::ₘ V)) :
    PrefixFreeMultiset ((v ++ [false]) ::ₘ (v ++ [true]) ::ₘ V) := by
  obtain ⟨hnd, hpf⟩ := h
  rw [Multiset.nodup_cons] at hnd
  obtain ⟨hvV, hVnd⟩ := hnd
  have hA : ∀ u ∈ V, ¬ (v <+: u) ∧ ¬ (u <+: v) := by
    intro u hu
    have hne : u ≠ v := by rintro rfl; exact hvV hu
    exact ⟨hpf v (Multiset.mem_cons_self _ _) u (Multiset.mem_cons_of_mem hu) (Ne.symm hne),
      hpf u (Multiset.mem_cons_of_mem hu) v (Multiset.mem_cons_self _ _) hne⟩
  have hB : ∀ b : Bool, v ++ [b] ∉ V := by
    intro b hb
    exact (hA _ hb).1 ⟨[b], rfl⟩
  have hne01 : v ++ [false] ≠ v ++ [true] := by simp
  have hkey : ∀ b : Bool, ∀ u ∈ V, ¬ (v ++ [b] <+: u) ∧ ¬ (u <+: v ++ [b]) := by
    intro b u hu
    refine ⟨fun hp => (hA u hu).1 (List.IsPrefix.trans ⟨[b], rfl⟩ hp), fun hp => ?_⟩
    rcases List.prefix_concat_iff.mp hp with h1 | h1
    · exact hB b (h1 ▸ hu)
    · exact (hA u hu).2 h1
  refine ⟨?_, ?_⟩
  · rw [Multiset.nodup_cons, Multiset.nodup_cons]
    refine ⟨?_, hB true, hVnd⟩
    simp only [Multiset.mem_cons]
    push_neg
    exact ⟨hne01, hB false⟩
  · intro u hu w hw hne hpre
    simp only [Multiset.mem_cons] at hu hw
    rcases hu with rfl | rfl | hu
    · rcases hw with rfl | rfl | hw
      · exact hne rfl
      · rw [List.prefix_append_right_inj] at hpre; simp at hpre
      · exact (hkey false w hw).1 hpre
    · rcases hw with rfl | rfl | hw
      · rw [List.prefix_append_right_inj] at hpre; simp at hpre
      · exact hne rfl
      · exact (hkey true w hw).1 hpre
    · rcases hw with rfl | rfl | hw
      · exact (hkey false u hu).2 hpre
      · exact (hkey true u hu).2 hpre
      · exact hpf u (Multiset.mem_cons_of_mem hu) w (Multiset.mem_cons_of_mem hw) hne hpre

/-- The Huffman cost of a multiset of weights is attained by an actual prefix-free code. -/
theorem huffCost_achievable_aux : ∀ n : ℕ, ∀ W : Multiset ℝ, Multiset.card W = n →
    ∃ S : Multiset (ℝ × List Bool), S.map Prod.fst = W ∧
      PrefixFreeMultiset (S.map Prod.snd) ∧ codeCost S = huffCost W := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n IH =>
  intro W hcard
  by_cases hle : Multiset.card W ≤ 1
  · rcases Nat.le_one_iff_eq_zero_or_eq_one.1 hle with h | h
    · refine ⟨0, ?_, ⟨by simp, by simp⟩, ?_⟩
      · simp [Multiset.card_eq_zero.1 h]
      · simp [codeCost, Multiset.card_eq_zero.1 h]
    · obtain ⟨a, ha⟩ := Multiset.card_eq_one.1 h
      refine ⟨{(a, [])}, by simp [ha], ⟨by simp, ?_⟩, by simp [codeCost, ha]⟩
      intro u hu v hv hne
      simp at hu hv
      exact absurd (hu.trans hv.symm) hne
  · push_neg at hle
    have hWne : W ≠ 0 := by intro h; rw [h] at hle; simp at hle
    obtain ⟨x, hxW, hxmin⟩ := exists_min_of_ne_zero W hWne
    obtain ⟨W₁, hW₁⟩ := Multiset.exists_cons_of_mem hxW
    have hW₁ne : W₁ ≠ 0 := by
      intro h; rw [hW₁, h] at hle; simp at hle
    obtain ⟨y, hyW₁, hymin⟩ := exists_min_of_ne_zero W₁ hW₁ne
    obtain ⟨l, hl⟩ := Multiset.exists_cons_of_mem hyW₁
    have hWeq : W = x ::ₘ y ::ₘ l := by rw [hW₁, hl]
    have hxle : ∀ z ∈ l, x ≤ z := by
      intro z hz
      exact hxmin z (by rw [hWeq]; exact Multiset.mem_cons_of_mem (Multiset.mem_cons_of_mem hz))
    have hyle : ∀ z ∈ l, y ≤ z := by
      intro z hz
      exact hymin z (by rw [hl]; exact Multiset.mem_cons_of_mem hz)
    have hcard' : Multiset.card ((x + y) ::ₘ l) < n := by
      rw [← hcard, hWeq]; simp
    obtain ⟨S', hfst', hpf', hcost'⟩ := IH _ hcard' ((x + y) ::ₘ l) rfl
    have hmem : (x + y) ∈ S'.map Prod.fst := by rw [hfst']; exact Multiset.mem_cons_self _ _
    obtain ⟨p, hpS', hp⟩ := Multiset.mem_map.1 hmem
    obtain ⟨R, hR⟩ := Multiset.exists_cons_of_mem hpS'
    have hRfst : R.map Prod.fst = l := by
      have h2 : (x + y) ::ₘ R.map Prod.fst = (x + y) ::ₘ l := by
        rw [← hfst', hR]; simp [hp]
      exact (Multiset.cons_inj_right _).1 h2
    refine ⟨(x, p.2 ++ [false]) ::ₘ (y, p.2 ++ [true]) ::ₘ R, ?_, ?_, ?_⟩
    · simp only [Multiset.map_cons, hRfst]
      exact hWeq.symm
    · simp only [Multiset.map_cons]
      have hS'snd : S'.map Prod.snd = p.2 ::ₘ R.map Prod.snd := by rw [hR]; simp
      rw [hS'snd] at hpf'
      exact prefixFree_split p.2 (R.map Prod.snd) hpf'
    · have hcostS' : codeCost S' = (x + y) * (p.2.length : ℝ) + codeCost R := by
        rw [hR]; simp [codeCost, hp]
      have hhuff : huffCost W = (x + y) + huffCost ((x + y) ::ₘ l) := by
        rw [hWeq]; exact huffCost_cons_cons x y l hxle hyle
      simp only [codeCost, Multiset.map_cons, Multiset.sum_cons, List.length_append,
        List.length_singleton]
      rw [hhuff, ← hcost']
      simp only [codeCost] at hcostS' ⊢
      rw [hcostS']
      push_cast
      ring

/-! ## Turning a multiset solution into an indexed one -/

/-- If a multiset `S` maps onto the multiset of `g`-values of a finite index set, then `S`
can be indexed by that set compatibly with `g`. -/
theorem exists_fun_of_map_eq {α β γ : Type*} [DecidableEq α] [Nonempty β] (f : β → γ)
    (g : α → γ) : ∀ (s : Finset α) (S : Multiset β), S.map f = s.val.map g →
      ∃ h : α → β, s.val.map h = S ∧ ∀ a ∈ s, f (h a) = g a := by
  intro s
  induction s using Finset.cons_induction with
  | empty =>
      intro S hS
      refine ⟨fun _ => Classical.arbitrary β, ?_, by simp⟩
      simp only [Finset.empty_val, Multiset.map_zero] at hS ⊢
      exact (Multiset.map_eq_zero.1 hS).symm
  | cons a s ha ih =>
      intro S hS
      rw [Finset.cons_val, Multiset.map_cons] at hS
      have hga : g a ∈ S.map f := by rw [hS]; exact Multiset.mem_cons_self _ _
      obtain ⟨b, hbS, hb⟩ := Multiset.mem_map.1 hga
      obtain ⟨S₀, hS₀⟩ := Multiset.exists_cons_of_mem hbS
      have hS₀map : S₀.map f = s.val.map g := by
        rw [hS₀, Multiset.map_cons, hb] at hS
        exact (Multiset.cons_inj_right _).1 hS
      obtain ⟨h', hh'1, hh'2⟩ := ih S₀ hS₀map
      refine ⟨Function.update h' a b, ?_, ?_⟩
      · rw [Finset.cons_val, Multiset.map_cons, hS₀]
        congr 1
        · simp
        · rw [← hh'1]
          refine Multiset.map_congr rfl ?_
          intro x hx
          have : x ≠ a := by rintro rfl; exact ha hx
          simp [Function.update_of_ne this]
      · intro c hc
        rcases Finset.mem_cons.1 hc with rfl | hc'
        · simpa using hb
        · have hca : c ≠ a := by rintro rfl; exact ha hc'
          rw [Function.update_of_ne hca]
          exact hh'2 c hc'

/-- **Achievability**: for any finite alphabet with weights there is a prefix code whose
expected codeword length is exactly the Huffman cost. -/
theorem huffman_achievable {α : Type*} [Fintype α] (w : α → ℝ) :
    ∃ c : α → List Bool, IsPrefixCode c ∧
      ∑ a, w a * ((c a).length : ℝ) = huffCost (Multiset.map w Finset.univ.val) := by
  classical
  obtain ⟨S, hfst, hpf, hcost⟩ :=
    huffCost_achievable_aux _ (Multiset.map w Finset.univ.val) rfl
  obtain ⟨h, hh1, hh2⟩ :=
    exists_fun_of_map_eq (β := ℝ × List Bool) Prod.fst w Finset.univ S hfst
  refine ⟨fun a => (h a).2, ?_, ?_⟩
  · -- prefix code
    have hsnd : S.map Prod.snd = Multiset.map (fun a => (h a).2) Finset.univ.val := by
      rw [← hh1, Multiset.map_map]
      rfl
    have hinj : Function.Injective (fun a => (h a).2) := by
      have hnd := hpf.1
      rw [hsnd, Multiset.nodup_map_iff_inj_on Finset.univ.nodup] at hnd
      intro a b hab
      exact hnd a (Finset.mem_univ a) b (Finset.mem_univ b) hab
    intro a b hab hpre
    refine hpf.2 ((h a).2) ?_ ((h b).2) ?_ (fun heq => hab (hinj heq)) hpre
    · rw [hsnd]; exact Multiset.mem_map_of_mem _ (Finset.mem_univ a)
    · rw [hsnd]; exact Multiset.mem_map_of_mem _ (Finset.mem_univ b)
  · rw [← hcost, codeCost, ← hh1, Multiset.map_map, ← Finset.sum_map_val]
    refine Finset.sum_congr rfl ?_
    intro a _
    simp only [Function.comp_apply]
    rw [hh2 a (Finset.mem_univ a)]

/-- **Huffman coding minimizes the expected codeword length among prefix codes**: the
Huffman cost is the least element of the set of expected codeword lengths of prefix codes
over a finite alphabet with nonnegative weights. -/
theorem huffman_isLeast {α : Type*} [Fintype α] (w : α → ℝ) (hw : ∀ a, 0 ≤ w a) :
    IsLeast {r : ℝ | ∃ c : α → List Bool, IsPrefixCode c ∧ ∑ a, w a * ((c a).length : ℝ) = r}
      (huffCost (Multiset.map w Finset.univ.val)) := by
  constructor
  · obtain ⟨c, hc, hcost⟩ := huffman_achievable w
    exact ⟨c, hc, hcost⟩
  · rintro r ⟨c, hc, rfl⟩
    exact huffman_optimal w hw c hc

end

end CS

import Mathlib

/-!
# Optimality of Huffman coding

This file develops, from scratch, a proof that Huffman coding minimizes the expected
codeword length among all prefix (prefix-free) binary codes.

The development has three parts.

* `CS.huffCost` : the cost of the Huffman code for a multiset of weights, defined by the
  usual greedy algorithm (repeatedly merge the two smallest weights, and accumulate the
  merged weights).
* `CS.huffCost_le_of_kraft` : the core optimality statement.  For any assignment of
  codeword *lengths* to the weights whose Kraft sum `∑ 2 ^ (-ℓ)` is at most `1`, the
  Huffman cost is a lower bound for the resulting expected length.
* `CS.kraft_le_one_of_prefixFree` : Kraft's inequality: the lengths of a prefix-free code
  satisfy the Kraft inequality.

Combining the last two yields `CS.huffman_optimal`.
-/

namespace CS

open scoped BigOperators

noncomputable section

/-! ## The Huffman cost -/

/-- Auxiliary: the Huffman cost of a *sorted* list of weights.  At each step the two
smallest weights `a ≤ b` are merged into `a + b`, contributing `a + b` to the cost. -/
noncomputable def huffList : List ℝ → ℝ
  | [] => 0
  | [_] => 0
  | a :: b :: l => (a + b) + huffList (Multiset.sort ((a + b) ::ₘ (↑l : Multiset ℝ)) (· ≤ ·))
termination_by l => l.length
decreasing_by simp

/-- The cost of the Huffman code built from the multiset of weights `W`, i.e. the
sum `∑ w * (depth of w)` over the Huffman tree. -/
noncomputable def huffCost (W : Multiset ℝ) : ℝ := huffList (Multiset.sort W (· ≤ ·))

/-- The Kraft sum `∑ 2 ^ (-ℓ)` of a multiset of codeword lengths. -/
noncomputable def kraft (L : Multiset ℕ) : ℝ := (L.map fun n => ((2 : ℝ)⁻¹) ^ n).sum

/-- The expected length `∑ w * ℓ` of an assignment of weights and codeword lengths. -/
noncomputable def costOf (S : Multiset (ℝ × ℕ)) : ℝ := (S.map fun p => p.1 * (p.2 : ℝ)).sum

@[simp] theorem kraft_zero : kraft 0 = 0 := rfl

@[simp] theorem kraft_cons (n : ℕ) (L : Multiset ℕ) :
    kraft (n ::ₘ L) = ((2 : ℝ)⁻¹) ^ n + kraft L := by
  simp [kraft]

theorem kraft_nonneg (L : Multiset ℕ) : 0 ≤ kraft L := by
  refine Multiset.sum_nonneg ?_
  intro x hx
  simp only [Multiset.mem_map] at hx
  obtain ⟨n, _, rfl⟩ := hx
  positivity

@[simp] theorem costOf_zero : costOf 0 = 0 := rfl

@[simp] theorem costOf_cons (p : ℝ × ℕ) (S : Multiset (ℝ × ℕ)) :
    costOf (p ::ₘ S) = p.1 * (p.2 : ℝ) + costOf S := by
  simp [costOf]

theorem costOf_nonneg {S : Multiset (ℝ × ℕ)} (h : ∀ p ∈ S, 0 ≤ p.1) : 0 ≤ costOf S := by
  refine Multiset.sum_nonneg ?_
  intro x hx
  simp only [Multiset.mem_map] at hx
  obtain ⟨p, hp, rfl⟩ := hx
  exact mul_nonneg (h p hp) (Nat.cast_nonneg _)

/-! ## Basic facts about `huffCost` -/

theorem sort_cons_cons (x y : ℝ) (l : Multiset ℝ) (hx : ∀ z ∈ l, x ≤ z) (hy : ∀ z ∈ l, y ≤ z) :
    Multiset.sort (x ::ₘ y ::ₘ l) (· ≤ ·) = min x y :: max x y :: Multiset.sort l (· ≤ ·) := by
  have h1 : x ::ₘ y ::ₘ l = min x y ::ₘ max x y ::ₘ l := by
    rcases le_total x y with h | h
    · simp [min_eq_left h, max_eq_right h]
    · simp [min_eq_right h, max_eq_left h, Multiset.cons_swap]
  rw [h1, Multiset.sort_cons, Multiset.sort_cons]
  · intro b hb
    rcases le_total x y with h | h
    · simpa [max_eq_right h] using hy b hb
    · simpa [max_eq_left h] using hx b hb
  · intro b hb
    simp only [Multiset.mem_cons] at hb
    rcases hb with rfl | hb
    · exact min_le_max
    · exact le_trans (min_le_left x y) (hx b hb)

@[simp] theorem huffCost_zero : huffCost 0 = 0 := by simp [huffCost, huffList]

@[simp] theorem huffCost_singleton (a : ℝ) : huffCost {a} = 0 := by simp [huffCost, huffList]

/-- The defining recursion of the Huffman algorithm: if `x` and `y` are two smallest
weights, they get merged. -/
theorem huffCost_cons_cons (x y : ℝ) (l : Multiset ℝ) (hx : ∀ z ∈ l, x ≤ z)
    (hy : ∀ z ∈ l, y ≤ z) :
    huffCost (x ::ₘ y ::ₘ l) = (x + y) + huffCost ((x + y) ::ₘ l) := by
  rw [huffCost, sort_cons_cons x y l hx hy, huffList, huffCost, min_add_max]
  congr 2
  rw [Multiset.sort_eq]

/-- Sanity check: for weights `1, 1, 2` the Huffman code has expected length
`1*2 + 1*2 + 2*1 = 6`. -/
example : huffCost {1, 1, 2} = (6 : ℝ) := by
  have h1 : ({1, 1, 2} : Multiset ℝ) = (1 : ℝ) ::ₘ (1 : ℝ) ::ₘ {(2 : ℝ)} := rfl
  rw [h1, huffCost_cons_cons 1 1 {2} (by norm_num) (by norm_num),
    show ((1 : ℝ) + 1) ::ₘ ({2} : Multiset ℝ) = (2 : ℝ) ::ₘ (2 : ℝ) ::ₘ 0 by norm_num,
    huffCost_cons_cons 2 2 0 (by simp) (by simp)]
  norm_num

/-! ## Multiset helpers -/

theorem exists_min_of_ne_zero {α : Type*} [LinearOrder α] (s : Multiset α) (h : s ≠ 0) :
    ∃ x ∈ s, ∀ y ∈ s, x ≤ y := by
  induction s using Multiset.induction with
  | empty => exact absurd rfl h
  | cons a t ih =>
      by_cases ht : t = 0
      · subst ht; exact ⟨a, by simp, by simp⟩
      · obtain ⟨x, hx, hx'⟩ := ih ht
        rcases le_total a x with hax | hax
        · exact ⟨a, by simp, by
            intro y hy
            rcases Multiset.mem_cons.1 hy with rfl | hy
            · exact le_rfl
            · exact hax.trans (hx' y hy)⟩
        · exact ⟨x, Multiset.mem_cons_of_mem hx, by
            intro y hy
            rcases Multiset.mem_cons.1 hy with rfl | hy
            · exact hax
            · exact hx' y hy⟩

theorem exists_max_of_ne_zero {α : Type*} [LinearOrder α] (s : Multiset α) (h : s ≠ 0) :
    ∃ x ∈ s, ∀ y ∈ s, y ≤ x := by
  induction s using Multiset.induction with
  | empty => exact absurd rfl h
  | cons a t ih =>
      by_cases ht : t = 0
      · subst ht; exact ⟨a, by simp, by simp⟩
      · obtain ⟨x, hx, hx'⟩ := ih ht
        rcases le_total a x with hax | hax
        · exact ⟨x, Multiset.mem_cons_of_mem hx, by
            intro y hy
            rcases Multiset.mem_cons.1 hy with rfl | hy
            · exact hax
            · exact hx' y hy⟩
        · exact ⟨a, by simp, by
            intro y hy
            rcases Multiset.mem_cons.1 hy with rfl | hy
            · exact le_rfl
            · exact (hx' y hy).trans hax⟩

/-! ## The exchange (swap) argument -/

/-- If some element of `S` has (maximal) length `d` and `x` is a minimal weight occurring in
`S`, then `S` can be rearranged, without changing the multiset of weights or of lengths and
without increasing the cost, so that the weight `x` sits at length `d`. -/
theorem exists_min_at_max_length (S : Multiset (ℝ × ℕ)) (d : ℕ) (x : ℝ)
    (hd : ∃ p ∈ S, p.2 = d) (hxmem : ∃ q ∈ S, q.1 = x)
    (hxmin : ∀ p ∈ S, x ≤ p.1) (hdmax : ∀ p ∈ S, p.2 ≤ d) :
    ∃ R : Multiset (ℝ × ℕ), S.map Prod.fst = ((x, d) ::ₘ R).map Prod.fst ∧
      S.map Prod.snd = ((x, d) ::ₘ R).map Prod.snd ∧
      costOf ((x, d) ::ₘ R) ≤ costOf S := by
  obtain ⟨p, hpS, hpd⟩ := hd
  obtain ⟨R₀, hR₀⟩ := Multiset.exists_cons_of_mem hpS
  by_cases hpx : p.1 = x
  · have hp : ((x, d) : ℝ × ℕ) = p := Prod.ext hpx.symm hpd.symm
    exact ⟨R₀, by rw [hR₀, hp], by rw [hR₀, hp], by rw [hR₀, hp]⟩
  · obtain ⟨q, hqS, hqx⟩ := hxmem
    have hqR : q ∈ R₀ := by
      have : q ∈ p ::ₘ R₀ := hR₀ ▸ hqS
      rcases Multiset.mem_cons.1 this with rfl | h
      · exact absurd hqx hpx
      · exact h
    obtain ⟨R, hR⟩ := Multiset.exists_cons_of_mem hqR
    refine ⟨(p.1, q.2) ::ₘ R, ?_, ?_, ?_⟩
    · rw [hR₀, hR]
      simp only [Multiset.map_cons]
      rw [← hqx]
      exact Multiset.cons_swap _ _ _
    · rw [hR₀, hR]
      simp only [Multiset.map_cons]
      rw [← hpd]
    · rw [hR₀, hR]
      simp only [costOf_cons]
      have h1 : x ≤ p.1 := hxmin p hpS
      have h2 : (q.2 : ℝ) ≤ (d : ℝ) := by
        exact_mod_cast hdmax q hqS
      have hqp : q.1 = x := hqx
      rw [hqp, hpd]
      nlinarith [mul_nonneg (sub_nonneg.2 h1) (sub_nonneg.2 h2)]

/-! ## Kraft bookkeeping -/

/-- Integer version of the Kraft sum, scaled by `2 ^ d`. -/
def kraftNat (d : ℕ) (L : Multiset ℕ) : ℕ := (L.map fun n => 2 ^ (d - n)).sum

theorem kraft_eq_kraftNat (d : ℕ) (L : Multiset ℕ) (hL : ∀ n ∈ L, n ≤ d) :
    kraft L * 2 ^ d = (kraftNat d L : ℝ) := by
  induction L using Multiset.induction with
  | empty => simp [kraftNat]
  | cons a t ih =>
      have ha : a ≤ d := hL a (Multiset.mem_cons_self _ _)
      have ht : ∀ n ∈ t, n ≤ d := fun n hn => hL n (Multiset.mem_cons_of_mem hn)
      rw [kraft_cons, add_mul, ih ht]
      have hda : ((2 : ℝ)⁻¹) ^ a * 2 ^ d = (2 : ℝ) ^ (d - a) := by
        have h1 : ((2 : ℝ)⁻¹) ^ a * 2 ^ d = 2 ^ d / 2 ^ a := by
          rw [inv_pow]; ring
        rw [h1, div_eq_iff (by positivity : (2:ℝ) ^ a ≠ 0), ← pow_add]
        congr 1
        omega
      rw [hda]
      simp only [kraftNat, Multiset.map_cons, Multiset.sum_cons]
      push_cast
      ring

theorem inv_two_pow_pred (d : ℕ) (hd : 1 ≤ d) :
    ((2:ℝ)⁻¹) ^ (d - 1) = 2 * ((2:ℝ)⁻¹) ^ d := by
  have h : ((2:ℝ)⁻¹) ^ d = ((2:ℝ)⁻¹) ^ (d - 1) * (2:ℝ)⁻¹ := by
    rw [← pow_succ]
    congr 1
    omega
  rw [h]
  ring

/-- If the maximum length `d ≥ 1` is attained by exactly one codeword, then that codeword
can be shortened while keeping the Kraft inequality. -/
theorem kraft_shorten_unique_max (d : ℕ) (hd : 1 ≤ d) (L : Multiset ℕ)
    (hL : ∀ n ∈ L, n < d) (hk : kraft (d ::ₘ L) ≤ 1) :
    kraft ((d - 1) ::ₘ L) ≤ 1 := by
  set N := kraftNat d (d ::ₘ L) with hN
  have hmem : ∀ n ∈ d ::ₘ L, n ≤ d := by
    intro n hn
    rcases Multiset.mem_cons.1 hn with rfl | hn
    · exact le_rfl
    · exact (hL n hn).le
  have hEq : kraft (d ::ₘ L) * 2 ^ d = (N : ℝ) := kraft_eq_kraftNat d _ hmem
  -- `N` is odd
  have hodd : ¬ (2 ∣ N) := by
    have hsplit : N = 1 + (L.map fun n => 2 ^ (d - n)).sum := by
      simp [hN, kraftNat]
    have heven : (2 : ℕ) ∣ (L.map fun n => 2 ^ (d - n)).sum := by
      refine Multiset.dvd_sum ?_
      intro x hx
      simp only [Multiset.mem_map] at hx
      obtain ⟨n, hn, rfl⟩ := hx
      exact dvd_pow_self 2 (by have := hL n hn; omega)
    obtain ⟨k, hk⟩ := heven
    omega
  have hle : (N : ℝ) ≤ 2 ^ d := by
    rw [← hEq]
    have : (0:ℝ) < 2 ^ d := by positivity
    nlinarith [kraft_nonneg (d ::ₘ L)]
  have hleN : N ≤ 2 ^ d := by exact_mod_cast hle
  have hne : N ≠ 2 ^ d := by
    intro h
    apply hodd
    rw [h]
    exact dvd_pow_self 2 (by omega)
  have hlt : N + 1 ≤ 2 ^ d := by omega
  -- now compute the new Kraft sum
  have hone : ((2:ℝ)⁻¹) ^ d * 2 ^ d = 1 := by
    rw [inv_pow, inv_mul_cancel₀ (by positivity)]
  have hkey : kraft ((d - 1) ::ₘ L) * 2 ^ d = (N : ℝ) + 1 := by
    rw [kraft_cons, add_mul] at hEq
    rw [hone] at hEq
    have h2 : (2:ℝ) * ((2:ℝ)⁻¹) ^ d * 2 ^ d = 2 := by rw [mul_assoc, hone]; ring
    rw [kraft_cons, inv_two_pow_pred d hd, add_mul]
    linarith
  have h2d : (0:ℝ) < 2 ^ d := by positivity
  have hcast : (N : ℝ) + 1 ≤ 2 ^ d := by exact_mod_cast hlt
  have : kraft ((d - 1) ::ₘ L) * 2 ^ d ≤ 1 * 2 ^ d := by
    rw [hkey, one_mul]; exact hcast
  exact le_of_mul_le_mul_right this h2d

theorem kraft_merge (d : ℕ) (hd : 1 ≤ d) (L : Multiset ℕ) :
    kraft ((d - 1) ::ₘ L) = kraft (d ::ₘ d ::ₘ L) := by
  rw [kraft_cons, kraft_cons, kraft_cons, inv_two_pow_pred d hd]
  ring

/-! ## The core optimality theorem -/

theorem huffCost_le_of_kraft_aux : ∀ n : ℕ, ∀ S : Multiset (ℝ × ℕ),
    (S.map Prod.snd).sum = n → (∀ p ∈ S, 0 ≤ p.1) → kraft (S.map Prod.snd) ≤ 1 →
    huffCost (S.map Prod.fst) ≤ costOf S := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n IH =>
  intro S hsum hpos hk
  have hposW : ∀ w ∈ S.map Prod.fst, 0 ≤ w := by
    intro w hw
    obtain ⟨q, hq, rfl⟩ := Multiset.mem_map.1 hw
    exact hpos q hq
  by_cases hcard : Multiset.card S ≤ 1
  · -- Base case: at most one codeword.
    have hc : Multiset.card (S.map Prod.fst) ≤ 1 := by simpa using hcard
    have h0 : huffCost (S.map Prod.fst) = 0 := by
      rcases Nat.le_one_iff_eq_zero_or_eq_one.1 hc with h | h
      · rw [Multiset.card_eq_zero.1 h]; exact huffCost_zero
      · obtain ⟨a, ha⟩ := Multiset.card_eq_one.1 h
        rw [ha]; exact huffCost_singleton a
    rw [h0]
    exact costOf_nonneg hpos
  push_neg at hcard
  have hSne : S ≠ 0 := by
    intro h; rw [h] at hcard; simp at hcard
  obtain ⟨d, hdmem, hdmax⟩ := exists_max_of_ne_zero (S.map Prod.snd) (by simpa using hSne)
  obtain ⟨p₀, hp₀S, hp₀d⟩ := Multiset.mem_map.1 hdmem
  have hdmaxS : ∀ q ∈ S, q.2 ≤ d := fun q hq => hdmax _ (Multiset.mem_map_of_mem _ hq)
  obtain ⟨R, hR⟩ := Multiset.exists_cons_of_mem hp₀S
  have hlen : S.map Prod.snd = d ::ₘ R.map Prod.snd := by rw [hR]; simp [hp₀d]
  have hRS : ∀ q ∈ R, q ∈ S := by
    intro q hq; rw [hR]; exact Multiset.mem_cons_of_mem hq
  by_cases hcount : (S.map Prod.snd).count d ≤ 1
  · -- Case A: the maximal length is attained exactly once; shorten that codeword.
    have hcount0 : (R.map Prod.snd).count d = 0 := by
      rw [hlen, Multiset.count_cons_self] at hcount
      omega
    have hnotmem : d ∉ R.map Prod.snd := Multiset.count_eq_zero.1 hcount0
    have hRlt : ∀ q ∈ R, q.2 < d := by
      intro q hq
      have h1 : q.2 ≤ d := hdmaxS q (hRS q hq)
      have h2 : q.2 ≠ d := by
        intro h; exact hnotmem (h ▸ Multiset.mem_map_of_mem _ hq)
      omega
    have hRlt' : ∀ m ∈ R.map Prod.snd, m < d := by
      intro m hm
      obtain ⟨q, hq, rfl⟩ := Multiset.mem_map.1 hm
      exact hRlt q hq
    have hd1 : 1 ≤ d := by
      by_contra hcon
      have hd0 : d = 0 := by omega
      have hRz : R = 0 := by
        refine Multiset.eq_zero_of_forall_notMem ?_
        intro q hq
        have := hRlt q hq
        omega
      rw [hR, hRz] at hcard
      simp at hcard
    set S' : Multiset (ℝ × ℕ) := (p₀.1, d - 1) ::ₘ R with hS'
    have hfst : S'.map Prod.fst = S.map Prod.fst := by rw [hS', hR]; simp
    have hsnd : S'.map Prod.snd = (d - 1) ::ₘ R.map Prod.snd := by rw [hS']; simp
    have hnsum : (S.map Prod.snd).sum = d + (R.map Prod.snd).sum := by rw [hlen]; simp
    have hlt : (S'.map Prod.snd).sum < n := by
      rw [hsnd]
      simp only [Multiset.sum_cons]
      omega
    have hk' : kraft (S'.map Prod.snd) ≤ 1 := by
      rw [hsnd]
      exact kraft_shorten_unique_max d hd1 (R.map Prod.snd) hRlt' (by rw [← hlen]; exact hk)
    have hpos' : ∀ q ∈ S', 0 ≤ q.1 := by
      intro q hq
      rw [hS'] at hq
      rcases Multiset.mem_cons.1 hq with rfl | hq
      · exact hpos p₀ hp₀S
      · exact hpos q (hRS q hq)
    have hIH := IH _ hlt S' rfl hpos' hk'
    have hcost : costOf S' ≤ costOf S := by
      rw [hS', hR, costOf_cons, costOf_cons, hp₀d]
      have hcast : ((d - 1 : ℕ) : ℝ) = (d : ℝ) - 1 := by
        have : (1:ℕ) ≤ d := hd1
        push_cast [Nat.cast_sub this]
        ring
      rw [hcast]
      have := hpos p₀ hp₀S
      nlinarith
    rw [← hfst]
    exact hIH.trans hcost
  · -- Case B: at least two codewords of maximal length; merge the two smallest weights.
    push_neg at hcount
    have hcountR : 1 ≤ (R.map Prod.snd).count d := by
      rw [hlen, Multiset.count_cons_self] at hcount
      omega
    have hdmemR : d ∈ R.map Prod.snd := by
      rw [← Multiset.count_pos]; omega
    obtain ⟨L₀, hL₀⟩ := Multiset.exists_cons_of_mem hdmemR
    have hd1 : 1 ≤ d := by
      by_contra hcon
      have hd0 : d = 0 := by omega
      have : kraft (S.map Prod.snd) = 1 + (1 + kraft L₀) := by
        rw [hlen, hL₀, kraft_cons, kraft_cons, hd0]
        norm_num
      have := kraft_nonneg L₀
      linarith [hk, this]
    -- pick the smallest weight and move it to depth `d`
    obtain ⟨x, hxmem, hxmin⟩ := exists_min_of_ne_zero (S.map Prod.fst) (by simpa using hSne)
    obtain ⟨qx, hqxS, hqx⟩ := Multiset.mem_map.1 hxmem
    obtain ⟨R₁, hfst1, hsnd1, hcost1⟩ :=
      exists_min_at_max_length S d x ⟨p₀, hp₀S, hp₀d⟩ ⟨qx, hqxS, hqx⟩
        (fun q hq => hxmin _ (Multiset.mem_map_of_mem _ hq)) hdmaxS
    simp only [Multiset.map_cons] at hfst1 hsnd1
    -- `R₁` still contains a codeword of maximal length
    have hcount1 : 1 ≤ (R₁.map Prod.snd).count d := by
      have : (S.map Prod.snd).count d = (R₁.map Prod.snd).count d + 1 := by
        rw [hsnd1, Multiset.count_cons_self]
      omega
    have hdmemR₁ : d ∈ R₁.map Prod.snd := by rw [← Multiset.count_pos]; omega
    obtain ⟨p₁, hp₁R₁, hp₁d⟩ := Multiset.mem_map.1 hdmemR₁
    have hR₁ne : R₁ ≠ 0 := by
      intro h; rw [h] at hp₁R₁; simp at hp₁R₁
    have hmemR₁S : ∀ w ∈ R₁.map Prod.fst, w ∈ S.map Prod.fst := by
      intro w hw; rw [hfst1]; exact Multiset.mem_cons_of_mem hw
    have hdmaxR₁ : ∀ q ∈ R₁, q.2 ≤ d := by
      intro q hq
      have : q.2 ∈ S.map Prod.snd := by
        rw [hsnd1]; exact Multiset.mem_cons_of_mem (Multiset.mem_map_of_mem _ hq)
      exact hdmax _ this
    obtain ⟨y, hymem, hymin⟩ := exists_min_of_ne_zero (R₁.map Prod.fst) (by simpa using hR₁ne)
    obtain ⟨qy, hqyR₁, hqy⟩ := Multiset.mem_map.1 hymem
    obtain ⟨R₂, hfst2, hsnd2, hcost2⟩ :=
      exists_min_at_max_length R₁ d y ⟨p₁, hp₁R₁, hp₁d⟩ ⟨qy, hqyR₁, hqy⟩
        (fun q hq => hymin _ (Multiset.mem_map_of_mem _ hq)) hdmaxR₁
    simp only [Multiset.map_cons] at hfst2 hsnd2
    -- the merged instance
    set T : Multiset (ℝ × ℕ) := (x + y, d - 1) ::ₘ R₂ with hT
    have hTfst : T.map Prod.fst = (x + y) ::ₘ R₂.map Prod.fst := by rw [hT]; simp
    have hTsnd : T.map Prod.snd = (d - 1) ::ₘ R₂.map Prod.snd := by rw [hT]; simp
    have hSsnd : S.map Prod.snd = d ::ₘ d ::ₘ R₂.map Prod.snd := by rw [hsnd1, hsnd2]
    have hSfst : S.map Prod.fst = x ::ₘ y ::ₘ R₂.map Prod.fst := by rw [hfst1, hfst2]
    have hnsum : (S.map Prod.snd).sum = d + (d + (R₂.map Prod.snd).sum) := by
      rw [hSsnd]; simp
    have hlt : (T.map Prod.snd).sum < n := by
      rw [hTsnd]; simp only [Multiset.sum_cons]; omega
    have hk' : kraft (T.map Prod.snd) ≤ 1 := by
      rw [hTsnd, kraft_merge d hd1, ← hSsnd]; exact hk
    -- nonnegativity
    have hxnn : 0 ≤ x := hposW x hxmem
    have hynn : 0 ≤ y := hposW y (hmemR₁S y hymem)
    have hR₂w : ∀ w ∈ R₂.map Prod.fst, w ∈ S.map Prod.fst := by
      intro w hw
      rw [hSfst]
      exact Multiset.mem_cons_of_mem (Multiset.mem_cons_of_mem hw)
    have hpos' : ∀ q ∈ T, 0 ≤ q.1 := by
      intro q hq
      rw [hT] at hq
      rcases Multiset.mem_cons.1 hq with rfl | hq
      · exact add_nonneg hxnn hynn
      · exact hposW _ (hR₂w _ (Multiset.mem_map_of_mem _ hq))
    have hIH := IH _ hlt T rfl hpos' hk'
    -- the Huffman recursion
    have hxle : ∀ z ∈ R₂.map Prod.fst, x ≤ z := fun z hz => hxmin z (hR₂w z hz)
    have hyle : ∀ z ∈ R₂.map Prod.fst, y ≤ z := by
      intro z hz
      refine hymin z ?_
      rw [hfst2]
      exact Multiset.mem_cons_of_mem hz
    have hhuff : huffCost (S.map Prod.fst) = (x + y) + huffCost ((x + y) ::ₘ R₂.map Prod.fst) := by
      rw [hSfst]
      exact huffCost_cons_cons x y _ hxle hyle
    have hcast : ((d - 1 : ℕ) : ℝ) = (d : ℝ) - 1 := by
      push_cast [Nat.cast_sub hd1]; ring
    have hTcost : costOf T = (x + y) * ((d : ℝ) - 1) + costOf R₂ := by
      rw [hT, costOf_cons, hcast]
    have hcostS₁ : costOf ((x, d) ::ₘ R₁) ≤ costOf S := hcost1
    have hcostR₁ : costOf ((y, d) ::ₘ R₂) ≤ costOf R₁ := hcost2
    rw [hhuff, ← hTfst]
    have h1 : huffCost (T.map Prod.fst) ≤ costOf T := hIH
    rw [hTfst] at h1
    simp only [costOf_cons] at hcostS₁ hcostR₁
    rw [hTcost] at h1
    nlinarith [h1, hcostS₁, hcostR₁]

/-- **Core optimality of Huffman coding.**  If codeword lengths are attached to the weights
in such a way that the Kraft inequality holds, then the resulting expected length is at
least the Huffman cost. -/
theorem huffCost_le_of_kraft (S : Multiset (ℝ × ℕ)) (hpos : ∀ p ∈ S, 0 ≤ p.1)
    (hk : kraft (S.map Prod.snd) ≤ 1) : huffCost (S.map Prod.fst) ≤ costOf S :=
  huffCost_le_of_kraft_aux _ S rfl hpos hk

/-! ## Kraft's inequality for prefix-free codes -/

/-- A finite set of binary words is prefix-free if no word is a prefix of another. -/
def PrefixFreeSet (C : Finset (List Bool)) : Prop :=
  ∀ l ∈ C, ∀ m ∈ C, l ≠ m → ¬ (l <+: m)

/-- **Kraft's inequality** for a prefix-free set of binary codewords. -/
theorem kraft_finset_le : ∀ n : ℕ, ∀ C : Finset (List Bool), (∀ l ∈ C, l.length ≤ n) →
    PrefixFreeSet C → ∑ l ∈ C, ((2:ℝ)⁻¹) ^ l.length ≤ 1 := by
  intro n
  induction n with
  | zero =>
      intro C hlen _
      have hsub : C ⊆ {([] : List Bool)} := by
        intro l hl
        have := hlen l hl
        simp only [Finset.mem_singleton]
        exact List.length_eq_zero_iff.1 (by omega)
      calc ∑ l ∈ C, ((2:ℝ)⁻¹) ^ l.length
          ≤ ∑ l ∈ ({([] : List Bool)} : Finset (List Bool)), ((2:ℝ)⁻¹) ^ l.length := by
            refine Finset.sum_le_sum_of_subset_of_nonneg hsub ?_
            intro i _ _; positivity
        _ = 1 := by simp
  | succ n ih =>
      intro C hlen hpf
      by_cases hnil : ([] : List Bool) ∈ C
      · have hsub : C ⊆ {([] : List Bool)} := by
          intro l hl
          simp only [Finset.mem_singleton]
          by_contra hne
          exact hpf [] hnil l hl (Ne.symm hne) List.nil_prefix
        calc ∑ l ∈ C, ((2:ℝ)⁻¹) ^ l.length
            ≤ ∑ l ∈ ({([] : List Bool)} : Finset (List Bool)), ((2:ℝ)⁻¹) ^ l.length := by
              refine Finset.sum_le_sum_of_subset_of_nonneg hsub ?_
              intro i _ _; positivity
          _ = 1 := by simp
      · -- every codeword is nonempty, so split according to the first bit
        have key : ∀ b : Bool,
            ∑ l ∈ C.filter (fun l => l.head? = some b), ((2:ℝ)⁻¹) ^ l.length ≤ (2:ℝ)⁻¹ := by
          intro b
          set D := C.filter (fun l => l.head? = some b) with hD
          set Cb := D.image List.tail with hCb
          have hDmem : ∀ l ∈ D, l = b :: l.tail := by
            intro l hl
            rw [hD, Finset.mem_filter] at hl
            cases l with
            | nil => simp at hl
            | cons c t => simp at hl ⊢; exact hl.2
          have hDeq : D = Cb.image (List.cons b) := by
            ext l
            constructor
            · intro hl
              rw [Finset.mem_image]
              exact ⟨l.tail, by rw [hCb, Finset.mem_image]; exact ⟨l, hl, rfl⟩, (hDmem l hl).symm⟩
            · intro hl
              rw [Finset.mem_image] at hl
              obtain ⟨t, ht, rfl⟩ := hl
              rw [hCb, Finset.mem_image] at ht
              obtain ⟨m, hm, rfl⟩ := ht
              rw [← hDmem m hm]; exact hm
          have hsum : ∑ l ∈ D, ((2:ℝ)⁻¹) ^ l.length
              = (2:ℝ)⁻¹ * ∑ t ∈ Cb, ((2:ℝ)⁻¹) ^ t.length := by
            rw [hDeq, Finset.sum_image (by intro x _ y _ h; exact List.cons_injective h),
              Finset.mul_sum]
            refine Finset.sum_congr rfl ?_
            intro t _
            simp [pow_succ]
            ring
          have hlenb : ∀ t ∈ Cb, t.length ≤ n := by
            intro t ht
            rw [hCb, Finset.mem_image] at ht
            obtain ⟨m, hm, rfl⟩ := ht
            have hmC : m ∈ C := by rw [hD, Finset.mem_filter] at hm; exact hm.1
            have h3 := hlen m hmC
            rw [hDmem m hm] at h3
            simpa using h3
          have hpfb : PrefixFreeSet Cb := by
            intro t ht t' ht' hne hpre
            have hmem : ∀ s ∈ Cb, b :: s ∈ C := by
              intro s hs
              have : b :: s ∈ D := by rw [hDeq, Finset.mem_image]; exact ⟨s, hs, rfl⟩
              rw [hD, Finset.mem_filter] at this; exact this.1
            exact hpf (b :: t) (hmem t ht) (b :: t') (hmem t' ht')
              (by simpa using hne) (by simpa using hpre)
          have hih := ih Cb hlenb hpfb
          rw [hsum]
          nlinarith [hih]
        have hsplit : ∑ l ∈ C, ((2:ℝ)⁻¹) ^ l.length
            = ∑ l ∈ C.filter (fun l => l.head? = some false), ((2:ℝ)⁻¹) ^ l.length
              + ∑ l ∈ C.filter (fun l => l.head? = some true), ((2:ℝ)⁻¹) ^ l.length := by
          rw [← Finset.sum_filter_add_sum_filter_not C (fun l => l.head? = some false)]
          congr 1
          refine Finset.sum_congr ?_ (fun _ _ => rfl)
          ext l
          simp only [Finset.mem_filter]
          constructor
          · rintro ⟨hl, h2⟩
            refine ⟨hl, ?_⟩
            cases l with
            | nil => exact absurd hl hnil
            | cons c t => cases c <;> simp_all
          · rintro ⟨hl, h2⟩
            refine ⟨hl, ?_⟩
            cases l with
            | nil => exact absurd hl hnil
            | cons c t => cases c <;> simp_all
        rw [hsplit]
        have h1 := key false
        have h2 := key true
        linarith

/-! ## Prefix codes -/

/-- `c` is a prefix code: the codewords of distinct symbols are never prefixes of one
another. -/
def IsPrefixCode {α : Type*} (c : α → List Bool) : Prop :=
  ∀ a b : α, a ≠ b → ¬ (c a <+: c b)

theorem injective_of_isPrefixCode {α : Type*} {c : α → List Bool} (hc : IsPrefixCode c) :
    Function.Injective c := by
  intro a b hab
  by_contra hne
  exact hc a b hne (by rw [hab])

/-- Kraft's inequality, in terms of a prefix code indexed by a finite type. -/
theorem kraft_le_one_of_isPrefixCode {α : Type*} [Fintype α] {c : α → List Bool}
    (hc : IsPrefixCode c) : ∑ a, ((2:ℝ)⁻¹) ^ (c a).length ≤ 1 := by
  classical
  set C : Finset (List Bool) := Finset.univ.image c with hC
  have hreindex : ∑ a, ((2:ℝ)⁻¹) ^ (c a).length = ∑ l ∈ C, ((2:ℝ)⁻¹) ^ l.length := by
    rw [hC, Finset.sum_image (fun x _ y _ h => injective_of_isPrefixCode hc h)]
  rw [hreindex]
  refine kraft_finset_le (C.sup fun l => l.length) C (fun l hl => Finset.le_sup hl) ?_
  intro l hl m hm hne hpre
  rw [hC, Finset.mem_image] at hl hm
  obtain ⟨a, -, rfl⟩ := hl
  obtain ⟨b, -, rfl⟩ := hm
  exact hc a b (fun h => hne (by rw [h])) hpre

/-! ## Main theorem -/

/-- **Huffman coding minimizes the expected codeword length among prefix codes.**

For any finite alphabet `α` with nonnegative weights `w` and any prefix code
`c : α → List Bool`, the cost of the Huffman code built from the multiset of weights is at
most the expected codeword length `∑ a, w a * (c a).length` of `c`. -/
theorem huffman_optimal {α : Type*} [Fintype α] (w : α → ℝ) (hw : ∀ a, 0 ≤ w a)
    (c : α → List Bool) (hc : IsPrefixCode c) :
    huffCost (Multiset.map w Finset.univ.val) ≤ ∑ a, w a * ((c a).length : ℝ) := by
  classical
  set S : Multiset (ℝ × ℕ) := Finset.univ.val.map (fun a => (w a, (c a).length)) with hS
  have hfst : S.map Prod.fst = Multiset.map w Finset.univ.val := by
    rw [hS, Multiset.map_map]
    rfl
  have hcost : costOf S = ∑ a, w a * ((c a).length : ℝ) := by
    rw [← Finset.sum_map_val]
    simp [costOf, hS, Multiset.map_map, Function.comp]
  have hkr : kraft (S.map Prod.snd) = ∑ a, ((2:ℝ)⁻¹) ^ (c a).length := by
    rw [← Finset.sum_map_val]
    simp [kraft, hS, Multiset.map_map, Function.comp]
  have hpos : ∀ p ∈ S, 0 ≤ p.1 := by
    intro p hp
    rw [hS, Multiset.mem_map] at hp
    obtain ⟨a, -, rfl⟩ := hp
    exact hw a
  have := huffCost_le_of_kraft S hpos (by rw [hkr]; exact kraft_le_one_of_isPrefixCode hc)
  rwa [hfst, hcost] at this

end

end CS

import Mathlib
import RequestProject.Huffman
import RequestProject.HuffmanAchievable

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

