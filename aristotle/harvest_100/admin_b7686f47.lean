/-
# Huffman Optimal
Category: Computer Science
Target: CS.huffman_optimal
Statement: Huffman coding minimizes expected codeword length among prefix codes.
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/
import Mathlib

namespace CS

open List

variable {α : Type*} {ι : Type*}

/-! ## Extracting a minimum-weight element from a list -/

/-- `popMin f a l` returns a pair whose first component is an element of `a :: l`
minimizing `f`, and whose second component is the remaining list. -/
noncomputable def popMin (f : α → ℝ) : α → List α → α × List α
  | a, [] => (a, [])
  | a, b :: l =>
      if f b < f a then ((popMin f b l).1, a :: (popMin f b l).2)
      else ((popMin f a l).1, b :: (popMin f a l).2)

@[simp] lemma popMin_nil (f : α → ℝ) (a : α) : popMin f a [] = (a, []) := rfl

lemma popMin_cons (f : α → ℝ) (a b : α) (l : List α) :
    popMin f a (b :: l) =
      if f b < f a then ((popMin f b l).1, a :: (popMin f b l).2)
      else ((popMin f a l).1, b :: (popMin f a l).2) := rfl

@[simp] lemma popMin_length (f : α → ℝ) (a : α) (l : List α) :
    (popMin f a l).2.length = l.length := by
  induction l generalizing a with
  | nil => simp
  | cons b l ih => by_cases h : f b < f a <;> simp [popMin_cons, h, ih]

lemma popMin_perm (f : α → ℝ) (a : α) (l : List α) :
    (popMin f a l).1 :: (popMin f a l).2 ~ a :: l := by
  induction l generalizing a with
  | nil => simp
  | cons b l ih =>
      by_cases h : f b < f a
      · simp only [popMin_cons, h, if_pos]
        exact (List.Perm.swap a _ _).trans ((ih b).cons a)
      · simp only [popMin_cons, h, if_neg, not_false_iff]
        exact ((List.Perm.swap b _ _).trans (((ih a).cons b).trans (List.Perm.swap _ _ _)))

lemma popMin_le (f : α → ℝ) (a : α) (l : List α) :
    ∀ x ∈ a :: l, f (popMin f a l).1 ≤ f x := by
  induction l generalizing a with
  | nil => simp
  | cons b l ih =>
      intro x hx
      by_cases h : f b < f a
      · simp only [popMin_cons, h, if_pos]
        have h1 := ih b
        rcases List.mem_cons.1 hx with rfl | hx'
        · exact le_trans (h1 b (by simp)) h.le
        · exact h1 x hx'
      · simp only [popMin_cons, h, if_neg, not_false_iff]
        have h1 := ih a
        rcases List.mem_cons.1 hx with rfl | hx'
        · exact h1 x (by simp)
        · rcases List.mem_cons.1 hx' with rfl | hx''
          · exact le_trans (h1 a (by simp)) (not_lt.1 h)
          · exact h1 x (by simp [hx''])

lemma popMin_map (f : α → ℝ) (a : α) (l : List α) :
    f (popMin f a l).1 = (popMin id (f a) (l.map f)).1 ∧
      (popMin f a l).2.map f = (popMin id (f a) (l.map f)).2 := by
  induction l generalizing a with
  | nil => simp
  | cons b l ih =>
      by_cases h : f b < f a
      · simp only [popMin_cons, h, if_pos, List.map_cons]
        have : (id (f b) : ℝ) < id (f a) := h
        simp only [this, if_pos]
        exact ⟨(ih b).1, by simp [(ih b).2]⟩
      · simp only [popMin_cons, h, if_neg, not_false_iff, List.map_cons]
        have : ¬ ((id (f b) : ℝ) < id (f a)) := h
        simp only [this, if_neg, not_false_iff]
        exact ⟨(ih a).1, by simp [(ih a).2]⟩

/-! ## Codes -/

/-- The total weight of a group of symbols. -/
def gw (w : ι → ℝ) (g : List (ι × List Bool)) : ℝ := (g.map fun p => w p.1).sum

/-- The total cost (weighted codeword length) of a group. -/
def gcost (w : ι → ℝ) (g : List (ι × List Bool)) : ℝ :=
  (g.map fun p => w p.1 * (p.2.length : ℝ)).sum

/-- Merging two groups: prepend `false` to all codewords on the left,
`true` to all codewords on the right. -/
def gmerge (A B : List (ι × List Bool)) : List (ι × List Bool) :=
  A.map (fun p => (p.1, false :: p.2)) ++ B.map (fun p => (p.1, true :: p.2))

/-- One run of Huffman's algorithm: repeatedly merge two minimum-weight groups. -/
noncomputable def hstep (w : ι → ℝ) :
    List (ι × List Bool) → List (List (ι × List Bool)) → List (ι × List Bool)
  | g, [] => g
  | g, h :: F =>
      hstep w (gmerge (popMin (gw w) g (h :: F)).1
                (popMin (gw w) (popMin (gw w) g (h :: F)).2.headI
                  (popMin (gw w) g (h :: F)).2.tail).1)
            (popMin (gw w) (popMin (gw w) g (h :: F)).2.headI
                  (popMin (gw w) g (h :: F)).2.tail).2
  termination_by _ F => F.length
  decreasing_by
    simp [popMin_length]

/-- The cost of the Huffman code for a list of weights, defined by Huffman's recursion. -/
noncomputable def hcost : ℝ → List ℝ → ℝ
  | _, [] => 0
  | a, h :: F =>
      (popMin id a (h :: F)).1 +
        (popMin id (popMin id a (h :: F)).2.headI (popMin id a (h :: F)).2.tail).1 +
        hcost ((popMin id a (h :: F)).1 +
          (popMin id (popMin id a (h :: F)).2.headI (popMin id a (h :: F)).2.tail).1)
          (popMin id (popMin id a (h :: F)).2.headI (popMin id a (h :: F)).2.tail).2
  termination_by _ F => F.length
  decreasing_by
    simp [popMin_length]

/-- Kraft sum of a list of (weight, codeword length) pairs. -/
noncomputable def kraft (S : List (ℝ × ℕ)) : ℝ := (S.map fun p => (2:ℝ)⁻¹ ^ p.2).sum

/-- Expected codeword length of a list of (weight, codeword length) pairs. -/
def dcost (S : List (ℝ × ℕ)) : ℝ := (S.map fun p => p.1 * (p.2 : ℝ)).sum

/-- A list of codewords is prefix free. -/
def PrefixFreeList (L : List (List Bool)) : Prop :=
  L.Pairwise fun c d => ¬ c <+: d ∧ ¬ d <+: c

/-- A code (assignment of codewords to symbols) is a prefix code. -/
def IsPrefixCode (c : ι → List Bool) : Prop := ∀ i j, i ≠ j → ¬ c i <+: c j


/-! ## Kraft's inequality -/

/-- Kraft sum of a list of codewords. -/
noncomputable def ks (L : List (List Bool)) : ℝ := (L.map fun c => (2:ℝ)⁻¹ ^ c.length).sum

lemma ks_nonneg (L : List (List Bool)) : 0 ≤ ks L := by
  refine List.sum_nonneg ?_
  intro x hx
  obtain ⟨c, -, rfl⟩ := List.mem_map.1 hx
  positivity

lemma prefixFreeList_symm {c d : List Bool} :
    (¬ c <+: d ∧ ¬ d <+: c) → (¬ d <+: c ∧ ¬ c <+: d) := fun h => ⟨h.2, h.1⟩

lemma prefixFreeList_eq_singleton {L : List (List Bool)} (hpf : PrefixFreeList L)
    (hnil : [] ∈ L) : L = [[]] := by
  have hp : L ~ [] :: L.erase [] := List.perm_cons_erase hnil
  have hpf' : PrefixFreeList ([] :: L.erase []) :=
    (List.Perm.pairwise_iff prefixFreeList_symm hp).1 hpf
  have he : L.erase ([] : List Bool) = [] := by
    rcases e : L.erase ([] : List Bool) with _ | ⟨d, R⟩
    · rfl
    · exfalso
      rw [e] at hpf'
      exact ((List.pairwise_cons.1 hpf').1 d (by simp)).1 (List.nil_prefix)
  rw [he] at hp
  exact List.perm_singleton.1 hp

lemma ks_tail (M : List (List Bool)) (hne : ∀ c ∈ M, c ≠ []) :
    ks M = 2⁻¹ * ks (M.map List.tail) := by
  induction M with
  | nil => simp [ks]
  | cons c M ih =>
      have hc : c ≠ [] := hne c (by simp)
      have hlen : c.length = c.tail.length + 1 := by
        cases c with
        | nil => exact absurd rfl hc
        | cons a t => simp
      have ih' := ih (fun d hd => hne d (by simp [hd]))
      simp only [ks, List.map_cons, List.sum_cons, hlen, pow_succ] at *
      rw [ih']
      ring

lemma prefixFreeList_tail (b : Bool) (M : List (List Bool)) (hb : ∀ c ∈ M, c.headI = b)
    (hne : ∀ c ∈ M, c ≠ []) (h : PrefixFreeList M) : PrefixFreeList (M.map List.tail) := by
  rw [PrefixFreeList, List.pairwise_map]
  refine List.Pairwise.imp_of_mem ?_ h
  intro c d hc hd hcd
  have hc' : c = b :: c.tail := by
    have hcb := hb c hc
    cases c with
    | nil => exact absurd rfl (hne _ hc)
    | cons a t => simpa using hcb
  have hd' : d = b :: d.tail := by
    have hdb := hb d hd
    cases d with
    | nil => exact absurd rfl (hne _ hd)
    | cons a t => simpa using hdb
  constructor
  · intro hpre
    exact hcd.1 (by rw [hc', hd']; exact List.cons_prefix_cons.2 ⟨rfl, hpre⟩)
  · intro hpre
    exact hcd.2 (by rw [hc', hd']; exact List.cons_prefix_cons.2 ⟨rfl, hpre⟩)

/-- **Kraft's inequality**: a prefix-free list of codewords satisfies `∑ 2^(-|c|) ≤ 1`. -/
lemma ks_le_one : ∀ (n : ℕ) (L : List (List Bool)), (∀ c ∈ L, c.length ≤ n) →
    PrefixFreeList L → ks L ≤ 1 := by
  intro n
  induction n with
  | zero =>
      intro L hlen hpf
      rcases L with _ | ⟨c, R⟩
      · simp [ks]
      · have : c = [] := List.eq_nil_of_length_eq_zero (Nat.le_zero.1 (hlen c (by simp)))
        rw [prefixFreeList_eq_singleton hpf (this ▸ (by simp : c ∈ c :: R))]
        norm_num [ks]
  | succ n ih =>
      intro L hlen hpf
      by_cases hnil : [] ∈ L
      · rw [prefixFreeList_eq_singleton hpf hnil]; norm_num [ks]
      · have hne : ∀ c ∈ L, c ≠ [] := by
          intro c hc h; exact hnil (h ▸ hc)
        have half : ∀ (M : List (List Bool)) (b : Bool), (∀ c ∈ M, c ∈ L) →
            (∀ c ∈ M, c.headI = b) → PrefixFreeList M → ks M ≤ 2⁻¹ := by
          intro M b hML hb hpfM
          have hneM : ∀ c ∈ M, c ≠ [] := fun c hc => hne c (hML c hc)
          rw [ks_tail M hneM]
          have hlen' : ∀ d ∈ M.map List.tail, d.length ≤ n := by
            intro d hd
            obtain ⟨c, hc, rfl⟩ := List.mem_map.1 hd
            have := hlen c (hML c hc)
            have hc0 : c.length = c.tail.length + 1 := by
              cases c with
              | nil => exact absurd rfl (hneM _ hc)
              | cons a t => simp
            omega
          have := ih (M.map List.tail) hlen' (prefixFreeList_tail b M hb hneM hpfM)
          nlinarith [ks_nonneg (M.map List.tail)]
        have hsplit : ks (L.filter (fun c => c.headI)) +
            ks (L.filter (fun c => !(c.headI))) = ks L := by
          have hp := List.filter_append_perm (fun c : List Bool => c.headI) L
          have := (hp.map (fun c : List Bool => (2:ℝ)⁻¹ ^ c.length)).sum_eq
          simpa [ks, List.map_append, List.sum_append] using this
        have h1 : ks (L.filter (fun c => c.headI)) ≤ 2⁻¹ := by
          refine half _ true (fun c hc => (List.mem_filter.1 hc).1) ?_
            (List.Pairwise.sublist (List.filter_sublist) hpf)
          intro c hc; simpa using (List.mem_filter.1 hc).2
        have h2 : ks (L.filter (fun c => !(c.headI))) ≤ 2⁻¹ := by
          refine half _ false (fun c hc => (List.mem_filter.1 hc).1) ?_
            (List.Pairwise.sublist (List.filter_sublist) hpf)
          intro c hc
          have := (List.mem_filter.1 hc).2
          simpa using this
        linarith

/-! ## Basic properties of the Kraft sum and the cost -/

lemma kraft_cons (p : ℝ × ℕ) (S : List (ℝ × ℕ)) :
    kraft (p :: S) = (2:ℝ)⁻¹ ^ p.2 + kraft S := by simp [kraft]

lemma dcost_cons (p : ℝ × ℕ) (S : List (ℝ × ℕ)) :
    dcost (p :: S) = p.1 * (p.2 : ℝ) + dcost S := by simp [dcost]

lemma kraft_nonneg (S : List (ℝ × ℕ)) : 0 ≤ kraft S := by
  refine List.sum_nonneg ?_
  intro x hx
  obtain ⟨c, -, rfl⟩ := List.mem_map.1 hx
  positivity

lemma kraft_eq_of_snd_perm {S T : List (ℝ × ℕ)} (h : S.map Prod.snd ~ T.map Prod.snd) :
    kraft S = kraft T := by
  have := (h.map (fun n : ℕ => (2:ℝ)⁻¹ ^ n)).sum_eq
  simpa [kraft, List.map_map, Function.comp] using this

lemma dcost_perm {S T : List (ℝ × ℕ)} (h : S ~ T) : dcost S = dcost T :=
  (h.map _).sum_eq

lemma dcost_swap (x y : ℝ) (m d : ℕ) (T : List (ℝ × ℕ)) (hxy : x ≤ y) (hdm : d ≤ m) :
    dcost ((x, m) :: (y, d) :: T) ≤ dcost ((x, d) :: (y, m) :: T) := by
  simp only [dcost_cons]
  have h1 : (0:ℝ) ≤ (y - x) * ((m : ℝ) - d) := by
    have : (d : ℝ) ≤ m := by exact_mod_cast hdm
    nlinarith
  nlinarith

/-! ## The maximal depth can be assumed to occur twice -/

lemma nat_sum_even (L : List ℕ) (h : ∀ n ∈ L, n % 2 = 0) : L.sum % 2 = 0 := by
  induction L with
  | nil => simp
  | cons n L ih =>
      have h1 := h n (by simp)
      have h2 := ih (fun k hk => h k (by simp [hk]))
      simp only [List.sum_cons]
      omega

lemma kraft_mul_pow (m : ℕ) : ∀ (S : List (ℝ × ℕ)), (∀ p ∈ S, p.2 ≤ m) →
    (2:ℝ)^m * kraft S = ((S.map fun p => 2^(m - p.2)).sum : ℕ) := by
  intro S
  induction S with
  | nil => simp [kraft]
  | cons p S ih =>
      intro h
      have hp : p.2 ≤ m := h p (by simp)
      have key : (2:ℝ)^m * (2⁻¹)^p.2 = 2^(m - p.2) := by
        rw [pow_sub₀ (2:ℝ) (by norm_num) hp, inv_pow]
      have hIH := ih (fun q hq => h q (by simp [hq]))
      rw [kraft_cons, mul_add, key, hIH]
      simp only [List.map_cons, List.sum_cons]
      push_cast
      ring

/-- If the maximal depth `m` occurs only once, the Kraft sum leaves room to shorten it. -/
lemma kraft_shorten_unique_max (m : ℕ) (hm : 1 ≤ m) (x : ℝ) (T : List (ℝ × ℕ))
    (hT : ∀ p ∈ T, p.2 < m) (hk : kraft ((x, m) :: T) ≤ 1) :
    kraft ((x, m - 1) :: T) ≤ 1 := by
  set N : ℕ := (((x, m) :: T).map fun p => 2^(m - p.2)).sum with hN
  have hle : ∀ p ∈ (x, m) :: T, p.2 ≤ m := by
    intro p hp
    rcases List.mem_cons.1 hp with rfl | hp'
    · exact le_rfl
    · exact (hT p hp').le
  have hkey : (2:ℝ)^m * kraft ((x, m) :: T) = (N : ℝ) := kraft_mul_pow m _ hle
  -- `N` is odd
  have hodd : N % 2 = 1 := by
    have heven : ((T.map fun p => 2^(m - p.2)).sum) % 2 = 0 := by
      refine nat_sum_even ?_
      intro n hn
      obtain ⟨q, hq, rfl⟩ := List.mem_map.1 hn
      have h1 : 1 ≤ m - q.2 := by have := hT q hq; omega
      obtain ⟨j, hj⟩ : ∃ j, m - q.2 = j + 1 := ⟨m - q.2 - 1, by omega⟩
      rw [hj, pow_succ]
      omega
    have : N = 2^(m - m) + (T.map fun p => 2^(m - p.2)).sum := by
      rw [hN]; simp
    rw [this]
    simp only [Nat.sub_self, pow_zero]
    omega
  -- `N ≤ 2 ^ m`
  have hNle : (N : ℝ) ≤ 2^m := by
    rw [← hkey]
    have : (0:ℝ) < 2^m := by positivity
    nlinarith
  have hNle' : N ≤ 2^m := by exact_mod_cast hNle
  have hNlt : N < 2^m := by
    rcases lt_or_eq_of_le hNle' with h | h
    · exact h
    · exfalso
      have : (2:ℕ)^m % 2 = 0 := by
        obtain ⟨j, hj⟩ : ∃ j, m = j + 1 := ⟨m - 1, by omega⟩
        rw [hj, pow_succ]; omega
      omega
  -- conclude
  have hpow : (0:ℝ) < 2^m := by positivity
  have h1 : kraft ((x, m) :: T) ≤ 1 - (2:ℝ)⁻¹^m := by
    have hNle2 : (N : ℝ) ≤ 2^m - 1 := by
      have : (N : ℝ) + 1 ≤ 2^m := by exact_mod_cast hNlt
      linarith
    have hmul : (2:ℝ)^m * kraft ((x, m) :: T) ≤ 2^m - 1 := by rw [hkey]; exact hNle2
    have h2 : kraft ((x, m) :: T) ≤ ((2:ℝ)^m - 1) / 2^m := by
      rw [le_div_iff₀ hpow]; linarith
    have h3 : ((2:ℝ)^m - 1)/2^m = 1 - (2:ℝ)⁻¹^m := by
      rw [inv_pow]; field_simp
    rw [h3] at h2
    exact h2
  have hstep : kraft ((x, m - 1) :: T) = kraft ((x, m) :: T) + (2:ℝ)⁻¹^m := by
    rw [kraft_cons, kraft_cons]
    have : (2:ℝ)⁻¹^(m-1) = 2 * 2⁻¹^m := by
      obtain ⟨j, hj⟩ : ∃ j, m = j + 1 := ⟨m - 1, by omega⟩
      subst hj
      simp [pow_succ]
      ring
    simp only [this]
    ring
  rw [hstep]
  linarith

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

