import Mathlib

/-!
# Kraft's inequality for prefix-free codes
-/

namespace CS

open scoped BigOperators

theorem two_zpow_neg_eq_div {k n : ℕ} (h : k ≤ n) :
    (2 : ℝ) ^ (-(k : ℤ)) = 2 ^ (n - k) / 2 ^ n := by
  have key : (2:ℝ) ^ (n - k) * 2 ^ k = 2 ^ n := by
    rw [← pow_add]; congr 1; omega
  rw [eq_div_iff (by positivity : (2:ℝ) ^ n ≠ 0), ← key, zpow_neg, zpow_natCast]
  field_simp

/-- A code `c` is *prefix-free* if no codeword is a prefix of a different symbol's codeword.
Note that this in particular forces `c` to be injective. -/
def PrefixFree {α : Type*} (c : α → List Bool) : Prop :=
  ∀ a b : α, a ≠ b → ¬ (c a).IsPrefix (c b)

theorem PrefixFree.injective {α : Type*} {c : α → List Bool} (h : PrefixFree c) :
    Function.Injective c := by
  intro a b hab
  by_contra hne
  exact h a b hne (by rw [hab])

/-- The finset of all bit strings of a given length. -/
def allBits : ℕ → Finset (List Bool)
  | 0 => {[]}
  | n + 1 => (allBits n).image (fun l => false :: l) ∪ (allBits n).image (fun l => true :: l)

@[simp] theorem mem_allBits {n : ℕ} {l : List Bool} : l ∈ allBits n ↔ l.length = n := by
  induction n generalizing l with
  | zero => simp [allBits, List.length_eq_zero_iff]
  | succ n ih =>
      cases l with
      | nil => simp [allBits]
      | cons b t =>
          cases b <;> simp [allBits, ih]

theorem card_allBits (n : ℕ) : (allBits n).card = 2 ^ n := by
  induction n with
  | zero => simp [allBits]
  | succ n ih =>
      have hdisj : Disjoint ((allBits n).image (fun l => false :: l))
          ((allBits n).image (fun l => true :: l)) := by
        rw [Finset.disjoint_left]
        rintro l hl hl'
        simp only [Finset.mem_image] at hl hl'
        obtain ⟨x, _, rfl⟩ := hl
        obtain ⟨y, _, hy⟩ := hl'
        exact absurd hy (by simp)
      rw [allBits, Finset.card_union_of_disjoint hdisj,
        Finset.card_image_of_injective _ (fun x y h => by simpa using h),
        Finset.card_image_of_injective _ (fun x y h => by simpa using h), ih]
      ring

/-- All extensions of `s` by `k` bits. -/
def extBits (s : List Bool) (k : ℕ) : Finset (List Bool) :=
  (allBits k).image (fun t => s ++ t)

theorem card_extBits (s : List Bool) (k : ℕ) : (extBits s k).card = 2 ^ k := by
  rw [extBits, Finset.card_image_of_injective _ (fun x y h => by simpa using h), card_allBits]

theorem extBits_subset {s : List Bool} {k m : ℕ} (h : s.length + k = m) :
    extBits s k ⊆ allBits m := by
  intro l hl
  simp only [extBits, Finset.mem_image, mem_allBits] at hl
  obtain ⟨t, ht, rfl⟩ := hl
  simp [← h, ht]

theorem prefix_of_mem_extBits {s l : List Bool} {k : ℕ} (h : l ∈ extBits s k) : s <+: l := by
  simp only [extBits, Finset.mem_image] at h
  obtain ⟨t, _, rfl⟩ := h
  exact ⟨t, rfl⟩

/-- **Kraft's inequality**: for a prefix-free code on a finite alphabet,
`∑ 2 ^ (-length)` is at most `1`. -/
theorem kraft_inequality {α : Type*} [Fintype α] [DecidableEq α] (c : α → List Bool)
    (hc : PrefixFree c) : ∑ a : α, (2 : ℝ) ^ (-((c a).length : ℤ)) ≤ 1 := by
  classical
  set m : ℕ := Finset.univ.sup (fun a : α => (c a).length) with hm
  have hle : ∀ a : α, (c a).length ≤ m := fun a => by
    rw [hm]; exact Finset.le_sup (f := fun a : α => (c a).length) (Finset.mem_univ a)
  -- the counting bound
  have hdisj : Set.PairwiseDisjoint (↑(Finset.univ : Finset α) : Set α)
      (fun a => extBits (c a) (m - (c a).length)) := by
    intro a _ b _ hab
    rw [Function.onFun, Finset.disjoint_left]
    intro l hl hl'
    have h1 : c a <+: l := prefix_of_mem_extBits hl
    have h2 : c b <+: l := prefix_of_mem_extBits hl'
    rcases (List.prefix_or_prefix_of_prefix h1 h2) with h | h
    · exact hc a b hab h
    · exact hc b a (Ne.symm hab) h
  have hsub : (Finset.univ.biUnion (fun a : α => extBits (c a) (m - (c a).length)))
      ⊆ allBits m :=
    Finset.biUnion_subset.2 (fun a _ => extBits_subset (by have := hle a; omega))
  have hcount : ∑ a : α, 2 ^ (m - (c a).length) ≤ 2 ^ m := by
    have h := Finset.card_le_card hsub
    rwa [Finset.card_biUnion hdisj, card_allBits,
      Finset.sum_congr rfl (fun a _ => card_extBits (c a) (m - (c a).length))] at h
  -- convert to the real statement
  have hcountR : ∑ a : α, (2 : ℝ) ^ (m - (c a).length) ≤ 2 ^ m := by
    have h := (Nat.cast_le (α := ℝ)).2 hcount
    push_cast at h
    exact h
  have hpow : ∀ a : α, (2 : ℝ) ^ (-((c a).length : ℤ)) = 2 ^ (m - (c a).length) / 2 ^ m :=
    fun a => two_zpow_neg_eq_div (hle a)
  rw [Finset.sum_congr rfl (fun a _ => hpow a), ← Finset.sum_div, div_le_one (by positivity)]
  exact hcountR

end CS

import RequestProject.Kraft

/-!
# Binary code trees

A `HTree α` is a binary tree whose leaves are labelled by symbols of `α`.  Such a tree
determines a binary code: the codeword of a symbol is the path from the root to its leaf.
-/

namespace CS

/-- A binary tree with leaves labelled by `α`. -/
inductive HTree (α : Type*) where
  | leaf : α → HTree α
  | node : HTree α → HTree α → HTree α
  deriving Inhabited

namespace HTree

variable {α : Type*}

/-- The multiset of leaf labels of a tree. -/
def leaves : HTree α → Multiset α
  | leaf a => {a}
  | node l r => l.leaves + r.leaves

@[simp] theorem leaves_leaf (a : α) : (leaf a).leaves = {a} := rfl
@[simp] theorem leaves_node (l r : HTree α) : (node l r).leaves = l.leaves + r.leaves := rfl

/-- The total weight of a tree. -/
def wt (w : α → ℝ) : HTree α → ℝ
  | leaf a => w a
  | node l r => wt w l + wt w r

@[simp] theorem wt_leaf (w : α → ℝ) (a : α) : (leaf a).wt w = w a := rfl
@[simp] theorem wt_node (w : α → ℝ) (l r : HTree α) :
    (node l r).wt w = l.wt w + r.wt w := rfl

/-- The cost (weighted external path length) of a tree. -/
def cost (w : α → ℝ) : HTree α → ℝ
  | leaf _ => 0
  | node l r => cost w l + cost w r + wt w l + wt w r

@[simp] theorem cost_leaf (w : α → ℝ) (a : α) : (leaf a).cost w = 0 := rfl
@[simp] theorem cost_node (w : α → ℝ) (l r : HTree α) :
    (node l r).cost w = l.cost w + r.cost w + l.wt w + r.wt w := rfl

theorem wt_eq_sum (w : α → ℝ) (t : HTree α) : t.wt w = (t.leaves.map w).sum := by
  induction t with
  | leaf a => simp
  | node l r ihl ihr => simp [ihl, ihr]

theorem wt_nonneg {w : α → ℝ} (hw : ∀ a, 0 ≤ w a) (t : HTree α) : 0 ≤ t.wt w := by
  induction t with
  | leaf a => simpa using hw a
  | node l r ihl ihr => simp only [wt_node]; linarith

theorem cost_nonneg {w : α → ℝ} (hw : ∀ a, 0 ≤ w a) (t : HTree α) : 0 ≤ t.cost w := by
  induction t with
  | leaf a => simp
  | node l r ihl ihr =>
      have := wt_nonneg hw l
      have := wt_nonneg hw r
      simp only [cost_node]; linarith

/-- The codeword assigned to a symbol by a tree: the path from the root to its leaf. -/
def encode [DecidableEq α] : HTree α → α → List Bool
  | leaf _, _ => []
  | node l r, a => if a ∈ l.leaves then false :: l.encode a else true :: r.encode a

@[simp] theorem encode_leaf [DecidableEq α] (b a : α) : (leaf b).encode a = [] := rfl

theorem encode_node_left [DecidableEq α] {l r : HTree α} {a : α} (h : a ∈ l.leaves) :
    (node l r).encode a = false :: l.encode a := by simp [encode, h]

theorem encode_node_right [DecidableEq α] {l r : HTree α} {a : α} (h : a ∉ l.leaves) :
    (node l r).encode a = true :: r.encode a := by simp [encode, h]

/-- Distinct symbols of a tree with distinct leaves get codewords none of which is a
prefix of another. -/
theorem encode_not_prefix [DecidableEq α] :
    ∀ (t : HTree α), t.leaves.Nodup → ∀ a ∈ t.leaves, ∀ b ∈ t.leaves, a ≠ b →
      ¬ (t.encode a <+: t.encode b) := by
  intro t
  induction t with
  | leaf x =>
      intro _ a ha b hb hab
      simp only [leaves_leaf, Multiset.mem_singleton] at ha hb
      exact absurd (ha.trans hb.symm) hab
  | node l r ihl ihr =>
      intro hnd a ha b hb hab
      rw [leaves_node, Multiset.nodup_add] at hnd
      obtain ⟨hl, hr, hdisj⟩ := hnd
      simp only [leaves_node, Multiset.mem_add] at ha hb
      by_cases hal : a ∈ l.leaves
      · by_cases hbl : b ∈ l.leaves
        · rw [encode_node_left hal, encode_node_left hbl, List.cons_prefix_cons]
          exact fun h => ihl hl a hal b hbl hab h.2
        · have hbr : b ∈ r.leaves := hb.resolve_left hbl
          rw [encode_node_left hal, encode_node_right hbl, List.cons_prefix_cons]
          simp
      · have har : a ∈ r.leaves := ha.resolve_left hal
        by_cases hbl : b ∈ l.leaves
        · rw [encode_node_right hal, encode_node_left hbl, List.cons_prefix_cons]
          simp
        · have hbr : b ∈ r.leaves := hb.resolve_left hbl
          rw [encode_node_right hal, encode_node_right hbl, List.cons_prefix_cons]
          exact fun h => ihr hr a har b hbr hab h.2

/-- The cost of a tree is the weighted sum of the codeword lengths. -/
theorem cost_eq_sum [DecidableEq α] (w : α → ℝ) :
    ∀ (t : HTree α), t.leaves.Nodup →
      t.cost w = (t.leaves.map (fun a => w a * (t.encode a).length)).sum := by
  intro t
  induction t with
  | leaf x => simp
  | node l r ihl ihr =>
      intro hnd
      rw [leaves_node, Multiset.nodup_add] at hnd
      obtain ⟨hl, hr, hdisj⟩ := hnd
      have hL : (l.leaves.map (fun a => w a * ((node l r).encode a).length)).sum
          = (l.leaves.map w).sum + (l.leaves.map (fun a => w a * (l.encode a).length)).sum := by
        rw [← Multiset.sum_map_add]
        refine congrArg Multiset.sum (Multiset.map_congr rfl ?_)
        intro x hx
        rw [encode_node_left hx]
        simp
        ring
      have hR : (r.leaves.map (fun a => w a * ((node l r).encode a).length)).sum
          = (r.leaves.map w).sum + (r.leaves.map (fun a => w a * (r.encode a).length)).sum := by
        rw [← Multiset.sum_map_add]
        refine congrArg Multiset.sum (Multiset.map_congr rfl ?_)
        intro x hx
        rw [encode_node_right (Multiset.disjoint_right.mp hdisj hx)]
        simp
        ring
      rw [leaves_node, Multiset.map_add, Multiset.sum_add, hL, hR, cost_node,
        ihl hl, ihr hr, wt_eq_sum, wt_eq_sum]
      ring

end HTree

end CS

import RequestProject.Kraft

/-!
# Kraft sums of multisets of codeword lengths, and normalisation of length assignments

The key combinatorial content of the optimality of Huffman's algorithm is the following
*normalisation* statement: given a collection of weighted items together with a length
assignment satisfying Kraft's inequality, if `b1` and `b2` are two items of minimal weight,
then the lengths may be modified, without increasing the total cost and without breaking
Kraft's inequality, so that `b1` and `b2` receive the same (positive) length.
-/

namespace CS

/-- The Kraft sum `∑ 2 ^ (-k)` of a multiset of codeword lengths. -/
noncomputable def kraftL (L : Multiset ℕ) : ℝ := (L.map (fun k => (2:ℝ) ^ (-(k:ℤ)))).sum

@[simp] theorem kraftL_zero : kraftL 0 = 0 := rfl

@[simp] theorem kraftL_cons (n : ℕ) (L : Multiset ℕ) :
    kraftL (n ::ₘ L) = (2:ℝ) ^ (-(n:ℤ)) + kraftL L := by
  simp [kraftL]

theorem kraftL_nonneg (L : Multiset ℕ) : 0 ≤ kraftL L := by
  refine Multiset.sum_nonneg ?_
  intro x hx
  simp only [Multiset.mem_map] at hx
  obtain ⟨k, _, rfl⟩ := hx
  positivity

/-- Writing the Kraft sum with a common denominator `2 ^ n`. -/
theorem kraftL_eq_div (n : ℕ) :
    ∀ (L : Multiset ℕ), (∀ k ∈ L, k ≤ n) →
      kraftL L = (((L.map (fun k => 2 ^ (n - k))).sum : ℕ) : ℝ) / 2 ^ n := by
  intro L
  induction L using Multiset.induction_on with
  | empty => simp
  | cons k L ih =>
      intro h
      have hk : k ≤ n := h k (Multiset.mem_cons_self k L)
      have hL : ∀ j ∈ L, j ≤ n := fun j hj => h j (Multiset.mem_cons_of_mem hj)
      rw [kraftL_cons, ih hL, two_zpow_neg_eq_div hk, Multiset.map_cons, Multiset.sum_cons]
      push_cast
      ring

theorem even_pow_sum (n : ℕ) :
    ∀ (L : Multiset ℕ), (∀ k ∈ L, k < n) → Even ((L.map (fun k => 2 ^ (n - k))).sum) := by
  intro L
  induction L using Multiset.induction_on with
  | empty => simp
  | cons k L ih =>
      intro h
      have hk : k < n := h k (Multiset.mem_cons_self k L)
      have hL : ∀ j ∈ L, j < n := fun j hj => h j (Multiset.mem_cons_of_mem hj)
      rw [Multiset.map_cons, Multiset.sum_cons]
      refine Even.add ?_ (ih hL)
      have : n - k ≠ 0 := by omega
      exact (Nat.even_pow).2 ⟨even_two, this⟩

/-- If the length `n` is strictly larger than all other lengths, it can be decreased by one
without breaking Kraft's inequality. -/
theorem kraftL_decrement {n : ℕ} {L : Multiset ℕ} (h : ∀ k ∈ L, k < n)
    (hK : kraftL (n ::ₘ L) ≤ 1) : kraftL ((n - 1) ::ₘ L) ≤ 1 := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simpa using hK
  set S : ℕ := (L.map (fun k => 2 ^ (n - k))).sum with hS
  have hLn : ∀ k ∈ L, k ≤ n := fun k hk => le_of_lt (h k hk)
  have h1 : kraftL (n ::ₘ L) = ((1 + S : ℕ) : ℝ) / 2 ^ n := by
    rw [kraftL_eq_div n _ (by
      intro k hk
      rcases Multiset.mem_cons.1 hk with rfl | hk
      · exact le_refl _
      · exact hLn k hk)]
    simp [hS]
  have h2 : kraftL ((n - 1) ::ₘ L) = ((2 + S : ℕ) : ℝ) / 2 ^ n := by
    rw [kraftL_eq_div n _ (by
      intro k hk
      rcases Multiset.mem_cons.1 hk with rfl | hk
      · omega
      · exact hLn k hk)]
    congr 1
    simp only [Multiset.map_cons, Multiset.sum_cons, ← hS]
    have : n - (n - 1) = 1 := by omega
    rw [this]
    push_cast
    ring
  rw [h1, div_le_one (by positivity)] at hK
  have hnat : 1 + S ≤ 2 ^ n := by
    have : ((1 + S : ℕ) : ℝ) ≤ ((2 ^ n : ℕ) : ℝ) := by push_cast; exact_mod_cast hK
    exact_mod_cast this
  have hev : Even S := even_pow_sum n L h
  have hev2 : Even (2 ^ n) := (Nat.even_pow).2 ⟨even_two, by omega⟩
  have hne : 1 + S ≠ 2 ^ n := by
    intro hcon
    obtain ⟨m, hm⟩ := hev
    obtain ⟨j, hj⟩ := hev2
    omega
  have hnat2 : 2 + S ≤ 2 ^ n := by omega
  rw [h2, div_le_one (by positivity)]
  calc ((2 + S : ℕ) : ℝ) ≤ ((2 ^ n : ℕ) : ℝ) := by exact_mod_cast hnat2
    _ = 2 ^ n := by push_cast; ring

/-! ### Cost of a weighted length assignment -/

variable {β : Type*}

/-- The multiset of lengths occurring in a length assignment. -/
def klen (M : Multiset (β × ℕ)) : Multiset ℕ := M.map Prod.snd

@[simp] theorem klen_cons (p : β × ℕ) (M : Multiset (β × ℕ)) :
    klen (p ::ₘ M) = p.2 ::ₘ klen M := by simp [klen]

@[simp] theorem klen_zero : klen (0 : Multiset (β × ℕ)) = 0 := rfl

/-- Total cost of a length assignment: each item `b` contributes a fixed amount `C b`
plus its weight `W b` times the length assigned to it. -/
noncomputable def gcost (C W : β → ℝ) (M : Multiset (β × ℕ)) : ℝ :=
  (M.map (fun p => C p.1 + W p.1 * p.2)).sum

@[simp] theorem gcost_cons (C W : β → ℝ) (p : β × ℕ) (M : Multiset (β × ℕ)) :
    gcost C W (p ::ₘ M) = C p.1 + W p.1 * p.2 + gcost C W M := by simp [gcost]

@[simp] theorem gcost_zero (C W : β → ℝ) : gcost C W (0 : Multiset (β × ℕ)) = 0 := rfl

/-- Rearranging the lengths so that the two lightest items `b1, b2` carry the two largest
lengths does not increase the cost. -/
theorem sort_two (C W : β → ℝ) (b1 b2 : β) (h12 : W b1 ≤ W b2) :
    ∀ (N : Multiset (β × ℕ)), (∀ p ∈ N, W b2 ≤ W p.1) → ∀ (x y : ℕ),
      ∃ (x' y' : ℕ) (N' : Multiset (β × ℕ)),
        N'.map Prod.fst = N.map Prod.fst ∧
        kraftL (klen ((b1, x') ::ₘ (b2, y') ::ₘ N'))
          = kraftL (klen ((b1, x) ::ₘ (b2, y) ::ₘ N)) ∧
        y' ≤ x' ∧ (∀ p ∈ N', p.2 ≤ y') ∧
        gcost C W ((b1, x') ::ₘ (b2, y') ::ₘ N')
          ≤ gcost C W ((b1, x) ::ₘ (b2, y) ::ₘ N) := by
  intro N
  induction N using Multiset.induction_on with
  | empty =>
      intro _ x y
      rcases le_total x y with hxy | hxy
      · refine ⟨y, x, 0, rfl, by simp [klen, kraftL]; ring, hxy, by simp, ?_⟩
        have hx : (x:ℝ) ≤ y := by exact_mod_cast hxy
        simp only [gcost_cons, gcost_zero]
        nlinarith [mul_nonneg (sub_nonneg.2 h12) (sub_nonneg.2 hx)]
      · exact ⟨x, y, 0, rfl, by simp, hxy, by simp, le_refl _⟩
  | cons q N ih =>
      intro hmem x y
      have hqW : W b2 ≤ W q.1 := hmem q (Multiset.mem_cons_self q N)
      have hNW : ∀ p ∈ N, W b2 ≤ W p.1 := fun p hp => hmem p (Multiset.mem_cons_of_mem hp)
      obtain ⟨x', y', N', hfst, hkr, hyx, hbd, hcost⟩ := ih hNW x y
      obtain ⟨u, c⟩ := q
      simp only at hqW ⊢
      by_cases hc : c ≤ y'
      · refine ⟨x', y', (u, c) ::ₘ N', by simp [hfst], ?_, hyx, ?_, ?_⟩
        · simp only [klen_cons, kraftL_cons] at hkr ⊢
          linarith
        · intro p hp
          rcases Multiset.mem_cons.1 hp with rfl | hp
          · exact hc
          · exact hbd p hp
        · simp only [gcost_cons] at hcost ⊢
          linarith
      · push_neg at hc
        by_cases hcx : c ≤ x'
        · refine ⟨x', c, (u, y') ::ₘ N', by simp [hfst], ?_, hcx, ?_, ?_⟩
          · simp only [klen_cons, kraftL_cons] at hkr ⊢
            linarith
          · intro p hp
            rcases Multiset.mem_cons.1 hp with rfl | hp
            · exact le_of_lt hc
            · exact le_trans (hbd p hp) (le_of_lt hc)
          · have hcy : (y':ℝ) ≤ (c:ℝ) := by exact_mod_cast le_of_lt hc
            simp only [gcost_cons] at hcost ⊢
            nlinarith [mul_nonneg (sub_nonneg.2 hqW) (sub_nonneg.2 hcy)]
        · push_neg at hcx
          refine ⟨c, x', (u, y') ::ₘ N', by simp [hfst], ?_, le_of_lt hcx, ?_, ?_⟩
          · simp only [klen_cons, kraftL_cons] at hkr ⊢
            linarith
          · intro p hp
            rcases Multiset.mem_cons.1 hp with rfl | hp
            · exact hyx
            · exact le_trans (hbd p hp) hyx
          · have hcx' : (x':ℝ) ≤ (c:ℝ) := by exact_mod_cast le_of_lt hcx
            have hyx' : (y':ℝ) ≤ (x':ℝ) := by exact_mod_cast hyx
            have h1u : W b1 ≤ W u := le_trans h12 hqW
            simp only [gcost_cons] at hcost ⊢
            nlinarith [mul_nonneg (sub_nonneg.2 h1u) (sub_nonneg.2 hcx'),
              mul_nonneg (sub_nonneg.2 hqW) (sub_nonneg.2 hyx')]

/-- If `b1` carries a length larger than all the others, it may be lowered to the length of
`b2` without breaking Kraft's inequality. -/
theorem lower_max (b1 b2 : β) :
    ∀ (d y : ℕ) (N : Multiset (β × ℕ)), (∀ p ∈ N, p.2 ≤ y) →
      kraftL (klen ((b1, y + d) ::ₘ (b2, y) ::ₘ N)) ≤ 1 →
      kraftL (klen ((b1, y) ::ₘ (b2, y) ::ₘ N)) ≤ 1 := by
  intro d
  induction d with
  | zero => intro y N _ h; simpa using h
  | succ d ih =>
      intro y N hbd hK
      refine ih y N hbd ?_
      have hlt : ∀ k ∈ klen ((b2, y) ::ₘ N), k < y + (d + 1) := by
        intro k hk
        simp only [klen_cons, Multiset.mem_cons] at hk
        rcases hk with rfl | hk
        · omega
        · simp only [klen, Multiset.mem_map] at hk
          obtain ⟨p, hp, rfl⟩ := hk
          have := hbd p hp
          omega
      have := kraftL_decrement hlt (by simpa using hK)
      have hEq : y + (d + 1) - 1 = y + d := by omega
      rw [hEq] at this
      simpa using this

theorem gcost_mono_length (C W : β → ℝ) (b : β) {x y : ℕ} (hW : 0 ≤ W b) (hxy : x ≤ y)
    (M : Multiset (β × ℕ)) :
    gcost C W ((b, x) ::ₘ M) ≤ gcost C W ((b, y) ::ₘ M) := by
  have : (x:ℝ) ≤ (y:ℝ) := by exact_mod_cast hxy
  simp only [gcost_cons]
  nlinarith

/-- **Normalisation.** If `b1, b2` are of minimal weight, any Kraft-admissible length
assignment can be replaced by one of no larger cost in which `b1` and `b2` receive the same
positive length. -/
theorem normalize (C W : β → ℝ) (b1 b2 : β) (h12 : W b1 ≤ W b2) (hW1 : 0 ≤ W b1)
    (N : Multiset (β × ℕ)) (hN : ∀ p ∈ N, W b2 ≤ W p.1) (x y : ℕ)
    (hK : kraftL (klen ((b1, x) ::ₘ (b2, y) ::ₘ N)) ≤ 1) :
    ∃ (c : ℕ) (N' : Multiset (β × ℕ)),
      N'.map Prod.fst = N.map Prod.fst ∧
      1 ≤ c ∧
      kraftL (klen ((b1, c) ::ₘ (b2, c) ::ₘ N')) ≤ 1 ∧
      gcost C W ((b1, c) ::ₘ (b2, c) ::ₘ N')
        ≤ gcost C W ((b1, x) ::ₘ (b2, y) ::ₘ N) := by
  obtain ⟨x', y', N', hfst, hkr, hyx, hbd, hcost⟩ := sort_two C W b1 b2 h12 N hN x y
  have hK' : kraftL (klen ((b1, x') ::ₘ (b2, y') ::ₘ N')) ≤ 1 := by rw [hkr]; exact hK
  have hd : x' = y' + (x' - y') := by omega
  have hK'' : kraftL (klen ((b1, y') ::ₘ (b2, y') ::ₘ N')) ≤ 1 := by
    refine lower_max b1 b2 (x' - y') y' N' hbd ?_
    rw [← hd]
    exact hK'
  refine ⟨y', N', hfst, ?_, hK'', ?_⟩
  · by_contra hcon
    push_neg at hcon
    interval_cases y'
    · simp only [klen_cons, kraftL_cons] at hK''
      have := kraftL_nonneg (klen N')
      norm_num at hK''
      linarith
  · calc gcost C W ((b1, y') ::ₘ (b2, y') ::ₘ N')
        ≤ gcost C W ((b1, x') ::ₘ (b2, y') ::ₘ N') :=
          gcost_mono_length C W b1 hW1 hyx _
    _ ≤ _ := hcost

end CS

import RequestProject.Tree
import RequestProject.Normalize

/-!
# Huffman's algorithm and its optimality

`buildList w ts` repeatedly replaces the two lightest trees of a list of trees by their
combination, until a single tree remains.  The main result `buildList_optimal` says that the
resulting tree has the least possible cost among all Kraft-admissible length assignments to
the initial trees.
-/

namespace CS

open HTree

variable {α : Type*}

/-- Comparison of trees by weight. -/
noncomputable def treeLe (w : α → ℝ) (a b : HTree α) : Bool := decide (a.wt w ≤ b.wt w)

theorem treeLe_trans (w : α → ℝ) (a b c : HTree α) :
    treeLe w a b = true → treeLe w b c = true → treeLe w a c = true := by
  simp only [treeLe, decide_eq_true_eq]
  exact le_trans

theorem treeLe_total (w : α → ℝ) (a b : HTree α) : (treeLe w a b || treeLe w b a) = true := by
  simp only [treeLe, Bool.or_eq_true, decide_eq_true_eq]
  exact le_total _ _

/-- One step of Huffman's algorithm: combine two trees of least weight. -/
noncomputable def combineStep (w : α → ℝ) (ts : List (HTree α)) : List (HTree α) :=
  match ts.mergeSort (treeLe w) with
  | t1 :: t2 :: rest => HTree.node t1 t2 :: rest
  | _ => ts

theorem combineStep_spec (w : α → ℝ) (ts : List (HTree α)) (h : 2 ≤ ts.length) :
    ∃ (t1 t2 : HTree α) (rest : List (HTree α)),
      combineStep w ts = HTree.node t1 t2 :: rest ∧
      (↑ts : Multiset (HTree α)) = t1 ::ₘ t2 ::ₘ (↑rest : Multiset (HTree α)) ∧
      t1.wt w ≤ t2.wt w ∧ (∀ u ∈ rest, t2.wt w ≤ u.wt w) ∧
      rest.length + 2 = ts.length := by
  have hlen : (ts.mergeSort (treeLe w)).length = ts.length := List.length_mergeSort _
  have hperm : (ts.mergeSort (treeLe w)).Perm ts := List.mergeSort_perm _ _
  have hpw : List.Pairwise (fun a b => treeLe w a b = true) (ts.mergeSort (treeLe w)) :=
    List.pairwise_mergeSort (treeLe_trans w) (treeLe_total w) ts
  rcases hs : ts.mergeSort (treeLe w) with _ | ⟨t1, _ | ⟨t2, rest⟩⟩
  · rw [hs] at hlen; simp at hlen; omega
  · rw [hs] at hlen; simp at hlen; omega
  · refine ⟨t1, t2, rest, ?_, ?_, ?_, ?_, ?_⟩
    · simp only [combineStep, hs]
    · have : (↑(ts.mergeSort (treeLe w)) : Multiset (HTree α)) = ↑ts :=
        Multiset.coe_eq_coe.2 hperm
      rw [hs] at this
      rw [← this]
      simp
    · rw [hs] at hpw
      have := (List.pairwise_cons.1 hpw).1 t2 (by simp)
      simpa [treeLe] using this
    · intro u hu
      rw [hs] at hpw
      have h2 := (List.pairwise_cons.1 (List.pairwise_cons.1 hpw).2).1 u hu
      simpa [treeLe] using h2
    · rw [hs] at hlen; simp at hlen; omega

theorem combineStep_length (w : α → ℝ) (ts : List (HTree α)) (h : 2 ≤ ts.length) :
    (combineStep w ts).length + 1 = ts.length := by
  obtain ⟨t1, t2, rest, heq, _, _, _, hlen⟩ := combineStep_spec w ts h
  rw [heq]
  simpa using hlen

/-- Huffman's algorithm: iterate `combineStep` until a single tree remains. -/
noncomputable def buildList (w : α → ℝ) (ts : List (HTree α)) : List (HTree α) :=
  if h : 2 ≤ ts.length then
    buildList w (combineStep w ts)
  else ts
termination_by ts.length
decreasing_by
  have := combineStep_length w ts h
  omega

theorem buildList_of_lt (w : α → ℝ) {ts : List (HTree α)} (h : ts.length < 2) :
    buildList w ts = ts := by
  rw [buildList]
  simp [Nat.not_le.2 h]

theorem buildList_of_le (w : α → ℝ) {ts : List (HTree α)} (h : 2 ≤ ts.length) :
    buildList w ts = buildList w (combineStep w ts) := by
  rw [buildList]
  simp [h]

/-- The total cost of a list of trees. -/
noncomputable def listCost (w : α → ℝ) (ts : List (HTree α)) : ℝ :=
  (ts.map (HTree.cost w)).sum

/-- Extract from a length assignment the entry attached to a given item. -/
theorem exists_pair_of_map_fst {β : Type*} {M : Multiset (β × ℕ)} {b : β} {s : Multiset β}
    (h : M.map Prod.fst = b ::ₘ s) :
    ∃ (k : ℕ) (M' : Multiset (β × ℕ)), M = (b, k) ::ₘ M' ∧ M'.map Prod.fst = s := by
  have hb : b ∈ M.map Prod.fst := by rw [h]; exact Multiset.mem_cons_self _ _
  rw [Multiset.mem_map] at hb
  obtain ⟨p, hp, hpb⟩ := hb
  obtain ⟨M', hM'⟩ := Multiset.exists_cons_of_mem hp
  refine ⟨p.2, M', ?_, ?_⟩
  · rw [hM']
    congr 1
    exact Prod.ext hpb rfl
  · rw [hM', Multiset.map_cons, hpb] at h
    exact (Multiset.cons_inj_right b).1 h

/-- **Optimality of Huffman's algorithm.**  For any Kraft-admissible assignment of codeword
lengths to the trees of `ts`, the tree produced by Huffman's algorithm costs no more. -/
theorem buildList_optimal (w : α → ℝ) (hw : ∀ a, 0 ≤ w a) :
    ∀ (n : ℕ) (ts : List (HTree α)), ts.length = n → ts ≠ [] →
      ∀ (M : Multiset (HTree α × ℕ)), M.map Prod.fst = (↑ts : Multiset (HTree α)) →
        kraftL (klen M) ≤ 1 →
        listCost w (buildList w ts) ≤ gcost (HTree.cost w) (HTree.wt w) M := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro ts hlen hne M hM hK
    by_cases hbig : 2 ≤ ts.length
    · -- inductive step
      obtain ⟨t1, t2, rest, hcs, hmul, hw12, hmin, hrl⟩ := combineStep_spec w ts hbig
      rw [hmul] at hM
      obtain ⟨a, M1, hM1, hM1f⟩ := exists_pair_of_map_fst hM
      obtain ⟨b, N, hN, hNf⟩ := exists_pair_of_map_fst hM1f
      subst hM1
      subst hN
      have hNW : ∀ p ∈ N, t2.wt w ≤ p.1.wt w := by
        intro p hp
        have : p.1 ∈ N.map Prod.fst := Multiset.mem_map_of_mem _ hp
        rw [hNf] at this
        exact hmin p.1 (by simpa using this)
      obtain ⟨c, N', hN'f, hc1, hK', hcost'⟩ :=
        normalize (HTree.cost w) (HTree.wt w) t1 t2 hw12 (wt_nonneg hw t1) N hNW a b hK
      -- the merged assignment
      set Mstar : Multiset (HTree α × ℕ) := (HTree.node t1 t2, c - 1) ::ₘ N' with hMstar
      have hcast : ((c - 1 : ℕ) : ℝ) = (c : ℝ) - 1 := by
        have : (1:ℕ) ≤ c := hc1
        push_cast [Nat.cast_sub this]
        ring
      have hKstar : kraftL (klen Mstar) ≤ 1 := by
        have hz : ((c - 1 : ℕ) : ℤ) = (c : ℤ) - 1 := by omega
        have h2 : (2:ℝ) ^ (-((c - 1 : ℕ) : ℤ)) = 2 * 2 ^ (-(c : ℤ)) := by
          rw [hz]
          rw [neg_sub, sub_eq_add_neg, zpow_add₀ (by norm_num : (2:ℝ) ≠ 0)]
          ring
        simp only [hMstar, klen_cons, kraftL_cons] at *
        rw [h2]
        linarith
      have hMstarf : Mstar.map Prod.fst = (↑(combineStep w ts) : Multiset (HTree α)) := by
        rw [hcs, hMstar]
        simp [hN'f, hNf]
      have hgc : gcost (HTree.cost w) (HTree.wt w) Mstar
          = gcost (HTree.cost w) (HTree.wt w) ((t1, c) ::ₘ (t2, c) ::ₘ N') := by
        simp only [hMstar, gcost_cons, cost_node, wt_node, hcast]
        ring
      have hlt : (combineStep w ts).length < n := by
        have := combineStep_length w ts hbig
        omega
      have hne' : combineStep w ts ≠ [] := by rw [hcs]; simp
      have := ih (combineStep w ts).length hlt (combineStep w ts) rfl hne' Mstar hMstarf hKstar
      rw [buildList_of_le w hbig]
      calc listCost w (buildList w (combineStep w ts))
          ≤ gcost (HTree.cost w) (HTree.wt w) Mstar := this
        _ = gcost (HTree.cost w) (HTree.wt w) ((t1, c) ::ₘ (t2, c) ::ₘ N') := hgc
        _ ≤ _ := hcost'
    · -- base case: a single tree
      push_neg at hbig
      rw [buildList_of_lt w hbig]
      obtain ⟨t, hts⟩ : ∃ t, ts = [t] := by
        match ts, hne, hbig with
        | [t], _, _ => exact ⟨t, rfl⟩
      subst hts
      have hcard : Multiset.card M = 1 := by
        have := congrArg Multiset.card hM
        simpa using this
      obtain ⟨p, hp⟩ := Multiset.card_eq_one.1 hcard
      subst hp
      have hp1 : p.1 = t := by
        have := hM
        simp at this
        exact this
      simp only [listCost, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
        gcost, Multiset.map_singleton, Multiset.sum_singleton, hp1]
      have : 0 ≤ t.wt w * (p.2 : ℝ) :=
        mul_nonneg (wt_nonneg hw t) (Nat.cast_nonneg _)
      linarith


/-! ### The Huffman code of a finite weighted alphabet -/

/-- The multiset of all leaf labels of a multiset of trees. -/
def msLeaves (M : Multiset (HTree α)) : Multiset α := (M.map HTree.leaves).sum

@[simp] theorem msLeaves_cons (t : HTree α) (M : Multiset (HTree α)) :
    msLeaves (t ::ₘ M) = t.leaves + msLeaves M := by simp [msLeaves]

theorem combineStep_leaves (w : α → ℝ) (ts : List (HTree α)) (h : 2 ≤ ts.length) :
    msLeaves (↑(combineStep w ts)) = msLeaves (↑ts) := by
  obtain ⟨t1, t2, rest, hcs, hmul, _, _, _⟩ := combineStep_spec w ts h
  rw [hcs, hmul]
  have : (↑(HTree.node t1 t2 :: rest) : Multiset (HTree α))
      = HTree.node t1 t2 ::ₘ (↑rest : Multiset (HTree α)) := rfl
  rw [this]
  simp [add_assoc]

theorem buildList_leaves (w : α → ℝ) :
    ∀ (n : ℕ) (ts : List (HTree α)), ts.length = n →
      msLeaves (↑(buildList w ts)) = msLeaves (↑ts) := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro ts hlen
    by_cases hbig : 2 ≤ ts.length
    · rw [buildList_of_le w hbig,
        ih (combineStep w ts).length (by have := combineStep_length w ts hbig; omega)
          (combineStep w ts) rfl, combineStep_leaves w ts hbig]
    · rw [buildList_of_lt w (Nat.not_le.1 hbig)]

theorem buildList_length_eq_one (w : α → ℝ) :
    ∀ (n : ℕ) (ts : List (HTree α)), ts.length = n → ts ≠ [] →
      (buildList w ts).length = 1 := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro ts hlen hne
    by_cases hbig : 2 ≤ ts.length
    · obtain ⟨t1, t2, rest, hcs, _, _, _, _⟩ := combineStep_spec w ts hbig
      rw [buildList_of_le w hbig]
      exact ih (combineStep w ts).length (by have := combineStep_length w ts hbig; omega)
        (combineStep w ts) rfl (by rw [hcs]; simp)
    · rw [buildList_of_lt w (Nat.not_le.1 hbig)]
      have : ts.length ≠ 0 := by simpa [List.length_eq_zero_iff] using hne
      omega

theorem exists_buildList_singleton (w : α → ℝ) (ts : List (HTree α)) (hne : ts ≠ []) :
    ∃ t : HTree α, buildList w ts = [t] := by
  have h := buildList_length_eq_one w ts.length ts rfl hne
  match hbl : buildList w ts, h with
  | [t], _ => exact ⟨t, rfl⟩

variable (α) in
/-- The initial list of one-leaf trees, one for each symbol. -/
def leafList [Fintype α] : List (HTree α) := (Finset.univ : Finset α).toList.map HTree.leaf

theorem coe_leafList [Fintype α] :
    (↑(leafList α) : Multiset (HTree α)) = (Finset.univ : Finset α).val.map HTree.leaf := by
  rw [leafList, ← Multiset.map_coe, Finset.coe_toList]

theorem leafList_ne_nil [Fintype α] [Nonempty α] : leafList α ≠ [] := by
  intro h
  have : ((leafList α : List (HTree α)) : Multiset (HTree α)) = 0 := by rw [h]; rfl
  rw [coe_leafList] at this
  have hcard : (Finset.univ : Finset α).card = 0 := by
    simpa using congrArg Multiset.card this
  simp [Finset.card_univ] at hcard
  exact absurd hcard (Fintype.card_ne_zero)

/-- The Huffman tree of a finite weighted alphabet. -/
noncomputable def huffmanTree [Fintype α] [Nonempty α] (w : α → ℝ) : HTree α :=
  (buildList w (leafList α)).headD (HTree.leaf (Classical.arbitrary α))

theorem buildList_leafList [Fintype α] [Nonempty α] (w : α → ℝ) :
    buildList w (leafList α) = [huffmanTree w] := by
  obtain ⟨t, ht⟩ := exists_buildList_singleton w (leafList α) leafList_ne_nil
  rw [huffmanTree, ht]
  rfl

theorem huffmanTree_leaves [Fintype α] [Nonempty α] (w : α → ℝ) :
    (huffmanTree w).leaves = (Finset.univ : Finset α).val := by
  have h := buildList_leaves w (leafList α).length (leafList α) rfl
  rw [buildList_leafList] at h
  have h1 : msLeaves (↑[huffmanTree w] : Multiset (HTree α)) = (huffmanTree w).leaves := by
    simp [msLeaves]
  have h2 : msLeaves (↑(leafList α) : Multiset (HTree α)) = (Finset.univ : Finset α).val := by
    rw [msLeaves, coe_leafList, Multiset.map_map]
    simpa using Multiset.sum_map_singleton (Finset.univ : Finset α).val
  rw [h1, h2] at h
  exact h

/-- The Huffman code of a finite weighted alphabet. -/
noncomputable def huffmanCode [Fintype α] [DecidableEq α] [Nonempty α] (w : α → ℝ) :
    α → List Bool := (huffmanTree w).encode

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

