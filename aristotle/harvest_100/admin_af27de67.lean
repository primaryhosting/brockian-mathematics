/-
# Huffman Optimal
Category: Computer Science
Target: CS.huffman_optimal
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/
import Mathlib

/-!
# Huffman Optimal
Category: Computer Science
Target: CS.huffman_optimal
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)

(Lean 4 requires `import` to be the first command in a file, so the header above the
import is a plain block comment and this is its module-docstring copy.)
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

set_option pp.fullNames true
set_option pp.structureInstances true
set_option pp.coercions.types true
set_option pp.funBinderTypes true
set_option pp.letVarTypes true
set_option pp.piBinderTypes true

set_option grind.warning false

namespace CS

/-!
## Binary code trees

A binary prefix code for a finite set of weighted symbols is (up to the irrelevant
choice of which child is `0` and which is `1`) the same thing as a binary tree whose
leaves carry the weights of the symbols.  The expected codeword length of the code is
the *weighted external path length* of the tree, i.e. `∑ᵢ wᵢ * depthᵢ`.
-/

/-- A binary code tree: leaves carry a (nonnegative) weight. -/
inductive HTree : Type
  | leaf : ℝ → HTree
  | node : HTree → HTree → HTree
  deriving Inhabited

namespace HTree

/-- Total weight of a tree, i.e. the sum of the weights of its leaves. -/
def weight : HTree → ℝ
  | leaf w => w
  | node l r => l.weight + r.weight

/-- The weighted external path length of a tree, `∑ᵢ wᵢ * depthᵢ`, defined by the
standard recursion.  This is the expected codeword length of the corresponding prefix
code (when the weights are the probabilities of the symbols). -/
def cost : HTree → ℝ
  | leaf _ => 0
  | node l r => l.cost + r.cost + l.weight + r.weight

/-- The multiset of pairs `(weight of leaf, depth of leaf)`. -/
def pairs : HTree → Multiset (ℝ × ℕ)
  | leaf w => {(w, 0)}
  | node l r =>
      (l.pairs.map (fun p => (p.1, p.2 + 1))) + (r.pairs.map (fun p => (p.1, p.2 + 1)))

/-- The multiset of leaf weights of a tree. -/
def leaves (t : HTree) : Multiset ℝ := t.pairs.map Prod.fst

/-- The multiset of leaf depths of a tree. -/
def depths (t : HTree) : Multiset ℕ := t.pairs.map Prod.snd

end HTree

/-- The weighted external path length of an abstract multiset of (weight, depth) pairs. -/
def wcost (M : Multiset (ℝ × ℕ)) : ℝ := (M.map (fun p => p.1 * (p.2 : ℝ))).sum

/-- Kraft equality: the multiset of depths `ds` is the depth multiset of a full binary
tree, expressed in purely arithmetical form: `∑ 2 ^ (D - d) = 2 ^ D` for every `D`
bounding all the depths (this is `∑ 2 ^ (-d) = 1` cleared of denominators). -/
def KraftEq (ds : Multiset ℕ) : Prop :=
  ∀ D : ℕ, (∀ d ∈ ds, d ≤ D) → (ds.map (fun d => 2 ^ (D - d))).sum = 2 ^ D

/-- Kraft's inequality `∑ 2 ^ (-d) ≤ 1`, cleared of denominators.  Depth multisets of
binary trees satisfy it, and so do the codeword lengths of any prefix-free code. -/
def KraftLe (ds : Multiset ℕ) : Prop :=
  ∀ D : ℕ, (∀ d ∈ ds, d ≤ D) → (ds.map (fun d => 2 ^ (D - d))).sum ≤ 2 ^ D

lemma KraftEq.le {ds : Multiset ℕ} (h : KraftEq ds) : KraftLe ds :=
  fun D hD => le_of_eq (h D hD)

/-!
## Basic facts about trees
-/

namespace HTree

lemma leaves_leaf (w : ℝ) : (leaf w).leaves = {w} := by simp [leaves, pairs]

lemma leaves_node (l r : HTree) : (node l r).leaves = l.leaves + r.leaves := by
  simp [leaves, pairs, Multiset.map_map, Function.comp]

lemma depths_leaf (w : ℝ) : (leaf w).depths = {0} := by simp [depths, pairs]

lemma depths_node (l r : HTree) :
    (node l r).depths = (l.depths.map (· + 1)) + (r.depths.map (· + 1)) := by
  simp [depths, pairs, Multiset.map_map, Function.comp]

lemma pairs_ne_zero (t : HTree) : t.pairs ≠ 0 := by
  induction t with
  | leaf w => simp [pairs]
  | node l r ihl ihr => simp [pairs, ihl, ihr]

lemma leaves_ne_zero (t : HTree) : t.leaves ≠ 0 := by
  simpa [leaves] using pairs_ne_zero t

lemma depths_ne_zero (t : HTree) : t.depths ≠ 0 := by
  simpa [depths] using pairs_ne_zero t

lemma weight_eq_sum_leaves (t : HTree) : t.weight = t.leaves.sum := by
  induction t with
  | leaf w => simp [weight, leaves_leaf]
  | node l r ihl ihr => simp [weight, leaves_node, ihl, ihr]

lemma wcost_shift (M : Multiset (ℝ × ℕ)) :
    wcost (M.map (fun p => (p.1, p.2 + 1))) = wcost M + (M.map Prod.fst).sum := by
  simp [wcost, Multiset.map_map, Function.comp]
  rw [← Multiset.sum_map_add]
  congr 1
  apply Multiset.map_congr rfl
  intro p _
  ring

lemma cost_eq_wcost (t : HTree) : t.cost = wcost t.pairs := by
  induction t with
  | leaf w => simp [cost, wcost, pairs]
  | node l r ihl ihr =>
      simp only [cost, pairs, wcost, Multiset.map_add, Multiset.sum_add]
      rw [← wcost, ← wcost, wcost_shift, wcost_shift, ← ihl, ← ihr,
        ← leaves, ← leaves, ← weight_eq_sum_leaves, ← weight_eq_sum_leaves]
      ring

lemma kraftEq_depths (t : HTree) : KraftEq t.depths := by
  induction t with
  | leaf w => intro D hD; simp [depths_leaf]
  | node l r ihl ihr =>
      intro D hD
      rw [depths_node] at hD ⊢
      obtain ⟨d0, hd0⟩ := Multiset.exists_mem_of_ne_zero (depths_ne_zero l)
      have hD1 : 1 ≤ D := by
        have := hD (d0 + 1) (by
          simp only [Multiset.mem_add, Multiset.mem_map]
          exact Or.inl ⟨d0, hd0, rfl⟩)
        omega
      have key : ∀ (s : Multiset ℕ), (∀ d ∈ s, d ≤ D - 1) →
          ((s.map (· + 1)).map (fun d => 2 ^ (D - d))).sum
            = (s.map (fun d => 2 ^ ((D - 1) - d))).sum := by
        intro s _
        rw [Multiset.map_map]
        congr 1
        apply Multiset.map_congr rfl
        intro d _
        simp only [Function.comp_apply]
        congr 1
        omega
      have hl : ∀ d ∈ l.depths, d ≤ D - 1 := by
        intro d hd
        have := hD (d + 1) (by
          simp only [Multiset.mem_add, Multiset.mem_map]
          exact Or.inl ⟨d, hd, rfl⟩)
        omega
      have hr : ∀ d ∈ r.depths, d ≤ D - 1 := by
        intro d hd
        have := hD (d + 1) (by
          simp only [Multiset.mem_add, Multiset.mem_map]
          exact Or.inr ⟨d, hd, rfl⟩)
        omega
      rw [Multiset.map_add, Multiset.sum_add, key _ hl, key _ hr, ihl _ hl, ihr _ hr]
      have hD1' : D - 1 + 1 = D := by omega
      calc 2 ^ (D - 1) + 2 ^ (D - 1) = 2 ^ (D - 1 + 1) := by ring
        _ = 2 ^ D := by rw [hD1']

end HTree

/-!
## The Huffman algorithm
-/

/-- Insert a tree into a list of trees, keeping the list sorted by weight. -/
noncomputable def insertByWeight (t : HTree) : List HTree → List HTree
  | [] => [t]
  | u :: us => if t.weight ≤ u.weight then t :: u :: us else u :: insertByWeight t us

lemma length_insertByWeight (t : HTree) (ts : List HTree) :
    (insertByWeight t ts).length = ts.length + 1 := by
  induction ts with
  | nil => simp [insertByWeight]
  | cons u us ih =>
      by_cases h : t.weight ≤ u.weight <;> simp [insertByWeight, h, ih]

/-- The main loop of Huffman's algorithm: repeatedly merge the two lightest trees. -/
noncomputable def huffAux : List HTree → HTree
  | [] => HTree.leaf 0
  | [t] => t
  | a :: b :: rest => huffAux (insertByWeight (HTree.node a b) rest)
termination_by ts => ts.length
decreasing_by simp [length_insertByWeight]

/-- Huffman's algorithm: sort the weights, turn them into leaves, and run the loop. -/
noncomputable def huffman (ws : List ℝ) : HTree :=
  huffAux ((List.insertionSort (· ≤ ·) ws).map HTree.leaf)

/-- The cost of the Huffman tree built from a list of weights, as a numerical
recursion (the list is assumed sorted). -/
noncomputable def hcostL : List ℝ → ℝ
  | [] => 0
  | [_] => 0
  | a :: b :: rest => (a + b) + hcostL (List.orderedInsert (· ≤ ·) (a + b) rest)
termination_by ws => ws.length
decreasing_by simp [List.orderedInsert_length]

/-- Huffman cost of a multiset of weights. -/
noncomputable def hc (M : Multiset ℝ) : ℝ := hcostL (M.sort (· ≤ ·))

/-!
## Correctness of the algorithm: the produced tree has the right leaves and cost
-/

lemma map_weight_insertByWeight (t : HTree) (ts : List HTree) :
    (insertByWeight t ts).map HTree.weight
      = List.orderedInsert (· ≤ ·) t.weight (ts.map HTree.weight) := by
  induction ts with
  | nil => simp [insertByWeight]
  | cons u us ih =>
      by_cases h : t.weight ≤ u.weight <;> simp [insertByWeight, h, ih]

lemma sum_cost_insertByWeight (t : HTree) (ts : List HTree) :
    ((insertByWeight t ts).map HTree.cost).sum = t.cost + (ts.map HTree.cost).sum := by
  induction ts with
  | nil => simp [insertByWeight]
  | cons u us ih =>
      by_cases h : t.weight ≤ u.weight <;> simp [insertByWeight, h, ih]
      ring

lemma sum_leaves_insertByWeight (t : HTree) (ts : List HTree) :
    ((insertByWeight t ts).map HTree.leaves).sum = t.leaves + (ts.map HTree.leaves).sum := by
  induction ts with
  | nil => simp [insertByWeight]
  | cons u us ih =>
      by_cases h : t.weight ≤ u.weight <;> simp [insertByWeight, h, ih]
      rw [← add_assoc, ← add_assoc, add_comm t.leaves u.leaves]

lemma cost_huffAux : ∀ ts : List HTree, ts ≠ [] →
    (huffAux ts).cost = (ts.map HTree.cost).sum + hcostL (ts.map HTree.weight) := by
  intro ts
  induction ts using huffAux.induct with
  | case1 => intro h; exact absurd rfl h
  | case2 t => intro _; simp [huffAux, hcostL]
  | case3 a b rest ih =>
      intro _
      rw [huffAux, ih (by simp [← List.length_pos_iff, length_insertByWeight]),
        sum_cost_insertByWeight, map_weight_insertByWeight]
      simp only [List.map_cons, hcostL, HTree.cost, HTree.weight, List.sum_cons]
      ring

lemma leaves_huffAux : ∀ ts : List HTree, ts ≠ [] →
    (huffAux ts).leaves = (ts.map HTree.leaves).sum := by
  intro ts
  induction ts using huffAux.induct with
  | case1 => intro h; exact absurd rfl h
  | case2 t => intro _; simp [huffAux]
  | case3 a b rest ih =>
      intro _
      rw [huffAux, ih (by simp [← List.length_pos_iff, length_insertByWeight]),
        sum_leaves_insertByWeight]
      simp [HTree.leaves_node, add_assoc]

lemma insertionSort_ne_nil (ws : List ℝ) (hne : ws ≠ []) :
    List.insertionSort (· ≤ ·) ws ≠ [] := by
  intro h
  have := (List.perm_insertionSort (α := ℝ) (· ≤ ·) ws).length_eq
  rw [h] at this
  exact hne (List.eq_nil_of_length_eq_zero this.symm)

lemma sum_singleton_map (l : List ℝ) :
    (l.map (fun w => ({w} : Multiset ℝ))).sum = (l : Multiset ℝ) := by
  induction l with
  | nil => rfl
  | cons a l ih => simp [ih]

/-- The Huffman tree for `ws` has exactly the weights `ws` at its leaves. -/
theorem huffman_leaves (ws : List ℝ) (hne : ws ≠ []) :
    (huffman ws).leaves = (ws : Multiset ℝ) := by
  have hs := insertionSort_ne_nil ws hne
  rw [huffman, leaves_huffAux _ (by simpa using hs)]
  have h1 : ((List.insertionSort (· ≤ ·) ws).map HTree.leaf).map HTree.leaves
      = (List.insertionSort (· ≤ ·) ws).map (fun w => ({w} : Multiset ℝ)) := by
    simp [List.map_map, Function.comp, HTree.leaves_leaf]
  rw [h1, sum_singleton_map]
  exact Multiset.coe_eq_coe.mpr (List.perm_insertionSort (· ≤ ·) ws)

/-!
## The recursion satisfied by the Huffman cost
-/

lemma sort_eq_of (l : List ℝ) (M : Multiset ℝ) (hp : (l : Multiset ℝ) = M)
    (hs : l.Pairwise (· ≤ ·)) : M.sort (· ≤ ·) = l := by
  refine List.Perm.eq_of_pairwise (le := (· ≤ ·)) (fun x y _ _ h1 h2 => le_antisymm h1 h2)
    (Multiset.pairwise_sort M (· ≤ ·)) hs ?_
  rw [← Multiset.coe_eq_coe, Multiset.sort_eq, hp]

lemma hc_singleton (w : ℝ) : hc {w} = 0 := by
  rw [hc, sort_eq_of [w] {w} rfl (by simp)]
  simp [hcostL]

lemma hc_cons2 (a b : ℝ) (M : Multiset ℝ) (hab : a ≤ b) (hb : ∀ w ∈ M, b ≤ w) :
    hc (a ::ₘ b ::ₘ M) = (a + b) + hc ((a + b) ::ₘ M) := by
  have hsM : ((M.sort (· ≤ ·) : List ℝ) : Multiset ℝ) = M := Multiset.sort_eq M (· ≤ ·)
  have h1 : (a ::ₘ b ::ₘ M).sort (· ≤ ·) = a :: b :: M.sort (· ≤ ·) := by
    refine sort_eq_of _ _ (by rw [← Multiset.cons_coe, ← Multiset.cons_coe, hsM]) ?_
    refine List.Pairwise.cons ?_ (List.Pairwise.cons ?_ (Multiset.pairwise_sort M (· ≤ ·)))
    · intro y hy
      rcases List.mem_cons.mp hy with h | h
      · exact h ▸ hab
      · exact le_trans hab (hb y (by rwa [← hsM]))
    · intro y hy
      exact hb y (by rwa [← hsM])
  have h2 : ((a + b) ::ₘ M).sort (· ≤ ·)
      = List.orderedInsert (· ≤ ·) (a + b) (M.sort (· ≤ ·)) := by
    refine sort_eq_of _ _ ?_ (List.Pairwise.orderedInsert _ _ (Multiset.pairwise_sort M (· ≤ ·)))
    calc ((List.orderedInsert (· ≤ ·) (a + b) (M.sort (· ≤ ·)) : List ℝ) : Multiset ℝ)
        = ((a + b) :: M.sort (· ≤ ·) : List ℝ) :=
          Quot.sound (List.perm_orderedInsert (· ≤ ·) (a + b) (M.sort (· ≤ ·)))
      _ = (a + b) ::ₘ M := by rw [← Multiset.cons_coe, hsM]
  rw [hc, hc, h1, h2, hcostL]

/-- The cost of the Huffman tree is the Huffman cost of the weight multiset. -/
theorem cost_huffman (ws : List ℝ) (hne : ws ≠ []) :
    (huffman ws).cost = hc (ws : Multiset ℝ) := by
  have hs := insertionSort_ne_nil ws hne
  rw [huffman, cost_huffAux _ (by simpa using hs), hc,
    sort_eq_of (List.insertionSort (· ≤ ·) ws) (ws : Multiset ℝ)
      (Multiset.coe_eq_coe.mpr (List.perm_insertionSort (· ≤ ·) ws))
      (List.pairwise_insertionSort (· ≤ ·) ws)]
  have hw : ∀ l : List ℝ, l.map (HTree.weight ∘ HTree.leaf) = l := by
    intro l
    induction l with
    | nil => rfl
    | cons a l ih => simp [HTree.weight, ih]
  have hcst : ∀ l : List ℝ, (l.map (HTree.cost ∘ HTree.leaf)).sum = 0 := by
    intro l
    induction l with
    | nil => rfl
    | cons a l ih => simp [HTree.cost, ih]
  simp [List.map_map, hw, hcst]

/-!
## The exchange (rearrangement) step
-/

lemma wcost_cons (p : ℝ × ℕ) (M : Multiset (ℝ × ℕ)) :
    wcost (p ::ₘ M) = p.1 * (p.2 : ℝ) + wcost M := by
  simp [wcost]

/-- If `a` is a minimal weight, it may be moved to a slot of maximal depth without
increasing the weighted external path length. -/
lemma exists_min_at_deep (M₁ : Multiset (ℝ × ℕ)) (x a : ℝ) (d : ℕ)
    (hd : ∀ p ∈ ((x, d) ::ₘ M₁), p.2 ≤ d)
    (ha : ∀ w ∈ (((x, d) ::ₘ M₁).map Prod.fst), a ≤ w)
    (hmem : a ∈ (((x, d) ::ₘ M₁).map Prod.fst)) :
    ∃ M₁' : Multiset (ℝ × ℕ),
      ((a, d) ::ₘ M₁').map Prod.fst = ((x, d) ::ₘ M₁).map Prod.fst ∧
      ((a, d) ::ₘ M₁').map Prod.snd = ((x, d) ::ₘ M₁).map Prod.snd ∧
      wcost ((a, d) ::ₘ M₁') ≤ wcost ((x, d) ::ₘ M₁) := by
  by_cases hx : a = x
  · exact ⟨M₁, by rw [hx], by rw [hx], by rw [hx]⟩
  · have hmem' : a ∈ M₁.map Prod.fst := by
      rw [Multiset.map_cons, Multiset.mem_cons] at hmem
      exact hmem.resolve_left hx
    obtain ⟨p, hp, hpa⟩ := Multiset.mem_map.mp hmem'
    obtain ⟨E, hE⟩ := Multiset.exists_cons_of_mem hp
    have hax : a ≤ x := ha x (by simp)
    have hpd : p.2 ≤ d := hd p (by rw [Multiset.mem_cons]; exact Or.inr hp)
    refine ⟨(x, p.2) ::ₘ E, ?_, ?_, ?_⟩
    · rw [hE]
      simp only [Multiset.map_cons]
      rw [← hpa]
      exact Multiset.cons_swap _ _ _
    · rw [hE]
      simp only [Multiset.map_cons]
    · rw [hE]
      simp only [wcost_cons]
      have hp1 : p.1 = a := hpa
      rw [hp1]
      have hcast : (p.2 : ℝ) ≤ (d : ℝ) := Nat.cast_le.mpr hpd
      nlinarith [sub_nonneg.mpr hax, sub_nonneg.mpr hcast]

/-!
## Optimality
-/

/-- Rescaling the Kraft sum from one bound `D` to a larger bound `D'`. -/
lemma kraft_scale (t : Multiset ℕ) (D D' : ℕ) (hD : ∀ e ∈ t, e ≤ D) (hDD' : D ≤ D') :
    (t.map (fun e => 2 ^ (D' - e))).sum = 2 ^ (D' - D) * (t.map (fun e => 2 ^ (D - e))).sum := by
  rw [← Multiset.sum_map_mul_left]
  congr 1
  apply Multiset.map_congr rfl
  intro e he
  have hsplit : D' - e = (D' - D) + (D - e) := by have := hD e he; omega
  rw [hsplit, pow_add]

/-- To check Kraft's inequality it suffices to check it for one bound `D₀`. -/
lemma kraftLe_of_base (t : Multiset ℕ) (D₀ : ℕ) (h0 : ∀ e ∈ t, e ≤ D₀)
    (hbase : (t.map (fun e => 2 ^ (D₀ - e))).sum ≤ 2 ^ D₀) : KraftLe t := by
  intro D hD
  rcases le_total D₀ D with h | h
  · rw [kraft_scale t D₀ D h0 h]
    calc 2 ^ (D - D₀) * (t.map (fun e => 2 ^ (D₀ - e))).sum
        ≤ 2 ^ (D - D₀) * 2 ^ D₀ := Nat.mul_le_mul_left _ hbase
      _ = 2 ^ D := by rw [← pow_add]; congr 1; omega
  · have hsc := kraft_scale t D D₀ hD h
    rw [hsc] at hbase
    have h2 : (2 : ℕ) ^ D₀ = 2 ^ (D₀ - D) * 2 ^ D := by rw [← pow_add]; congr 1; omega
    rw [h2] at hbase
    exact Nat.le_of_mul_le_mul_left hbase (pow_pos (by norm_num) _)

/-- Merging two deepest siblings preserves Kraft's inequality. -/
lemma kraft_merge (d : ℕ) (hd : 1 ≤ d) (s : Multiset ℕ) (hs : ∀ e ∈ s, e ≤ d)
    (h : KraftLe (d ::ₘ d ::ₘ s)) : KraftLe ((d - 1) ::ₘ s) := by
  refine kraftLe_of_base _ d ?_ ?_
  · intro e he
    rcases Multiset.mem_cons.mp he with rfl | he
    · omega
    · exact hs e he
  · have hall : ∀ e ∈ (d ::ₘ d ::ₘ s), e ≤ d := by
      intro e he
      rcases Multiset.mem_cons.mp he with rfl | he
      · exact le_rfl
      · rcases Multiset.mem_cons.mp he with rfl | he
        · exact le_rfl
        · exact hs e he
    have hh := h d hall
    simp only [Multiset.map_cons, Multiset.sum_cons, Nat.sub_self, pow_zero] at hh ⊢
    have hpow : (2 : ℕ) ^ (d - (d - 1)) = 2 := by
      have he : d - (d - 1) = 1 := by omega
      rw [he]; ring
    omega

/-- Lowering the unique deepest leaf by one level preserves Kraft's inequality. -/
lemma kraft_lower_one (d : ℕ) (hd : 1 ≤ d) (s : Multiset ℕ) (hs : ∀ e ∈ s, e < d)
    (h : KraftLe (d ::ₘ s)) : KraftLe ((d - 1) ::ₘ s) := by
  refine kraftLe_of_base _ (d - 1) ?_ ?_
  · intro e he
    rcases Multiset.mem_cons.mp he with rfl | he
    · exact le_rfl
    · have := hs e he; omega
  · have hall : ∀ e ∈ (d ::ₘ s), e ≤ d := by
      intro e he
      rcases Multiset.mem_cons.mp he with rfl | he
      · exact le_rfl
      · have := hs e he; omega
    have hh := h d hall
    simp only [Multiset.map_cons, Multiset.sum_cons, Nat.sub_self, pow_zero] at hh ⊢
    have hrw : (s.map (fun e => 2 ^ (d - e))).sum
        = 2 * (s.map (fun e => 2 ^ ((d - 1) - e))).sum := by
      rw [← Multiset.sum_map_mul_left]
      congr 1
      apply Multiset.map_congr rfl
      intro e he
      have hee : d - e = ((d - 1) - e) + 1 := by have := hs e he; omega
      rw [hee]; ring
    have h2 : (2 : ℕ) ^ d = 2 * 2 ^ (d - 1) := by
      conv_lhs => rw [show d = (d - 1) + 1 by omega]
      rw [pow_succ]; ring
    omega

/-- The key lower bound: for any assignment of weights to the leaves of any binary
tree (recorded abstractly as a multiset of (weight, depth) pairs satisfying Kraft's
equality), the Huffman cost of the weights is a lower bound for the weighted external
path length. -/
theorem hc_le_wcost : ∀ (n : ℕ) (M : Multiset (ℝ × ℕ)), (M.map Prod.snd).sum = n →
    M ≠ 0 → (∀ p ∈ M, 0 ≤ p.1) → KraftLe (M.map Prod.snd) →
    hc (M.map Prod.fst) ≤ wcost M := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n IH =>
  intro M hn hM0 hnn hK
  have hnnw : ∀ w ∈ M.map Prod.fst, 0 ≤ w := by
    intro w hw
    obtain ⟨p, hp, rfl⟩ := Multiset.mem_map.mp hw
    exact hnn p hp
  by_cases hcard : Multiset.card M = 1
  · obtain ⟨p, rfl⟩ := Multiset.card_eq_one.mp hcard
    have h1 : 0 ≤ p.1 := hnn p (Multiset.mem_singleton_self p)
    rw [Multiset.map_singleton, hc_singleton, wcost, Multiset.map_singleton,
      Multiset.sum_singleton]
    positivity
  · have hcard2 : 2 ≤ Multiset.card M := by
      have h0 : Multiset.card M ≠ 0 := fun h => hM0 (Multiset.card_eq_zero.mp h)
      omega
    obtain ⟨q, hq, hqmax⟩ := Multiset.exists_max_image (f := Prod.snd) hM0
    obtain ⟨M₀, hM₀⟩ := Multiset.exists_cons_of_mem hq
    have hM₀0 : M₀ ≠ 0 := by
      intro h
      rw [hM₀, h] at hcard2
      simp at hcard2
    by_cases hex : ∃ r ∈ M₀, r.2 = q.2
    · -- The generic case: two leaves of maximal depth `d`.
      obtain ⟨r, hrmem, hrd⟩ := hex
      obtain ⟨M₁, hM₁⟩ := Multiset.exists_cons_of_mem hrmem
      have hr_eta : ((r.1, q.2) : ℝ × ℕ) = r := by rw [← hrd]
      have hMeq : M = (q.1, q.2) ::ₘ ((r.1, q.2) ::ₘ M₁) := by rw [hr_eta, hM₀, hM₁]
      set d : ℕ := q.2 with hd_def
      have hdall : ∀ p ∈ M, p.2 ≤ d := hqmax
      have hallsnd : ∀ e ∈ M.map Prod.snd, e ≤ d := by
        intro e he
        obtain ⟨p, hp, rfl⟩ := Multiset.mem_map.mp he
        exact hdall p hp
      have hh := hK d hallsnd
      rw [hMeq] at hh
      simp only [Multiset.map_cons, Multiset.sum_cons, Nat.sub_self, pow_zero] at hh
      have hd1 : 1 ≤ d := by
        by_contra hcon
        have hd0 : d = 0 := by omega
        rw [hd0] at hh
        simp only [pow_zero] at hh
        omega
      -- the two lightest weights are moved to the two deepest slots
      obtain ⟨pa, hpa, hpamin⟩ := Multiset.exists_min_image (f := Prod.fst) hM0
      set a : ℝ := pa.1 with ha_def
      have hamem : a ∈ M.map Prod.fst := Multiset.mem_map_of_mem _ hpa
      have hamin : ∀ w ∈ M.map Prod.fst, a ≤ w := by
        intro w hw
        obtain ⟨p, hp, rfl⟩ := Multiset.mem_map.mp hw
        exact hpamin p hp
      obtain ⟨N₁, hN₁f, hN₁s, hN₁c⟩ :=
        exists_min_at_deep ((r.1, d) ::ₘ M₁) q.1 a d
          (by rw [← hMeq]; exact hdall) (by rw [← hMeq]; exact hamin)
          (by rw [← hMeq]; exact hamem)
      rw [← hMeq] at hN₁f hN₁s hN₁c
      have hN₁snd : N₁.map Prod.snd = d ::ₘ M₁.map Prod.snd := by
        have h1 : d ::ₘ N₁.map Prod.snd = d ::ₘ (d ::ₘ M₁.map Prod.snd) := by
          have := hN₁s
          rw [hMeq] at this
          simpa using this
        exact (Multiset.cons_inj_right d).mp h1
      have hdmem : d ∈ N₁.map Prod.snd := by
        rw [hN₁snd]; exact Multiset.mem_cons_self _ _
      obtain ⟨s0, hs0, hs0d⟩ := Multiset.mem_map.mp hdmem
      obtain ⟨N₂, hN₂⟩ := Multiset.exists_cons_of_mem hs0
      have hN₁eq : N₁ = (s0.1, d) ::ₘ N₂ := by rw [hN₂, ← hs0d]
      have hN₁0 : N₁ ≠ 0 := by
        rw [hN₁eq]; exact Multiset.cons_ne_zero
      have hN₁depth : ∀ p ∈ N₁, p.2 ≤ d := by
        intro p hp
        have : p.2 ∈ N₁.map Prod.snd := Multiset.mem_map_of_mem _ hp
        rw [hN₁snd] at this
        rcases Multiset.mem_cons.mp this with h | h
        · omega
        · obtain ⟨p', hp', hp'2⟩ := Multiset.mem_map.mp h
          have hp'M : p' ∈ M := by
            rw [hM₀, hM₁]
            exact Multiset.mem_cons_of_mem (Multiset.mem_cons_of_mem hp')
          have := hdall p' hp'M
          omega
      obtain ⟨pb, hpb, hpbmin⟩ := Multiset.exists_min_image (f := Prod.fst) hN₁0
      set b : ℝ := pb.1 with hb_def
      have hbmem : b ∈ N₁.map Prod.fst := Multiset.mem_map_of_mem _ hpb
      have hbmin : ∀ w ∈ N₁.map Prod.fst, b ≤ w := by
        intro w hw
        obtain ⟨p, hp, rfl⟩ := Multiset.mem_map.mp hw
        exact hpbmin p hp
      obtain ⟨N₂', hN₂'f, hN₂'s, hN₂'c⟩ :=
        exists_min_at_deep N₂ s0.1 b d
          (by rw [← hN₁eq]; exact hN₁depth) (by rw [← hN₁eq]; exact hbmin)
          (by rw [← hN₁eq]; exact hbmem)
      rw [← hN₁eq] at hN₂'f hN₂'s hN₂'c
      -- the rearranged configuration
      have hfst : a ::ₘ b ::ₘ N₂'.map Prod.fst = M.map Prod.fst := by
        have h1 : b ::ₘ N₂'.map Prod.fst = N₁.map Prod.fst := by simpa using hN₂'f
        have h2 : a ::ₘ N₁.map Prod.fst = M.map Prod.fst := by simpa using hN₁f
        rw [h1, h2]
      have hsnd : d ::ₘ d ::ₘ N₂'.map Prod.snd = M.map Prod.snd := by
        have h1 : d ::ₘ N₂'.map Prod.snd = N₁.map Prod.snd := by simpa using hN₂'s
        have h2 : d ::ₘ N₁.map Prod.snd = M.map Prod.snd := by simpa using hN₁s
        rw [h1, h2]
      have hcostle : wcost ((a, d) ::ₘ (b, d) ::ₘ N₂') ≤ wcost M := by
        have h1 : wcost ((b, d) ::ₘ N₂') ≤ wcost N₁ := hN₂'c
        have h2 : wcost ((a, d) ::ₘ N₁) ≤ wcost M := hN₁c
        rw [wcost_cons] at h2 ⊢
        simp only at h2 ⊢
        linarith
      -- apply the induction hypothesis to the merged configuration
      have hbmem' : b ∈ M.map Prod.fst := by rw [← hfst]; simp
      have hab : a ≤ b := hamin b hbmem'
      have hbmin' : ∀ w ∈ N₂'.map Prod.fst, b ≤ w := by
        intro w hw
        refine hbmin w ?_
        have h1 : b ::ₘ N₂'.map Prod.fst = N₁.map Prod.fst := by simpa using hN₂'f
        rw [← h1]
        exact Multiset.mem_cons_of_mem hw
      have ha0 : 0 ≤ a := hnnw a hamem
      have hb0 : 0 ≤ b := hnnw b hbmem'
      have hN₂'nn : ∀ p ∈ N₂', 0 ≤ p.1 := by
        intro p hp
        refine hnnw p.1 ?_
        rw [← hfst]
        exact Multiset.mem_cons_of_mem (Multiset.mem_cons_of_mem (Multiset.mem_map_of_mem _ hp))
      have hsumT : ((((a + b, d - 1) : ℝ × ℕ) ::ₘ N₂').map Prod.snd).sum < n := by
        have h1 : (M.map Prod.snd).sum = d + (d + (N₂'.map Prod.snd).sum) := by
          rw [← hsnd]; simp
        simp only [Multiset.map_cons, Multiset.sum_cons]
        omega
      have hIH := IH _ hsumT ((a + b, d - 1) ::ₘ N₂') rfl Multiset.cons_ne_zero
        (by
          intro p hp
          rcases Multiset.mem_cons.mp hp with rfl | hp
          · simpa using add_nonneg ha0 hb0
          · exact hN₂'nn p hp)
        (by
          simp only [Multiset.map_cons]
          refine kraft_merge d hd1 (N₂'.map Prod.snd) ?_ (by rw [hsnd]; exact hK)
          intro e he
          refine hallsnd e ?_
          rw [← hsnd]
          exact Multiset.mem_cons_of_mem (Multiset.mem_cons_of_mem he))
      simp only [Multiset.map_cons] at hIH
      have hcast : ((d - 1 : ℕ) : ℝ) = (d : ℝ) - 1 := by
        have : ((d : ℝ) - 1) = ((d - 1 : ℕ) : ℝ) := by
          rw [Nat.cast_sub hd1]; norm_num
        linarith
      calc hc (M.map Prod.fst) = hc (a ::ₘ b ::ₘ N₂'.map Prod.fst) := by rw [hfst]
        _ = (a + b) + hc ((a + b) ::ₘ N₂'.map Prod.fst) := hc_cons2 a b _ hab hbmin'
        _ ≤ (a + b) + wcost ((a + b, d - 1) ::ₘ N₂') := by linarith
        _ = wcost ((a, d) ::ₘ (b, d) ::ₘ N₂') := by
              rw [wcost_cons, wcost_cons, wcost_cons]
              simp only [hcast]
              ring
        _ ≤ wcost M := hcostle
    · -- Only one leaf of maximal depth: lower it by one level.
      have hlt : ∀ p ∈ M₀, p.2 < q.2 := by
        intro p hp
        exact lt_of_le_of_ne (hqmax p (by rw [hM₀]; exact Multiset.mem_cons_of_mem hp))
          (fun h => hex ⟨p, hp, h⟩)
      obtain ⟨r, hr⟩ := Multiset.exists_mem_of_ne_zero hM₀0
      have hd1 : 1 ≤ q.2 := by have := hlt r hr; omega
      have hMsnd : M.map Prod.snd = q.2 ::ₘ M₀.map Prod.snd := by rw [hM₀]; simp
      have hltm : ∀ e ∈ M₀.map Prod.snd, e < q.2 := by
        intro e he
        obtain ⟨p, hp, rfl⟩ := Multiset.mem_map.mp he
        exact hlt p hp
      have hq0 : 0 ≤ q.1 := hnn q hq
      have hfst : (((q.1, q.2 - 1) : ℝ × ℕ) ::ₘ M₀).map Prod.fst = M.map Prod.fst := by
        rw [hM₀]; simp
      have hsum : ((((q.1, q.2 - 1) : ℝ × ℕ) ::ₘ M₀).map Prod.snd).sum < n := by
        have h1 : (M.map Prod.snd).sum = q.2 + (M₀.map Prod.snd).sum := by rw [hMsnd]; simp
        simp only [Multiset.map_cons, Multiset.sum_cons]
        omega
      have hIH := IH _ hsum (((q.1, q.2 - 1) : ℝ × ℕ) ::ₘ M₀) rfl Multiset.cons_ne_zero
        (by
          intro p hp
          rcases Multiset.mem_cons.mp hp with rfl | hp
          · simpa using hq0
          · exact hnn p (by rw [hM₀]; exact Multiset.mem_cons_of_mem hp))
        (by
          simp only [Multiset.map_cons]
          exact kraft_lower_one q.2 hd1 (M₀.map Prod.snd) hltm (by rw [← hMsnd]; exact hK))
      rw [hfst] at hIH
      refine hIH.trans ?_
      have hcast : ((q.2 - 1 : ℕ) : ℝ) = (q.2 : ℝ) - 1 := by
        have : ((q.2 : ℝ) - 1) = ((q.2 - 1 : ℕ) : ℝ) := by
          rw [Nat.cast_sub hd1]; norm_num
        linarith
      rw [hM₀, wcost_cons, wcost_cons]
      simp only [hcast]
      have : q.1 * ((q.2 : ℝ) - 1) ≤ q.1 * (q.2 : ℝ) := by nlinarith
      linarith

/-- **Huffman coding is optimal.**  For any list of nonnegative weights `ws` (e.g. the
probabilities of the symbols of a source), the Huffman tree `huffman ws` has the right
leaf weights (`huffman_leaves`) and its expected codeword length `cost` is minimal
among all binary prefix codes (binary trees) with the same multiset of leaf weights. -/
theorem huffman_optimal (ws : List ℝ) (hne : ws ≠ []) (hpos : ∀ w ∈ ws, 0 ≤ w)
    (t : HTree) (ht : t.leaves = (ws : Multiset ℝ)) :
    (huffman ws).cost ≤ t.cost := by
  rw [cost_huffman ws hne, HTree.cost_eq_wcost, ← ht]
  have hleaves : t.leaves = t.pairs.map Prod.fst := rfl
  rw [hleaves]
  refine hc_le_wcost ((t.pairs.map Prod.snd).sum) t.pairs rfl (HTree.pairs_ne_zero t) ?_
    (HTree.kraftEq_depths t).le
  intro p hp
  have hmem : p.1 ∈ t.leaves := Multiset.mem_map_of_mem _ hp
  rw [ht] at hmem
  exact hpos _ (by simpa using hmem)

/-!
## Prefix codes

A binary prefix code is a family of codewords, no one of which is a prefix of another.
Kraft's inequality holds for such families, hence Huffman's algorithm also minimizes
the expected codeword length among all prefix codes for the given weights.
-/

/-- A list of binary codewords is prefix-free if no codeword is a prefix of another. -/
def PrefixFree (cs : List (List Bool)) : Prop :=
  cs.Pairwise (fun a b => ¬ a <+: b ∧ ¬ b <+: a)

lemma prefixFree_eq_of_nil_mem (cs : List (List Bool)) (h : PrefixFree cs) (hnil : [] ∈ cs) :
    cs = [[]] := by
  match cs with
  | [] => simp at hnil
  | [c] =>
      rcases List.mem_singleton.mp hnil with h1
      rw [← h1]
  | c1 :: c2 :: rest =>
      exfalso
      rw [PrefixFree, List.pairwise_cons] at h
      rcases List.mem_cons.mp hnil with h1 | h1
      · exact (h.1 c2 (by simp)).1 (by rw [← h1]; exact List.nil_prefix)
      · exact (h.1 [] h1).2 List.nil_prefix

lemma prefix_of_tail_prefix (a b : List Bool) (h : a.tail <+: b.tail) (ha : a ≠ []) (hb : b ≠ [])
    (hh : a.headI = b.headI) : a <+: b := by
  cases a with
  | nil => exact absurd rfl ha
  | cons x xs =>
    cases b with
    | nil => exact absurd rfl hb
    | cons y ys =>
      simp only [List.headI] at hh
      subst hh
      simpa using h

/-- **Kraft's inequality** for prefix-free binary codes, in denominator-free form:
`∑ 2 ^ (D - |c|) ≤ 2 ^ D` for every `D` bounding all codeword lengths. -/
theorem kraft_inequality : ∀ (D : ℕ) (cs : List (List Bool)), PrefixFree cs →
    (∀ c ∈ cs, c.length ≤ D) → (cs.map (fun c => 2 ^ (D - c.length))).sum ≤ 2 ^ D := by
  intro D
  induction D with
  | zero =>
      intro cs hpf hlen
      by_cases hcs : cs = []
      · simp [hcs]
      · have hnil : [] ∈ cs := by
          obtain ⟨c, hc⟩ := List.exists_mem_of_ne_nil cs hcs
          have h1 := hlen c hc
          have h2 : c = [] := List.eq_nil_of_length_eq_zero (by omega)
          rwa [← h2]
        rw [prefixFree_eq_of_nil_mem cs hpf hnil]
        simp
  | succ D ih =>
      intro cs hpf hlen
      by_cases hnil : [] ∈ cs
      · rw [prefixFree_eq_of_nil_mem cs hpf hnil]
        simp
      · have hne : ∀ c ∈ cs, c ≠ [] := by
          intro c hc h
          exact hnil (h ▸ hc)
        have key : ∀ q : List Bool → Bool,
            (∀ a ∈ cs.filter q, ∀ b ∈ cs.filter q, a.headI = b.headI) →
            ((cs.filter q).map (fun c => 2 ^ (D + 1 - c.length))).sum ≤ 2 ^ D := by
          intro q hq
          have hsub : ∀ c ∈ cs.filter q, c ∈ cs := fun c hc => List.mem_of_mem_filter hc
          have hmapeq : ((cs.filter q).map (fun c => 2 ^ (D + 1 - c.length))).sum
              = (((cs.filter q).map List.tail).map (fun c => 2 ^ (D - c.length))).sum := by
            rw [List.map_map]
            congr 1
            apply List.map_congr_left
            intro c hc
            have hc0 : c ≠ [] := hne c (hsub c hc)
            simp only [Function.comp_apply, List.length_tail]
            congr 1
            have : 1 ≤ c.length := List.length_pos_iff.mpr hc0
            omega
          rw [hmapeq]
          refine ih _ ?_ ?_
          · rw [PrefixFree, List.pairwise_map]
            refine List.Pairwise.imp_of_mem ?_ (hpf.filter q)
            intro a b ha hb hab
            refine ⟨fun hcon => hab.1 ?_, fun hcon => hab.2 ?_⟩
            · exact prefix_of_tail_prefix a b hcon (hne a (hsub a ha)) (hne b (hsub b hb))
                (hq a ha b hb)
            · exact prefix_of_tail_prefix b a hcon (hne b (hsub b hb)) (hne a (hsub a ha))
                (hq b hb a ha)
          · intro c hc
            obtain ⟨c0, hc0, rfl⟩ := List.mem_map.mp hc
            have h1 : c0.length ≤ D + 1 := hlen c0 (hsub c0 hc0)
            simp only [List.length_tail]
            omega
        have hsplit : (cs.map (fun c => 2 ^ (D + 1 - c.length))).sum
            = (((cs.filter (fun c => c.headI)).map (fun c => 2 ^ (D + 1 - c.length))).sum
              + ((cs.filter (fun c => !(c.headI))).map (fun c => 2 ^ (D + 1 - c.length))).sum) := by
          have hperm := List.filter_append_perm (fun c : List Bool => c.headI) cs
          have h2 := (hperm.map (fun c : List Bool => 2 ^ (D + 1 - c.length))).sum_eq
          rw [← h2, List.map_append, List.sum_append]
        have h1 := key (fun c => c.headI) (by
          intro a ha b hb
          have h1 := (List.mem_filter.mp ha).2
          have h2 := (List.mem_filter.mp hb).2
          simp only at h1 h2
          rw [h1, h2])
        have h2 := key (fun c => !(c.headI)) (by
          intro a ha b hb
          have h1 := (List.mem_filter.mp ha).2
          have h2 := (List.mem_filter.mp hb).2
          simp only [Bool.not_eq_eq_eq_not, Bool.not_true] at h1 h2
          rw [h1, h2])
        rw [hsplit]
        have hp2 : (2 : ℕ) ^ (D + 1) = 2 ^ D + 2 ^ D := by ring
        omega

/-- **Huffman coding minimizes the expected codeword length among prefix codes.**
Here `code` lists, for each symbol, its weight and its binary codeword; the codewords
are assumed to form a prefix-free code, and the weights are (a permutation of) `ws`.
The Huffman tree for `ws` then has expected codeword length at most
`∑ᵢ wᵢ * |codewordᵢ|`. -/
theorem huffman_optimal_prefix_code (ws : List ℝ) (hne : ws ≠ []) (hpos : ∀ w ∈ ws, 0 ≤ w)
    (code : List (ℝ × List Bool))
    (hcode : ((code.map Prod.fst : List ℝ) : Multiset ℝ) = (ws : Multiset ℝ))
    (hpf : PrefixFree (code.map Prod.snd)) :
    (huffman ws).cost ≤ (code.map (fun p => p.1 * (p.2.length : ℝ))).sum := by
  set M : Multiset (ℝ × ℕ) := ((code.map (fun p => (p.1, p.2.length)) : List (ℝ × ℕ)) :
    Multiset (ℝ × ℕ)) with hM
  have hMfst : M.map Prod.fst = (ws : Multiset ℝ) := by
    rw [hM, ← hcode, Multiset.map_coe, List.map_map]
    rfl
  have hMsnd : M.map Prod.snd
      = (((code.map Prod.snd).map List.length : List ℕ) : Multiset ℕ) := by
    rw [hM, Multiset.map_coe, List.map_map, List.map_map]
    rfl
  have hwcost : wcost M = (code.map (fun p => p.1 * (p.2.length : ℝ))).sum := by
    rw [hM, wcost, Multiset.map_coe, List.map_map]
    rfl
  have hM0 : M ≠ 0 := by
    intro h
    rw [hM, Multiset.coe_eq_zero, List.map_eq_nil_iff] at h
    rw [h] at hcode
    exact hne (by simpa using hcode.symm)
  have hnn : ∀ p ∈ M, 0 ≤ p.1 := by
    intro p hp
    have hmem : p.1 ∈ M.map Prod.fst := Multiset.mem_map_of_mem _ hp
    rw [hMfst] at hmem
    exact hpos _ (by simpa using hmem)
  have hK : KraftLe (M.map Prod.snd) := by
    intro D hD
    have hlen : ∀ c ∈ code.map Prod.snd, c.length ≤ D := by
      intro c hc
      refine hD c.length ?_
      rw [hMsnd]
      simpa using List.mem_map_of_mem hc
    have hkr := kraft_inequality D (code.map Prod.snd) hpf hlen
    rw [hMsnd, Multiset.map_coe]
    simpa [List.map_map] using hkr
  rw [cost_huffman ws hne, ← hMfst, ← hwcost]
  exact hc_le_wcost _ M rfl hM0 hnn hK

/-!
## Sanity checks
-/

/-- Two equally likely symbols get one bit each. -/
example : (huffman [1, 1]).cost = 2 := by
  norm_num [huffman, List.insertionSort, List.orderedInsert, huffAux, insertByWeight,
    HTree.cost, HTree.weight]

/-- The Huffman code for the distribution `(1/2, 1/4, 1/4)` has expected length `3/2`. -/
example : (huffman [0.5, 0.25, 0.25]).cost = 1.5 := by
  norm_num [huffman, List.insertionSort, List.orderedInsert, huffAux, insertByWeight,
    HTree.cost, HTree.weight]

/-- `cost` really is the weighted external path length. -/
example : (HTree.node (HTree.leaf 1) (HTree.node (HTree.leaf 2) (HTree.leaf 3))).cost
    = 1 * 1 + 2 * 2 + 3 * 2 := by
  norm_num [HTree.cost, HTree.weight]

end CS

#print axioms CS.huffman_optimal
#print axioms CS.huffman_optimal_prefix_code
#print axioms CS.huffman_leaves
#print axioms CS.kraft_inequality

