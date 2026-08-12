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

/-!
# Information-theoretic lower bound for comparison sorting of 4 elements

We model a comparison-based sorting algorithm on `n` inputs as a binary decision tree
(`CS.CompTree n`): each internal node compares two input positions `i j` (asking `a i ≤ a j`)
and branches accordingly; each leaf outputs a permutation, which is meant to list the input
positions in sorted order.

A tree *sorts* if, for every injective input `a : Fin n → ℕ`, the output permutation `p`
satisfies that `a ∘ p` is strictly monotone.

The main theorem `CS.sorting_lb_4` states that any comparison tree that sorts `4` elements has
depth at least `⌈log₂ (4!)⌉ = 5`, i.e. it performs at least 5 comparisons in the worst case.
-/

namespace CS

/-- A comparison-based decision tree on `n` inputs: internal nodes compare two positions,
leaves output a permutation. -/
inductive CompTree (n : ℕ) : Type
  | leaf : Equiv.Perm (Fin n) → CompTree n
  | node : Fin n → Fin n → CompTree n → CompTree n → CompTree n

namespace CompTree

variable {n : ℕ}

/-- The depth of a comparison tree: the worst-case number of comparisons performed. -/
def depth : CompTree n → ℕ
  | leaf _ => 0
  | node _ _ l r => max (depth l) (depth r) + 1

/-- Running the tree on the input `a`: at node `(i, j)` we branch on whether `a i ≤ a j`. -/
def run (a : Fin n → ℕ) : CompTree n → Equiv.Perm (Fin n)
  | leaf p => p
  | node i j l r => if a i ≤ a j then run a l else run a r

/-- The finite set of permutations occurring as leaf labels of the tree. -/
def outputs : CompTree n → Finset (Equiv.Perm (Fin n))
  | leaf p => {p}
  | node _ _ l r => outputs l ∪ outputs r

/-- A tree sorts if on every injective input it outputs a permutation putting the input in
increasing order. -/
def Sorts (t : CompTree n) : Prop :=
  ∀ a : Fin n → ℕ, Function.Injective a → StrictMono (a ∘ (run a t))

theorem card_outputs_le (t : CompTree n) : (outputs t).card ≤ 2 ^ depth t := by
  induction t with
  | leaf p => simp [outputs, depth]
  | node i j l r ihl ihr =>
      refine le_trans (Finset.card_union_le _ _) ?_
      have h1 : (2 : ℕ) ^ depth l ≤ 2 ^ (max (depth l) (depth r)) :=
        Nat.pow_le_pow_right (by norm_num) (le_max_left _ _)
      have h2 : (2 : ℕ) ^ depth r ≤ 2 ^ (max (depth l) (depth r)) :=
        Nat.pow_le_pow_right (by norm_num) (le_max_right _ _)
      simp only [depth, pow_succ]
      omega

theorem run_mem_outputs (a : Fin n → ℕ) (t : CompTree n) : run a t ∈ outputs t := by
  induction t with
  | leaf p => simp [outputs, run]
  | node i j l r ihl ihr =>
      simp only [run, outputs, Finset.mem_union]
      split
      · exact Or.inl ihl
      · exact Or.inr ihr

end CompTree

theorem strictMono_perm_eq_refl {n : ℕ} (e : Equiv.Perm (Fin n))
    (h : StrictMono (e : Fin n → Fin n)) : e = Equiv.refl _ := by
  have hs : StrictMono (e.symm : Fin n → Fin n) := by
    intro a b hab
    by_contra hc
    push_neg at hc
    have := h.monotone hc
    simp at this
    omega
  ext k
  have h2 : k ≤ e.symm k := hs.le_apply
  have h3 : e k ≤ k := by simpa using h.monotone h2
  have h1 : k ≤ e k := h.le_apply
  simp
  omega

theorem CompTree.outputs_eq_univ {n : ℕ} (t : CompTree n) (h : t.Sorts) :
    t.outputs = Finset.univ := by
  refine Finset.eq_univ_of_forall ?_
  intro q
  set s : Equiv.Perm (Fin n) := q⁻¹ with hs
  set a : Fin n → ℕ := fun i => ((s i : Fin n) : ℕ) with ha
  have hinj : Function.Injective a := by
    intro x y hxy
    simp only [ha] at hxy
    exact s.injective (Fin.ext hxy)
  have hmono := h a hinj
  set p := run a t with hp
  have hsm : StrictMono ((p.trans s) : Fin n → Fin n) := by
    intro x y hxy
    have hlt := hmono hxy
    exact Fin.lt_def.mpr hlt
  have heq := strictMono_perm_eq_refl _ hsm
  have hpq : p = q := by
    have := congrArg (fun f => Equiv.trans f s.symm) heq
    simpa [hs, Equiv.trans_assoc] using this
  rw [← hpq, hp]
  exact run_mem_outputs a t

/-!
### Non-vacuity: comparison trees that sort `4` elements do exist

To confirm that the hypothesis `Sorts` is satisfiable (so the lower bound is not vacuous), we
build an explicit (very inefficient) comparison tree that sorts `4` elements: it scans over all
permutations, checking each one with three comparisons, and outputs the first that works.
-/

/-- `a ∘ q` is nondecreasing along the consecutive indices of `Fin 4`. -/
def Chain4 (a : Fin 4 → ℕ) (q : Equiv.Perm (Fin 4)) : Prop :=
  a (q 0) ≤ a (q 1) ∧ a (q 1) ≤ a (q 2) ∧ a (q 2) ≤ a (q 3)

instance (a : Fin 4 → ℕ) (q : Equiv.Perm (Fin 4)) : Decidable (Chain4 a q) :=
  inferInstanceAs (Decidable (_ ∧ _ ∧ _))

/-- Test the candidate permutation `q` using three comparisons; on success output `q`,
otherwise continue with `rest`. -/
def check4 (q : Equiv.Perm (Fin 4)) (rest : CompTree 4) : CompTree 4 :=
  CompTree.node (q 0) (q 1)
    (CompTree.node (q 1) (q 2)
      (CompTree.node (q 2) (q 3) (CompTree.leaf q) rest) rest) rest

theorem run_check4 (a : Fin 4 → ℕ) (q : Equiv.Perm (Fin 4)) (rest : CompTree 4) :
    CompTree.run a (check4 q rest) = if Chain4 a q then q else CompTree.run a rest := by
  unfold check4 Chain4
  simp only [CompTree.run]
  split_ifs with h1 h2 h3 h4 <;> simp_all

theorem chain4_of_run_foldr (a : Fin 4 → ℕ) (l : List (Equiv.Perm (Fin 4)))
    (base : CompTree 4) (h : ∃ q ∈ l, Chain4 a q) :
    Chain4 a (CompTree.run a (l.foldr check4 base)) := by
  induction l with
  | nil => simp at h
  | cons q l ih =>
      rw [List.foldr_cons, run_check4]
      split_ifs with hq
      · exact hq
      · refine ih ?_
        obtain ⟨r, hr, hcr⟩ := h
        rcases List.mem_cons.1 hr with rfl | hr'
        · exact absurd hcr hq
        · exact ⟨r, hr', hcr⟩

theorem strictMono_of_chain4 (a : Fin 4 → ℕ) (hinj : Function.Injective a)
    (q : Equiv.Perm (Fin 4)) (h : Chain4 a q) : StrictMono (a ∘ (q : Fin 4 → Fin 4)) := by
  refine Monotone.strictMono_of_injective ?_ (hinj.comp q.injective)
  rw [Fin.monotone_iff_le_succ]
  intro i
  fin_cases i
  · simpa using h.1
  · simpa using h.2.1
  · simpa using h.2.2

/-- There is a comparison tree that sorts `4` elements, so the lower bound below is not vacuous. -/
theorem exists_sorting_tree_4 : ∃ t : CompTree 4, t.Sorts := by
  refine ⟨((Finset.univ : Finset (Equiv.Perm (Fin 4))).toList).foldr check4 (CompTree.leaf 1), ?_⟩
  intro a hinj
  have hex : ∃ q ∈ (Finset.univ : Finset (Equiv.Perm (Fin 4))).toList, Chain4 a q := by
    refine ⟨Tuple.sort a, by simp, ?_⟩
    have hm := Tuple.monotone_sort a
    exact ⟨hm (by decide), hm (by decide), hm (by decide)⟩
  exact strictMono_of_chain4 a hinj _ (chain4_of_run_foldr a _ _ hex)

/-- **Comparison-sorting lower bound.**
Any comparison tree that correctly sorts `n` elements has depth at least `⌈log₂ (n!)⌉`,
i.e. it performs at least `⌈log₂ (n!)⌉` comparisons in the worst case. -/
theorem sorting_lb (n : ℕ) (t : CompTree n) (h : t.Sorts) :
    Nat.clog 2 (Nat.factorial n) ≤ t.depth := by
  have hcard := t.card_outputs_le
  rw [CompTree.outputs_eq_univ t h, Finset.card_univ, Fintype.card_perm, Fintype.card_fin] at hcard
  exact (Nat.clog_le_iff_le_pow one_lt_two).2 hcard

/-- **Comparison-sorting lower bound for 4 elements.**
Any comparison tree that correctly sorts `4` elements needs at least
`⌈log₂ (4!)⌉ = 5` comparisons in the worst case. -/
theorem sorting_lb_4 (t : CompTree 4) (h : t.Sorts) :
    Nat.clog 2 (Nat.factorial 4) ≤ t.depth :=
  sorting_lb 4 t h

/-- Explicit form of the bound for `4` elements: at least `5` comparisons are needed. -/
theorem sorting_lb_4' (t : CompTree 4) (h : t.Sorts) : 5 ≤ t.depth := by
  have := sorting_lb_4 t h
  norm_num [Nat.factorial] at this
  simpa using this

end CS

