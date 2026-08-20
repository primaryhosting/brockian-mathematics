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

