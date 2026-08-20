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

