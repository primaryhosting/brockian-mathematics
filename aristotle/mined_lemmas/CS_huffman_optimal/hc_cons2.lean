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
