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
