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
