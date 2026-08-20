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
