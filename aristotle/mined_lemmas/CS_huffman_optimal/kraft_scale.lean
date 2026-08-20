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

lemma kraft_scale (t : Multiset ℕ) (D D' : ℕ) (hD : ∀ e ∈ t, e ≤ D) (hDD' : D ≤ D') :
    (t.map (fun e => 2 ^ (D' - e))).sum = 2 ^ (D' - D) * (t.map (fun e => 2 ^ (D - e))).sum := by
  rw [← Multiset.sum_map_mul_left]
  congr 1
  apply Multiset.map_congr rfl
  intro e he
  have hsplit : D' - e = (D' - D) + (D - e) := by have := hD e he; omega
  rw [hsplit, pow_add]

/-- To check Kraft's inequality it suffices to check it for one bound `D₀`. -/
