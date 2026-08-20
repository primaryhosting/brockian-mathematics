import RequestProject.Forest

open scoped BigOperators
open scoped Classical

set_option maxHeartbeats 1000000
set_option relaxedAutoImplicit false
set_option autoImplicit false

namespace CS

/-- The value computed by Huffman's algorithm on a multiset of weights. -/

theorem huffman_optimal (w : ι → ℝ) (hw : ∀ i, 0 ≤ w i) :
    IsPrefixCode (huffmanCode w) ∧
      ∀ c : ι → List Bool, IsPrefixCode c →
        expLength w (huffmanCode w) ≤ expLength w c := by
  refine ⟨huffmanCode_isPrefixCode w, ?_⟩
  intro c hc
  rw [huffmanCode_expLength w]
  exact huffman_le_expLength w hw c hc

end CS

import Mathlib
import RequestProject.Huffman
import RequestProject.Examples

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

#print axioms CS.huffman_optimal

