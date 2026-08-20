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

set_option grind.warning false

namespace Chem

open Polynomial Complex

instance : Fact (Nat.Prime 13) := ⟨by norm_num⟩

/-- The cycle graph `C₁₃`, on the vertex set `ZMod 13`, where `i` and `j` are adjacent
iff they differ by `1`. -/

lemma mulVec_apply (v : ZMod 13 → ℂ) (i : ZMod 13) :
    adjC13.mulVec v i = v (i + 1) + v (i - 1) := by
  have hne : ∀ a : ZMod 13, (a + 1 : ZMod 13) ≠ a - 1 := by decide
  rw [adjC13, SimpleGraph.adjMatrix_mulVec_apply, neighborFinset_eq, Finset.sum_pair (hne i)]

/-- The eigenvector attached to the frequency `k`. -/
