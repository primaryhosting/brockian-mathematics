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

lemma adj_mul_fmat : adjC13 * fmat = fmat * Matrix.diagonal eval13 := by
  ext i k
  have h : (adjC13 * fmat) i k = adjC13.mulVec (evec k) i := rfl
  rw [h, mulVec_evec]
  simp [Matrix.mul_apply, Matrix.diagonal, evec, fmat, mul_comm]

