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

lemma mulVec_evec (k : ZMod 13) :
    adjC13.mulVec (evec k) = eval13 k • evec k := by
  funext i
  rw [mulVec_apply]
  have h1 : (i + 1) * k = i * k + k := by ring
  have h2 : (i - 1) * k = i * k + (-k) := by ring
  simp only [evec, h1, h2, ee_add, Pi.smul_apply, smul_eq_mul, eval13]
  rw [← ee_add_ee_neg k]
  ring

/-- The (unnormalized) discrete Fourier matrix. -/
