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

lemma sum_ee : ∑ x : ZMod 13, ee x = 0 := by
  have h : (∑ x : ZMod 13, ee x) = ∑ m ∈ Finset.range 13, zeta ^ m :=
    Fin.sum_univ_eq_sum_range (fun m => zeta ^ m) 13
  rw [h, zeta_primitive.geom_sum_eq_zero (by norm_num)]

