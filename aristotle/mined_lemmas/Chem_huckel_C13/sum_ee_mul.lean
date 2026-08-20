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

lemma sum_ee_mul (c : ZMod 13) :
    ∑ k : ZMod 13, ee (k * c) = if c = 0 then 13 else 0 := by
  by_cases hc : c = 0
  · simp [hc, ee_zero]
  · rw [if_neg hc, ← sum_ee]
    exact Fintype.sum_equiv (Equiv.mulRight₀ c hc) _ _ (fun k => rfl)

