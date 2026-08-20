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

lemma ee_eq_exp (x : ZMod 13) :
    ee x = Complex.exp ((2 * Real.pi * (x.val : ℝ) / 13 : ℝ) * Complex.I) := by
  rw [ee, zeta, ← Complex.exp_nat_mul]
  congr 1
  push_cast
  ring

/-- `ee k + ee (-k) = 2 cos (2πk/13)`. -/
