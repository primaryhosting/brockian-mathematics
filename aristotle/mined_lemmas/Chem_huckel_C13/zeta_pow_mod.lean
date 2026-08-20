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

lemma zeta_pow_mod (n : ℕ) : zeta ^ (n % 13) = zeta ^ n := by
  conv_rhs => rw [← Nat.div_add_mod n 13]
  rw [pow_add, pow_mul, zeta_pow_13, one_pow, one_mul]

