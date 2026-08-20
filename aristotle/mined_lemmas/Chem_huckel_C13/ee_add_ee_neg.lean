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

lemma ee_add_ee_neg (x : ZMod 13) :
    ee x + ee (-x) = ((2 * Real.cos (2 * Real.pi * (x.val : ℝ) / 13) : ℝ) : ℂ) := by
  have key : ∀ t : ℂ, Complex.exp (t * Complex.I) + (Complex.exp (t * Complex.I))⁻¹
      = 2 * Complex.cos t := by
    intro t
    rw [← Complex.exp_neg, show -(t * Complex.I) = (-t) * Complex.I by ring,
      Complex.exp_mul_I, Complex.exp_mul_I, Complex.cos_neg, Complex.sin_neg]
    ring
  rw [ee_neg, ee_eq_exp, key]
  push_cast [Complex.ofReal_cos]
  ring

