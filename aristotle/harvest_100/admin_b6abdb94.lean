import Mathlib

/-!
# Mobius Root Sum 12
Category: Pure Mathematics
Target: Math.mobius_root_sum_12
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
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

set_option grind.warning false

namespace Math

/-- The Möbius function vanishes at `12`, since `12 = 2 ^ 2 * 3` is not squarefree. -/
lemma moebius_twelve : ArithmeticFunction.moebius 12 = 0 := by
  apply ArithmeticFunction.moebius_eq_zero_of_not_squarefree
  decide

/-- If `z` is a primitive `12`-th root of unity in `ℂ`, then `z ^ 6 = -1`. -/
lemma pow_six_eq_neg_one {z : ℂ} (hz : IsPrimitiveRoot z 12) : z ^ 6 = -1 := by
  have h1 : z ^ 12 = 1 := hz.pow_eq_one
  have h2 : z ^ 6 ≠ 1 := hz.pow_ne_one_of_pos_of_lt (by norm_num) (by norm_num)
  have h3 : (z ^ 6 - 1) * (z ^ 6 + 1) = 0 := by linear_combination h1
  rcases mul_eq_zero.1 h3 with h | h
  · exact absurd (sub_eq_zero.1 h) h2
  · linear_combination h

/-- The negative of a primitive `12`-th root of unity is again a primitive `12`-th root of
unity (it is the `7`-th power of the original root). -/
lemma neg_mem_primitiveRoots_twelve {z : ℂ} (hz : z ∈ primitiveRoots 12 ℂ) :
    -z ∈ primitiveRoots 12 ℂ := by
  rw [mem_primitiveRoots (by norm_num)] at hz ⊢
  have h7 : IsPrimitiveRoot (z ^ 7) 12 := hz.pow_of_coprime 7 (by decide)
  have : z ^ 7 = -z := by
    have h6 : z ^ 6 = -1 := pow_six_eq_neg_one hz
    calc z ^ 7 = z ^ 6 * z := by ring
    _ = -z := by rw [h6]; ring
  rwa [this] at h7

/-- **The sum of the primitive 12-th roots of unity equals `μ(12)`.**

Both sides are `0`: the Möbius function vanishes at `12` because `12` is not squarefree, and the
primitive 12-th roots of unity come in pairs `{z, -z}` (as `-z = z ^ 7` and `gcd(7, 12) = 1`),
so they cancel in the sum. -/
theorem mobius_root_sum_12 :
    ∑ z ∈ primitiveRoots 12 ℂ, z = (ArithmeticFunction.moebius 12 : ℂ) := by
  rw [moebius_twelve]
  push_cast
  refine Finset.sum_involution (fun z _ => -z) (fun a _ => by ring) ?_
    (fun a ha => neg_mem_primitiveRoots_twelve ha) (fun a _ => neg_neg a)
  intro a _ ha0 h
  exact ha0 (by linear_combination (-1 / 2 : ℂ) * h)

end Math

