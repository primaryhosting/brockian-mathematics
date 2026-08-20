/-
# Euler Pentagonal
Category: Pure Mathematics
Target: Math.euler_pentagonal
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Euler Pentagonal
Category: Pure Mathematics
Target: Math.euler_pentagonal
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

/-!
Euler's pentagonal number theorem.

We prove that the coefficient of `q^n` in the (truncated) product `∏_{i=1}^{N} (1 - q^i)`
(for any `N ≥ n`, so that the coefficient has already stabilised) equals
`∑_{k ∈ ℤ} (-1)^k [n = k(3k-1)/2]`.

The proof is Franklin's involution on partitions into distinct parts.
-/

namespace Math

open Finset

/-! ### Basic combinatorial gadgets -/

/-- `runLen s t` is the length of the maximal run `t, t-1, t-2, …` of consecutive
elements of `s` ending at `t`. -/

lemma b2_mxf (h0 : 0 ∉ s) (hne : s.Nonempty) (hb : df s < mnf s) (hexc : ¬ IsExc s) :
    mxf (b2img s) = mxf s - 1 := by
  have hd1 : 1 ≤ df s := one_le_df h0 hne
  have h2 := b2_two_mul_df_lt h0 hne hb hexc
  have hmM : mnf s ≤ mxf s := mnf_le (mxf_mem hne)
  refine mxf_eq_of ?_ ?_
  · rcases Nat.lt_or_ge 1 (df s) with hd | hd
    · exact mem_b2img.2 (Or.inr (Or.inr ⟨df_run s 1 hd, by omega⟩))
    · exact mem_b2img.2 (Or.inr (Or.inl (by omega)))
  · intro b hbm
    rcases mem_b2img.1 hbm with h | h | ⟨h, hne'⟩
    · omega
    · omega
    · have := le_mxf h; omega

