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

lemma b1_df (h0 : 0 ∉ s) (hne : s.Nonempty) (hb : mnf s ≤ df s) (hexc : ¬ IsExc s) :
    df (b1img s) = mnf s := by
  have h2 := b1_two_mul_mnf_le h0 hne hb hexc
  have hm1 : 1 ≤ mnf s := one_le_mnf h0 hne
  have hmx : mnf s ≤ mxf s := mnf_le (mxf_mem hne)
  refine df_eq_of (b1_zero_not_mem h0) ?_ ?_
  · intro i hi
    rw [b1_mxf]
    rcases Nat.eq_zero_or_pos i with rfl | hpos
    · exact mem_b1img.2 (Or.inl (by omega))
    · refine mem_b1img.2 (Or.inr ⟨?_, by omega, by omega⟩)
      have hmem := df_run s (i - 1) (by omega)
      have heq : mxf s - (i - 1) = mxf s + 1 - i := by omega
      rwa [heq] at hmem
  · rw [b1_mxf]
    intro hmem
    rcases mem_b1img.1 hmem with h | ⟨_, _, h⟩
    · omega
    · omega

