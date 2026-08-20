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

lemma b2_card (h0 : 0 ∉ s) (hne : s.Nonempty) (hb : df s < mnf s) (hexc : ¬ IsExc s) :
    (b2img s).card = s.card + 1 := by
  classical
  have hd1 : 1 ≤ df s := one_le_df h0 hne
  have h2 := b2_two_mul_df_lt h0 hne hb hexc
  have hMmem : mxf s ∈ s := mxf_mem hne
  have hdn : df s ∉ s := b2_df_not_mem hb
  have hMdn : mxf s - df s ∉ s := df_not_mem h0
  have hn1 : mxf s - df s ∉ s.erase (mxf s) := fun h => hMdn (Finset.mem_of_mem_erase h)
  have hn2 : df s ∉ insert (mxf s - df s) (s.erase (mxf s)) := by
    simp only [Finset.mem_insert, Finset.mem_erase, not_or]
    exact ⟨by omega, fun h => hdn h.2⟩
  have e1 : (b2img s).card = (s.erase (mxf s)).card + 2 := by
    rw [b2img, Finset.card_insert_of_notMem hn2, Finset.card_insert_of_notMem hn1]
  have e2 : (s.erase (mxf s)).card + 1 = s.card := Finset.card_erase_add_one hMmem
  omega

