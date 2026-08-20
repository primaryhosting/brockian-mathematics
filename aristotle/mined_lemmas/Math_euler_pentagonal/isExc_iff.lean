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

lemma isExc_iff {s : Finset ℕ} (h0 : 0 ∉ s) (hne : s.Nonempty) :
    IsExc s ↔ ∃ k, 1 ≤ k ∧ (s = Finset.Ico k (2 * k) ∨ s = Finset.Ico (k + 1) (2 * k + 1)) := by
  constructor
  · rintro (⟨hb, hM⟩ | ⟨hb, hM⟩)
    · have hm1 : 1 ≤ mnf s := one_le_mnf h0 hne
      have hsum := mnf_add_df_le h0 hne
      have hdf : df s = mnf s := by omega
      refine ⟨mnf s, hm1, Or.inl ?_⟩
      apply Finset.ext
      intro a
      constructor
      · intro ha
        have h1 := mnf_le ha
        have h2 := le_mxf ha
        exact Finset.mem_Ico.2 ⟨h1, by omega⟩
      · intro ha
        have := Finset.mem_Ico.1 ha
        have hmem := df_run s (mxf s - a) (by omega)
        have heq : mxf s - (mxf s - a) = a := by omega
        rwa [heq] at hmem
    · have hm1 : 1 ≤ mnf s := one_le_mnf h0 hne
      have hd1 : 1 ≤ df s := one_le_df h0 hne
      have hsum := mnf_add_df_le h0 hne
      have hmn : mnf s = df s + 1 := by omega
      refine ⟨df s, hd1, Or.inr ?_⟩
      apply Finset.ext
      intro a
      constructor
      · intro ha
        have h1 := mnf_le ha
        have h2 := le_mxf ha
        exact Finset.mem_Ico.2 ⟨by omega, by omega⟩
      · intro ha
        have := Finset.mem_Ico.1 ha
        have hmem := df_run s (mxf s - a) (by omega)
        have heq : mxf s - (mxf s - a) = a := by omega
        rwa [heq] at hmem
  · rintro ⟨k, hk, rfl | rfl⟩
    · left
      rw [mnf_Ico (by omega : k < 2 * k), mxf_Ico (by omega : k < 2 * k), df_Ico1 hk]
      omega
    · right
      rw [mnf_Ico (by omega : k + 1 < 2 * k + 1), mxf_Ico (by omega : k + 1 < 2 * k + 1),
        df_Ico2 hk]
      omega

/-- The index set of the pentagonal numbers attached to `n`. -/
