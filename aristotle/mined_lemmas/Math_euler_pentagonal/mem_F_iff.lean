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

lemma mem_F_iff (n : ℕ) (hn : 1 ≤ n) (s : Finset ℕ) :
    s ∈ (distinctParts n).filter (fun s => IsFixed s) ↔
      ∃ k : ℕ, 1 ≤ k ∧ ((s = Finset.Ico k (2 * k) ∧ 2 * n + k = 3 * k * k) ∨
                        (s = Finset.Ico (k + 1) (2 * k + 1) ∧ 2 * n = 3 * k * k + k)) := by
  classical
  simp only [Finset.mem_filter, mem_distinctParts]
  constructor
  · rintro ⟨⟨h0, hsum⟩, hfix⟩
    have hne : s.Nonempty := by
      rcases Finset.eq_empty_or_nonempty s with rfl | h
      · simp at hsum; omega
      · exact h
    have hexc : IsExc s := by
      rcases hfix with rfl | h
      · simp at hsum; omega
      · exact h
    obtain ⟨k, hk, hcase⟩ := (isExc_iff h0 hne).1 hexc
    refine ⟨k, hk, ?_⟩
    rcases hcase with rfl | rfl
    · left
      refine ⟨rfl, ?_⟩
      have := sum_Ico1 k
      omega
    · right
      refine ⟨rfl, ?_⟩
      have := sum_Ico2 k
      omega
  · rintro ⟨k, hk, ⟨rfl, harith⟩ | ⟨rfl, harith⟩⟩
    · have h0 : (0 : ℕ) ∉ Finset.Ico k (2 * k) := zero_not_mem_Ico hk
      have hne : (Finset.Ico k (2 * k)).Nonempty := ⟨k, Finset.mem_Ico.2 ⟨le_refl _, by omega⟩⟩
      refine ⟨⟨h0, ?_⟩, Or.inr ((isExc_iff h0 hne).2 ⟨k, hk, Or.inl rfl⟩)⟩
      have := sum_Ico1 k
      omega
    · have h0 : (0 : ℕ) ∉ Finset.Ico (k + 1) (2 * k + 1) := zero_not_mem_Ico (by omega)
      have hne : (Finset.Ico (k + 1) (2 * k + 1)).Nonempty :=
        ⟨k + 1, Finset.mem_Ico.2 ⟨le_refl _, by omega⟩⟩
      refine ⟨⟨h0, ?_⟩, Or.inr ((isExc_iff h0 hne).2 ⟨k, hk, Or.inr rfl⟩)⟩
      have := sum_Ico2 k
      omega

