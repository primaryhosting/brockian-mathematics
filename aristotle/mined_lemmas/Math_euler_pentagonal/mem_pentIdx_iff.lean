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

lemma mem_pentIdx_iff (n : ℕ) (hn : 1 ≤ n) (k : ℤ) :
    k ∈ pentIdx n ↔ ∃ j : ℕ, 1 ≤ j ∧ ((k = (j : ℤ) ∧ 2 * n + j = 3 * j * j) ∨
                                        (k = -(j : ℤ) ∧ 2 * n = 3 * j * j + j)) := by
  classical
  simp only [pentIdx, Finset.mem_filter, Finset.mem_Icc]
  constructor
  · rintro ⟨⟨hlo, hhi⟩, heq⟩
    have hk0 : k ≠ 0 := by
      intro h
      rw [h] at heq
      simp at heq
      omega
    rcases lt_or_gt_of_ne hk0 with hneg | hpos
    · refine ⟨k.natAbs, by omega, Or.inr ⟨by omega, ?_⟩⟩
      have hkk : k = -(k.natAbs : ℤ) := by omega
      have : 2 * (n : ℤ) = 3 * (k.natAbs : ℤ) * (k.natAbs : ℤ) + (k.natAbs : ℤ) := by
        rw [hkk] at heq; linarith [heq]
      exact_mod_cast this
    · refine ⟨k.toNat, by omega, Or.inl ⟨by omega, ?_⟩⟩
      have hkk : k = (k.toNat : ℤ) := by omega
      have : 2 * (n : ℤ) + (k.toNat : ℤ) = 3 * (k.toNat : ℤ) * (k.toNat : ℤ) := by
        rw [hkk] at heq; linarith [heq]
      exact_mod_cast this
  · rintro ⟨j, hj, ⟨rfl, harith⟩ | ⟨rfl, harith⟩⟩
    · have harith' : 2 * (n : ℤ) + (j : ℤ) = 3 * (j : ℤ) * (j : ℤ) := by exact_mod_cast harith
      have hjn : (j : ℤ) ≤ (n : ℤ) := by nlinarith [harith', (by exact_mod_cast hj : (1:ℤ) ≤ (j:ℤ))]
      exact ⟨⟨by omega, hjn⟩, by linarith⟩
    · have harith' : 2 * (n : ℤ) = 3 * (j : ℤ) * (j : ℤ) + (j : ℤ) := by exact_mod_cast harith
      have hjn : (j : ℤ) ≤ (n : ℤ) := by nlinarith [harith', (by exact_mod_cast hj : (1:ℤ) ≤ (j:ℤ))]
      exact ⟨⟨by omega, by omega⟩, by linarith⟩



