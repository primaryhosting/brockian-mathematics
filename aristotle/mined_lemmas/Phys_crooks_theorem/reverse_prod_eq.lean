import Mathlib

/-!
# Crooks Theorem
Category: Frontier Phys
Target: Phys.crooks_theorem
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace Phys

open Finset

section Setup

variable {X : Type*} [Fintype X] [Nonempty X]

/-- Partition function of the energy landscape `E k` at inverse temperature `beta`. -/

lemma reverse_prod_eq :
    ∏ j ∈ Finset.range N, T (N - 1 - j) (reversePath N x j) (reversePath N x (j + 1))
      = ∏ k ∈ Finset.range N, T k (x (k + 1)) (x k) := by
  have h : ∀ j ∈ Finset.range N,
      T (N - 1 - j) (reversePath N x j) (reversePath N x (j + 1))
        = (fun k => T k (x (k + 1)) (x k)) (N - 1 - j) := by
    intro j hj
    simp only [Finset.mem_range] at hj
    have h1 : N - 1 - j + 1 = N - j := by omega
    have h2 : N - (j + 1) = N - 1 - j := by omega
    simp only [reversePath, h1, h2]
  rw [Finset.prod_congr rfl h]
  exact Finset.prod_range_reflect (fun k => T k (x (k + 1)) (x k)) N

omit [Fintype X] [Nonempty X] in
/-- Microscopic reversibility for the kernel product. -/
