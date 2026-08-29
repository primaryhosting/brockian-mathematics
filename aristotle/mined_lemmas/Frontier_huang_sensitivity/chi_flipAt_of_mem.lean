/-
# Huang Sensitivity
Category: Frontier — Fields Medal Work
Target: Frontier.huang_sensitivity
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Huang Sensitivity
Category: Frontier — Fields Medal Work
Target: Frontier.huang_sensitivity
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open scoped BigOperators

set_option maxHeartbeats 4000000
set_option maxRecDepth 8000

namespace Frontier

/-! ## Basic definitions for Boolean functions on the hypercube -/

/-- The character `χ_S(x) = ∏_{i ∈ S} (-1)^{x i}`, valued in `ℤ`. -/

lemma chi_flipAt_of_mem {n : ℕ} {S : Finset (Fin n)} {i : Fin n} (hi : i ∈ S)
    (x : Fin n → Bool) : chi S (flipAt x i) = - chi S x := by
  rw [chi, chi, ← Finset.prod_erase_mul _ _ hi, ← Finset.prod_erase_mul _ _ hi]
  have h1 : ∏ j ∈ S.erase i, (if flipAt x i j then (-1 : ℤ) else 1)
      = ∏ j ∈ S.erase i, (if x j then (-1 : ℤ) else 1) :=
    Finset.prod_congr rfl fun j hj => by rw [flipAt_ne x (Finset.ne_of_mem_erase hj)]
  rw [h1, flipAt_self]
  cases x i <;> ring_nf <;> simp

/-- Fourier inversion: `∑_S f̂(S) χ_S(x) = 2^n (-1)^{f x}`. -/
