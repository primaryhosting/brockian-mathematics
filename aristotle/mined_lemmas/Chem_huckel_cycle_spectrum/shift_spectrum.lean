/-
# Huckel Cycle Spectrum
Category: Chemistry
Target: Chem.huckel_cycle_spectrum
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Huckel Cycle Spectrum
Category: Chemistry
Target: Chem.huckel_cycle_spectrum
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace Chem

open Complex Polynomial

/-- The cyclic shift matrix on `ZMod n`: it sends the standard basis vector `e i` to
`e (i - 1)`, equivalently `(shift n).mulVec v i = v (i + 1)`. -/

lemma shift_spectrum (n : ℕ) [NeZero n] :
    spectrum ℂ (shift n) = {μ : ℂ | μ ^ n = 1} := by
  refine Set.Subset.antisymm (fun μ hμ => ?_) (fun μ hμ => mem_shift_spectrum n μ hμ)
  have hne : (spectrum ℂ (shift n)).Nonempty := ⟨1, mem_shift_spectrum n 1 (one_pow n)⟩
  have hmap := spectrum.map_polynomial_aeval_of_nonempty (shift n) (X ^ n : ℂ[X]) hne
  have h1 : (aeval (shift n)) (X ^ n : ℂ[X]) = 1 := by
    simp [map_pow, shift_pow_card]
  rw [h1, spectrum.one_eq] at hmap
  have hmem : μ ^ n ∈ ({1} : Set ℂ) := by
    rw [hmap]; exact ⟨μ, hμ, by simp⟩
  simpa using hmem

