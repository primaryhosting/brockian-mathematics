import Mathlib

/-!
# Chinese Remainder
Category: Pure Mathematics
Target: Math.chinese_remainder
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open scoped BigOperators
open scoped Function

namespace Math

variable {ι : Type*} [Fintype ι]

/-- The natural reduction ring homomorphism `ℤ/(∏ i, n i) → ∏ i, ℤ/(n i)`. -/

lemma crtHom_intCast (n : ι → ℕ) (a : ℤ) (i : ι) :
    crtHom n (a : ZMod (∏ i, n i)) i = (a : ZMod (n i)) := by
  have : crtHom n (a : ZMod (∏ i, n i)) = ((a : ℤ) : ∀ i, ZMod (n i)) := by
    simp [map_intCast]
  rw [this]
  simp

/-- The natural reduction map is injective when the moduli are pairwise coprime. -/
