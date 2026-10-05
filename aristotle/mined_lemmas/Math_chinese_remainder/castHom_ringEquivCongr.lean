/-!
# Chinese Remainder
Category: Pure Mathematics
Target: Math.chinese_remainder
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

open scoped Function

namespace Math

variable {ι : Type*} [Fintype ι] (n : ι → ℕ)

/-- The canonical ring homomorphism `ZMod (∏ i, n i) →+* Π i, ZMod (n i)`, given componentwise
by reduction modulo `n i`. -/

private lemma castHom_ringEquivCongr {m N : ℕ} (hmN : m = N) (hdvd : m ∣ N) (x : ZMod m) :
    ZMod.castHom hdvd (ZMod m) (ZMod.ringEquivCongr hmN x) = x := by
  subst hmN
  rw [ZMod.ringEquivCongr_refl_apply]
  have : hdvd = dvd_rfl := rfl
  subst this
  simp [ZMod.castHom_self]

/-- Surjectivity in the degenerate case where one of the moduli is zero (then all the others
are `1`, by coprimality, and the product is `0`). -/
