/-!
# Chinese Remainder
Category: Pure Mathematics
Target: Math.chinese_remainder
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

open scoped Function -- for the scoped `on` notation

namespace Math

/-- Each modulus of a finite family divides the product of the family. -/

theorem ringHom_to_zmod_eq_castHom {N m : ℕ} (h : m ∣ N) (f : ZMod N →+* ZMod m) :
    f = ZMod.castHom h (ZMod m) :=
  RingHom.ext_zmod f (ZMod.castHom h (ZMod m))

/-- **Chinese Remainder Theorem.**  For a finite family `n : ι → ℕ` of pairwise coprime moduli,
the ring `ZMod (∏ i, n i)` is isomorphic to the product ring `Π i, ZMod (n i)`; moreover the
isomorphism is the canonical one, given componentwise by reduction mod `n i`. -/
