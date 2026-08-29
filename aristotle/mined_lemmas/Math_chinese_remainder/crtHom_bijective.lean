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

theorem crtHom_bijective (h : Pairwise (Nat.Coprime on n)) : Function.Bijective (crtHom n) :=
  ⟨crtHom_injective n h, crtHom_surjective n h⟩

/-- **Chinese Remainder Theorem.** For a finite family of pairwise coprime natural numbers `n i`,
the canonical reduction map gives a ring isomorphism `ZMod (∏ i, n i) ≃+* Π i, ZMod (n i)`. -/
