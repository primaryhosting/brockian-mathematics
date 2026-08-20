/-
# Chinese Remainder
Category: Pure Mathematics
Target: Math.chinese_remainder
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Chinese Remainder
Category: Pure Mathematics
Target: Math.chinese_remainder
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open scoped Function -- for the `on` notation

namespace Math

/-- **Chinese Remainder Theorem.**  For a finite family of pairwise coprime moduli `a i`,
the ring `ZMod (∏ i, a i)` is isomorphic to the product ring `Π i, ZMod (a i)`.

This is `ZMod.prodEquivPi` from Mathlib (`Mathlib/Data/ZMod/QuotientRing.lean`). -/

theorem chinese_remainder_apply {ι : Type*} [Fintype ι] (a : ι → ℕ)
    (coprime : Pairwise (Nat.Coprime on a)) (x : ZMod (∏ i, a i)) (i : ι) :
    chinese_remainder a coprime x i = ZMod.castHom (dvd_prod a i) (ZMod (a i)) x := by
  have h : ((Pi.evalRingHom (fun i ↦ ZMod (a i)) i).comp
      (chinese_remainder a coprime : ZMod (∏ i, a i) →+* Π i, ZMod (a i)))
      = ZMod.castHom (dvd_prod a i) (ZMod (a i)) := Subsingleton.elim _ _
  exact congrArg (fun f : ZMod (∏ i, a i) →+* ZMod (a i) => f x) h

/-- Cardinality form: the two rings have the same (finite) size when all moduli are positive. -/
