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

theorem dvd_prod {ι : Type*} [Fintype ι] (a : ι → ℕ) (i : ι) : a i ∣ ∏ j, a j :=
  Finset.dvd_prod_of_mem a (Finset.mem_univ i)

/-- The isomorphism of the Chinese Remainder Theorem is the natural one: its `i`-th component
is reduction modulo `a i`. -/
