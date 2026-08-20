import Mathlib

/-!
# Huckel C 10
Category: Chemistry
Target: Chem.huckel_C10
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open scoped BigOperators
open scoped Real

open Matrix Polynomial

namespace Chem

/-! ## A primitive tenth root of unity and the associated additive character -/

/-- A primitive `10`-th root of unity. -/

lemma zeta10_pow_ten : zeta10 ^ (10 : ℕ) = 1 :=
  ((IsPrimitiveRoot.iff_def zeta10 10).mp zeta10_isPrimitiveRoot).left

/-- The additive character `a ↦ ζ ^ a` of `ZMod 10`, where `ζ = exp (2πi/10)`. -/
