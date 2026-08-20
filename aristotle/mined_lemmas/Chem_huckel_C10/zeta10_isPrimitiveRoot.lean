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

lemma zeta10_isPrimitiveRoot : IsPrimitiveRoot zeta10 10 := by
  have h := Complex.isPrimitiveRoot_exp 10 (by norm_num)
  simpa [zeta10] using h

