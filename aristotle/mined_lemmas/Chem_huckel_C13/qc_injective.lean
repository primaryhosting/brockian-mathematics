import Mathlib

/-!
# Huckel C 13
Category: Chemistry
Target: Chem.huckel_C13
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/
open scoped Real

namespace Chem

/-! ### A primitive 13-th root of unity -/

/-- A primitive 13-th root of unity. -/

lemma qc_injective : Function.Injective qc := fun a b hab =>
  Fin.ext (zeta13_primitive.pow_inj a.isLt b.isLt hab)

