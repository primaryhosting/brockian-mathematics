/-
# Gottesman Knill
Category: Frontier Qi
Target: QI.gottesman_knill
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

-- (Lean requires `import` lines to precede any module docstring `/-! ... -/`,
-- so the header above is a plain comment and is repeated as a docstring below.)

import Mathlib

/-!
# Gottesman Knill
Category: Frontier Qi
Target: QI.gottesman_knill
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open scoped BigOperators
open Matrix

namespace QI

/-! ## Phases and signs -/

/-- Computational basis labels for `n` qubits: bit strings of length `n`. -/
abbrev Bits (n : ℕ) : Type := Fin n → ZMod 2

/-- The fourth root of unity `i ^ s` attached to `s : ZMod 4`. -/

noncomputable def gateMatrix {n : ℕ} : Gate n → Matrix (Bits n) (Bits n) ℂ
  | .H q => tp (Function.update (fun _ => 1) q hmat)
  | .S q => tp (Function.update (fun _ => 1) q smat)
  | .CZ c t => Matrix.diagonal (fun a => psign (a c * a t))

/-- The classical (tableau) update rule associated with a Clifford generator.
Only a bounded number of entries of the tableau row are touched. -/
