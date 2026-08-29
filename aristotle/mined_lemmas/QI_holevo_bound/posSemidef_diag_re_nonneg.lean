/-
# Holevo Bound
Category: Frontier Qi
Target: QI.holevo_bound
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/
-- (Lean 4 requires `import` to precede any module docstring, so the header above is repeated
-- verbatim as the module docstring below.)
import Mathlib

/-!
# Holevo Bound
Category: Frontier Qi
Target: QI.holevo_bound
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open scoped BigOperators
open scoped Real
open scoped Nat
open scoped Classical
open scoped Pointwise
open scoped ComplexOrder

set_option maxHeartbeats 8000000
set_option maxRecDepth 4000
set_option synthInstance.maxHeartbeats 20000
set_option synthInstance.maxSize 128

set_option relaxedAutoImplicit false
set_option autoImplicit false

set_option grind.warning false

namespace QI

/-! ## Classical information quantities -/

section ClassicalDefs

variable {X I Y : Type*}

/-- Shannon entropy `H(P) = -∑ P x * log (P x)` of a finite probability vector. -/

theorem posSemidef_diag_re_nonneg {A : Matrix X X ℂ} (hA : A.PosSemidef) (x : X) :
    0 ≤ (A x x).re := by
  simpa using hA.re_dotProduct_nonneg (Pi.single x 1)

end Bridge

/-! ## The Holevo bound -/

section Main

variable {X I Y : Type*} [Fintype X] [DecidableEq X] [Fintype I] [Fintype Y]

/-- **Holevo bound**, fixed POVM version, for an ensemble of commuting (simultaneously
diagonal) states: the mutual information between the ensemble label and the outcome of any
POVM measurement is at most the Holevo χ quantity of the ensemble. -/
