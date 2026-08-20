import Mathlib

/-!
# Qft Unitary 7
Category: Quantum Computing
Target: QC.qft_unitary_7
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace QC

open Complex ZMod AddChar Matrix Finset

/-- The `N`-dimensional quantum Fourier transform matrix: the entry in row `j`, column `k` is
`exp (2 π i · j · k / N) / √N`, with rows and columns indexed by `ZMod N`. -/

theorem qft_unitary_7' :
    star (qftMatrix (2 ^ 7)) * qftMatrix (2 ^ 7) = 1 ∧
      qftMatrix (2 ^ 7) * star (qftMatrix (2 ^ 7)) = 1 :=
  ⟨qft_unitary_7.1, qft_unitary_7.2⟩

end QC

import Mathlib

open scoped BigOperators
open scoped Real
open scoped Nat
open scoped Classical
open scoped Pointwise

set_option maxHeartbeats 8000000
set_option maxRecDepth 4000
set_option synthInstance.maxHeartbeats 20000
set_option synthInstance.maxSize 128

set_option relaxedAutoImplicit false
set_option autoImplicit false

set_option pp.fullNames true
set_option pp.structureInstances true
set_option pp.coercions.types true
set_option pp.funBinderTypes true
set_option pp.letVarTypes true
set_option pp.piBinderTypes true

set_option grind.warning false

