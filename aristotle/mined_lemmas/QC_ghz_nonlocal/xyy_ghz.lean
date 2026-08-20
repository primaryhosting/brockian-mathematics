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

/-!
# The GHZ / Mermin paradox

We formalize the deterministic (all-or-nothing) Bell argument of Greenberger–Horne–Zeilinger,
in the form given by Mermin.

* Quantum side: the three–qubit GHZ state
  `|GHZ⟩ = (|000⟩ - |111⟩)/√2`
  is an eigenvector with eigenvalue `+1` of the observables `X⊗Y⊗Y`, `Y⊗X⊗Y`, `Y⊗Y⊗X`,
  and an eigenvector with eigenvalue `-1` of `X⊗X⊗X`.  Hence quantum mechanics predicts with
  certainty that the product of the three `±1` outcomes is `+1` in the first three experiments
  and `-1` in the last one.

* Local hidden variable side: a deterministic local model assigns, for a fixed value of the
  hidden variable, a value `v i s ∈ {+1,-1}` to the measurement of setting `s` (`false` = `X`,
  `true` = `Y`) at site `i`, independently of what is measured at the other two sites, and the
  outcome of a joint measurement is the product of the local values.  No such assignment can
  reproduce the four quantum predictions.

The final statement `QC.ghz_nonlocal` bundles both halves.
-/

namespace QC

open Matrix
open scoped Kronecker

/-- The Pauli `X` matrix. -/

theorem xyy_ghz : (kron3 pauliX pauliY pauliY).mulVec ghz = ghz := by
  funext i
  fin_cases i <;>
    simp [kron3, Matrix.mulVec, dotProduct, Fin.sum_univ_succ, pauliX, pauliY, ghz,
      Fintype.sum_prod_type]

/-- Quantum prediction: `Y⊗X⊗Y` has the GHZ state as a `+1` eigenvector. -/
