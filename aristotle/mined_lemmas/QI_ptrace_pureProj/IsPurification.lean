import Mathlib

set_option maxHeartbeats 1000000

/-!
# Purification of mixed states

A mixed state on a finite dimensional system `n` is a positive semidefinite matrix `rho` of
trace one.  A *purification* of `rho` is a unit vector `psi` on the composite system
`n × m` (system ⊗ ancilla) whose reduced density matrix (partial trace over the ancilla `m`)
is `rho`.

The main theorem `QI.purification_exists` states that

* every mixed state admits a purification (with ancilla a copy of the system), and
* any two purifications of the same mixed state are related by an isometry acting on the
  ancilla alone (in particular, for ancillas of the same dimension, by a unitary).
-/

namespace QI

open Matrix
open scoped ComplexOrder MatrixOrder

section Defs

variable {n m : Type*}

/-- The matrix `A` whose `(i,k)` entry is `psi (i,k)`; this is the standard identification of a
vector of the composite system `n × m` with a linear map. -/

def IsPurification [Fintype m] (rho : Matrix n n ℂ) (psi : n × m → ℂ) : Prop :=
  ptraceAncilla (pureProj psi) = rho

/-- The action of an operator `V` on the ancilla factor alone, i.e. `(1 ⊗ V) psi`. -/
