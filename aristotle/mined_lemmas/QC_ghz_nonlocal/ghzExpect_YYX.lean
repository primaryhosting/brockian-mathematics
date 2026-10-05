import Mathlib

/-!
# Ghz Nonlocal
Category: Quantum Computing
Target: QC.ghz_nonlocal
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

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

namespace QC

/-- Index type for the computational basis of three qubits;
`false` stands for `|0⟩` and `true` for `|1⟩`. -/
abbrev Idx : Type := Bool × Bool × Bool

/-- The Pauli `X` matrix in the computational basis. -/

lemma ghzExpect_YYX : ghzExpect true true false = -1 := by
  simp only [ghzExpect, ghz, tensor3, pauli, pauliX, pauliY, Fintype.sum_prod_type,
    Fintype.sum_bool]
  norm_num [sqrt2_inv_sq, Complex.ext_iff]

/--
**Mermin's GHZ paradox: the three-qubit GHZ state admits no local hidden-variable model.**

Suppose each of the three parties deterministically assigns an outcome `±1` to each of its two
measurement settings (`false = X`, `true = Y`), the assignment of one party being independent of
the settings chosen by the others (this is the locality assumption, encoded by the outcome
functions `a`, `b`, `c` depending only on that party's own setting).  Then the products of the
outcomes cannot reproduce the four quantum expectation values of the GHZ state,
`⟨XXX⟩ = 1` and `⟨XYY⟩ = ⟨YXY⟩ = ⟨YYX⟩ = -1`, which are computed above from the state vector
itself.  The contradiction is deterministic: no inequality or statistics are involved.
-/
