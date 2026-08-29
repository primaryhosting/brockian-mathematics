import Mathlib

/-!
# Quantum Singleton
Category: Frontier Qi
Target: QI.quantum_singleton
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/


open scoped BigOperators
open scoped Classical

set_option maxHeartbeats 1000000

namespace QI

open Module

/-- The symplectic (phase-space) representation of the Pauli group on `n` qudits over the
finite field `F`: a Pauli operator is recorded by its `X`-part and `Z`-part on each qudit. -/
abbrev PSpace (F : Type*) (n : ℕ) := Fin n → F × F

variable {F : Type*} [Field F] {n : ℕ}

/-- The symplectic form on the phase space, as a bilinear map.  Two Pauli operators commute
iff their symplectic form vanishes. -/

lemma finrank_coordSub (A : Finset (Fin n)) :
    finrank F (coordSub A : Submodule F (PSpace F n)) = 2 * A.card := by
  rw [(coordEquiv A).finrank_eq, Module.finrank_pi_fintype F]
  simp [Module.finrank_prod, Fintype.card_coe, mul_comm]

