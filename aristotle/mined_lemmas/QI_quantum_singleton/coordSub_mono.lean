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

lemma coordSub_mono {A B : Finset (Fin n)} (h : A ⊆ B) :
    (coordSub A : Submodule F (PSpace F n)) ≤ coordSub B := by
  intro v hv i hi
  exact hv i (fun hA => hi (h hA))

/-- Pauli operators supported in `A` are determined by their restriction to `A`. -/
