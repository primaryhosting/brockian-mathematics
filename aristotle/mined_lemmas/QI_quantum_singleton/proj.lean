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

def proj (A : Finset (Fin n)) : PSpace F n →ₗ[F] PSpace F n where
  toFun v := fun i => if i ∈ A then v i else 0
  map_add' := by intro u v; funext i; by_cases h : i ∈ A <;> simp [h]
  map_smul' := by intro c v; funext i; by_cases h : i ∈ A <;> simp [h]

/-! ### Basic lemmas -/

