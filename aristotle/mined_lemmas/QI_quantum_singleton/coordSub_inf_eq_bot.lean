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

lemma coordSub_inf_eq_bot {B C : Finset (Fin n)} (h : Disjoint B C) :
    (coordSub B ⊓ coordSub C : Submodule F (PSpace F n)) = ⊥ := by
  rw [eq_bot_iff]
  rintro v ⟨h1, h2⟩
  have : v = 0 := by
    funext i
    by_cases hi : i ∈ B
    · exact h2 i (Finset.disjoint_left.mp h hi)
    · exact h1 i hi
  simpa using this

