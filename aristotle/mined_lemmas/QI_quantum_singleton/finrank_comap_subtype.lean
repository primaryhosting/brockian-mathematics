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

lemma finrank_comap_subtype (p q : Submodule F (PSpace F n)) :
    finrank F (Submodule.comap p.subtype q) = finrank F (p ⊓ q : Submodule F (PSpace F n)) := by
  have h := (Submodule.equivMapOfInjective p.subtype (Submodule.injective_subtype p)
    (Submodule.comap p.subtype q)).finrank_eq
  rwa [Submodule.map_comap_subtype] at h

/-- Rank-nullity for the truncation map restricted to a code. -/
