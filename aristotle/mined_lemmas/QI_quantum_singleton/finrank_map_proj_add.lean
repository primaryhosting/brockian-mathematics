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

lemma finrank_map_proj_add (S : Submodule F (PSpace F n)) (A : Finset (Fin n)) :
    finrank F (S.map (proj A)) + finrank F ((S ⊓ coordSub Aᶜ : Submodule F (PSpace F n))) =
      finrank F S := by
  have h := LinearMap.finrank_range_add_finrank_ker ((proj A).domRestrict S)
  rwa [LinearMap.range_domRestrict, LinearMap.ker_domRestrict, ker_proj,
    finrank_comap_subtype] at h

/-- Local duality: on the qudits of `A`, the centralizer of the code is at least as large as
the codimension of the truncated code. -/
