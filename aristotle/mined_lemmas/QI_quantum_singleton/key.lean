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

lemma key {S : Submodule F (PSpace F n)} {d : ℕ} (A : Finset (Fin n))
    (hd : ∀ v ∈ orth S, v ∉ S → d ≤ wt v) (hA : A.card < d) :
    finrank F ((S ⊓ coordSub Aᶜ : Submodule F (PSpace F n))) + 2 * A.card ≤
      finrank F ((S ⊓ coordSub A : Submodule F (PSpace F n))) + finrank F S := by
  have h1 := finrank_map_proj_add S A
  have h2 := duality S A
  have h3 : finrank F ((orth S ⊓ coordSub A : Submodule F (PSpace F n))) ≤
      finrank F ((S ⊓ coordSub A : Submodule F (PSpace F n))) :=
    Submodule.finrank_mono (correctable A hd hA)
  omega

/-- The core estimate: for any two disjoint correctable sets `A`, `B`, the number of qudits
they occupy is at most the number of stabilizer generators. -/
