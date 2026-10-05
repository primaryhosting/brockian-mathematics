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

lemma ker_proj (A : Finset (Fin n)) :
    LinearMap.ker (proj A : PSpace F n →ₗ[F] PSpace F n) = coordSub Aᶜ := by
  ext v
  simp only [LinearMap.mem_ker, funext_iff, proj_apply, Pi.zero_apply, mem_coordSub,
    Finset.mem_compl, not_not]
  constructor
  · intro h i hi
    simpa [hi] using h i
  · intro h i
    by_cases hi : i ∈ A
    · simp [hi, h i hi]
    · simp [hi]

