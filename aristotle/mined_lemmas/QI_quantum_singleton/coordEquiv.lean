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

noncomputable def coordEquiv (A : Finset (Fin n)) :
    (coordSub A : Submodule F (PSpace F n)) ≃ₗ[F] ({x // x ∈ A} → F × F) where
  toFun v := fun i => (v : PSpace F n) i
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  invFun g := ⟨fun i => if h : i ∈ A then g ⟨i, h⟩ else 0, by intro i hi; simp [hi]⟩
  left_inv v := by
    apply Subtype.ext
    funext i
    by_cases h : i ∈ A
    · simp [h]
    · simp [h, v.2 i h]
  right_inv g := by funext i; simp

