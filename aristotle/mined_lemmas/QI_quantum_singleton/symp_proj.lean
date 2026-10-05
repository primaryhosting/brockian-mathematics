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

lemma symp_proj {A : Finset (Fin n)} {w : PSpace F n}
    (hw : w ∈ (coordSub A : Submodule F (PSpace F n))) (s : PSpace F n) :
    symp w (proj A s) = symp w s := by
  rw [symp_apply, symp_apply]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  by_cases h : i ∈ A
  · simp [proj_apply, h]
  · simp [proj_apply, h, hw i h]

