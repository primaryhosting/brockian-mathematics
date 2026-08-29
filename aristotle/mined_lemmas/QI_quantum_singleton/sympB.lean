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

def sympB : PSpace F n →ₗ[F] PSpace F n →ₗ[F] F :=
  LinearMap.mk₂ F (fun u v => ∑ i, ((u i).1 * (v i).2 - (u i).2 * (v i).1))
    (by
      intro u u' v
      rw [← Finset.sum_add_distrib]
      exact Finset.sum_congr rfl (by intro i _; simp; ring))
    (by
      intro c u v
      simp only [smul_eq_mul, Finset.mul_sum]
      exact Finset.sum_congr rfl (by intro i _; simp; ring))
    (by
      intro u v v'
      rw [← Finset.sum_add_distrib]
      exact Finset.sum_congr rfl (by intro i _; simp; ring))
    (by
      intro c u v
      simp only [smul_eq_mul, Finset.mul_sum]
      exact Finset.sum_congr rfl (by intro i _; simp; ring))

/-- The symplectic form. -/
