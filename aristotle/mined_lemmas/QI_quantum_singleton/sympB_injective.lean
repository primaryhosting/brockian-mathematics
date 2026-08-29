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

lemma sympB_injective :
    Function.Injective (sympB : PSpace F n →ₗ[F] Module.Dual F (PSpace F n)) := by
  refine (injective_iff_map_eq_zero _).mpr ?_
  intro v hv
  funext i
  have h1 : sympB v (Pi.single i (0, 1)) = 0 := by rw [hv]; simp
  have h2 : sympB v (Pi.single i (1, 0)) = 0 := by rw [hv]; simp
  have e1 : sympB v (Pi.single i ((0 : F), (1 : F))) = (v i).1 := by
    rw [show (sympB v (Pi.single i ((0 : F), (1 : F)))) =
      ∑ j, ((v j).1 * ((Pi.single i ((0 : F), (1 : F))) j).2 -
        (v j).2 * ((Pi.single i ((0 : F), (1 : F))) j).1) from rfl]
    rw [Finset.sum_eq_single i]
    · simp
    · intro j _ hj
      simp [Pi.single_eq_of_ne hj]
    · simp
  have e2 : sympB v (Pi.single i ((1 : F), (0 : F))) = -(v i).2 := by
    rw [show (sympB v (Pi.single i ((1 : F), (0 : F)))) =
      ∑ j, ((v j).1 * ((Pi.single i ((1 : F), (0 : F))) j).2 -
        (v j).2 * ((Pi.single i ((1 : F), (0 : F))) j).1) from rfl]
    rw [Finset.sum_eq_single i]
    · simp
    · intro j _ hj
      simp [Pi.single_eq_of_ne hj]
    · simp
  rw [e1] at h1
  rw [e2, neg_eq_zero] at h2
  exact Prod.ext h1 h2

