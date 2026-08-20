/-
# Adiabatic Theorem
Category: Frontier Phys
Target: Phys.adiabatic_theorem
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/
import Mathlib

/-!
# Adiabatic Theorem
Category: Frontier Phys
Target: Phys.adiabatic_theorem
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

set_option autoImplicit false
set_option maxHeartbeats 1000000

open Set

namespace Phys

section Kato

variable {A : Type*} [NormedRing A] [NormedAlgebra ℝ A]

/-- Differentiating the idempotency relation `P s * P s = P s`. -/

lemma kato_generator_identity {P dP C : ℝ → A} (hP : ∀ s, HasDerivAt P (dP s) s)
    (hidem : ∀ s, P s * P s = P s) (hcomm : ∀ s, C s * P s = P s * C s) (s : ℝ) :
    dP s + (P s * (C s + (dP s * P s - P s * dP s))
      - (C s + (dP s * P s - P s * dP s)) * P s) = 0 := by
  have h1 := sandwich_eq_zero hP hidem s
  have h2 := hidem s
  have h3 := leibniz_of_idempotent hP hidem s
  have hPG : P s * (C s + (dP s * P s - P s * dP s)) = P s * C s - P s * dP s := by
    calc P s * (C s + (dP s * P s - P s * dP s))
        = P s * C s + (P s * dP s * P s - (P s * P s) * dP s) := by noncomm_ring
      _ = P s * C s + (0 - P s * dP s) := by rw [h1, h2]
      _ = P s * C s - P s * dP s := by abel
  have hGP : (C s + (dP s * P s - P s * dP s)) * P s = P s * C s + dP s * P s := by
    calc (C s + (dP s * P s - P s * dP s)) * P s
        = C s * P s + (dP s * (P s * P s) - P s * dP s * P s) := by noncomm_ring
      _ = P s * C s + (dP s * P s - 0) := by rw [h1, h2, hcomm s]
      _ = P s * C s + dP s * P s := by abel
  rw [hPG, hGP]
  calc dP s + (P s * C s - P s * dP s - (P s * C s + dP s * P s))
      = dP s - (dP s * P s + P s * dP s) := by abel
    _ = 0 := by rw [h3, sub_self]

/-- **Kato's intertwining theorem.**  Let `P s` be a differentiable family of idempotents
(spectral projections) and let `C s` be a family of operators commuting with `P s` (e.g.
`-i/ε` times a Hamiltonian having `P s` as a spectral projection).  Let `U` solve the
*adiabatic* evolution equation `U' = (C + [P', P]) U` with `U 0 = 1`.  Then `U`
intertwines the initial projection with the instantaneous one: `P s * U s = U s * P 0`. -/
