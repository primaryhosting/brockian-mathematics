/-
# Crooks Theorem
Category: Frontier Phys
Target: Phys.crooks_theorem
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/
import Mathlib

/-!
# Crooks Theorem
Category: Frontier Phys
Target: Phys.crooks_theorem
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open scoped BigOperators
open Finset
open scoped Classical

namespace Phys

variable {X : Type*} [Fintype X]

/-- State visited by a path at (natural-number) time `n`, clamped to the horizon `N`. -/

theorem crooks_path [Nonempty X] (hβ : β ≠ 0) (hDB : DetailedBalance β E p N)
    (γ : Fin (N + 1) → X) :
    Pfwd β E p N γ = Real.exp (β * (Wfwd E N γ - deltaF β E N)) * Prev β E p N (revPath γ) := by
  have hZ0 : (0 : ℝ) < Zpf β E 0 := Zpf_pos 0
  have hZN : (0 : ℝ) < Zpf β E N := Zpf_pos N
  have hexp : Real.exp (β * (Wfwd E N γ - deltaF β E N)) =
      Real.exp (β * Wfwd E N γ) * (Zpf β E N / Zpf β E 0) := by
    have hpos : (0 : ℝ) < Zpf β E N / Zpf β E 0 := div_pos hZN hZ0
    have hdF : β * deltaF β E N = -Real.log (Zpf β E N / Zpf β E 0) := by
      rw [deltaF]; field_simp
    rw [show β * (Wfwd E N γ - deltaF β E N) =
        β * Wfwd E N γ + Real.log (Zpf β E N / Zpf β E 0) by
      rw [mul_sub, hdF]; ring]
    rw [Real.exp_add, Real.exp_log hpos]
  rw [hexp, Prev_revPath, Pfwd]
  have hcore := crooks_core hDB γ
  simp only [neg_mul] at hcore ⊢
  field_simp
  linear_combination hcore

/-- **Crooks fluctuation theorem** (coarse-grained form): the probability that the forward
process performs work `w` equals `exp (β (w - ΔF))` times the probability that the reverse
process performs work `-w`. -/
