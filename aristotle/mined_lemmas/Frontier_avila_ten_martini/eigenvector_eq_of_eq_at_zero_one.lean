/-
# Avila Ten Martini
Category: Frontier — Fields Medal Work
Target: Frontier.avila_ten_martini
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Avila Ten Martini
Category: Frontier — Fields Medal Work
Target: Frontier.avila_ten_martini
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open scoped BigOperators
open scoped Real
open scoped Nat
open scoped Classical
open scoped Pointwise
open scoped ENNReal

set_option maxHeartbeats 8000000
set_option maxRecDepth 4000
set_option synthInstance.maxHeartbeats 20000
set_option synthInstance.maxSize 128

set_option relaxedAutoImplicit false
set_option autoImplicit false

set_option grind.warning false

namespace Frontier

noncomputable section

/-! ## The Hilbert space `ℓ²(ℤ, ℂ)` -/

/-- The Hilbert space `ℓ²(ℤ, ℂ)` on which the almost Mathieu operator acts. -/
abbrev H2 := ℓ²(ℤ, ℂ)

instance : Nontrivial H2 := by
  refine ⟨lp.single 2 (0 : ℤ) (1 : ℂ), 0, ?_⟩
  intro h
  have : (lp.single 2 (0 : ℤ) (1 : ℂ) : ℤ → ℂ) 0 = (0 : H2) 0 := by rw [h]
  simp [lp.single_apply] at this

/-! ## Shift operators -/


theorem eigenvector_eq_of_eq_at_zero_one {lam alpha theta : ℝ} {E : ℂ} {u w : H2}
    (hu : almostMathieu lam alpha theta u = E • u)
    (hw : almostMathieu lam alpha theta w = E • w)
    (h0 : (u : ℤ → ℂ) 0 = (w : ℤ → ℂ) 0) (h1 : (u : ℤ → ℂ) 1 = (w : ℤ → ℂ) 1) :
    u = w := by
  have key : ∀ n : ℤ, (u : ℤ → ℂ) n = (w : ℤ → ℂ) n ∧
      (u : ℤ → ℂ) (n + 1) = (w : ℤ → ℂ) (n + 1) := by
    intro n
    induction n using Int.induction_on with
    | zero => exact ⟨h0, by simpa using h1⟩
    | succ k ih =>
      refine ⟨ih.2, ?_⟩
      have hu' := eigen_recurrence hu ((k : ℤ) + 1)
      have hw' := eigen_recurrence hw ((k : ℤ) + 1)
      have e1 : ((k : ℤ) + 1 - 1) = (k : ℤ) := by ring
      rw [e1] at hu' hw'
      rw [show ((k : ℤ) + 1 + 1) = (k : ℤ) + 1 + 1 from rfl] at hu' hw'
      rw [hu', hw', ih.1, ih.2]
    | pred k ih =>
      have e2 : (-(k : ℤ) - 1 + 1) = -(k : ℤ) := by ring
      refine ⟨?_, by rw [e2]; exact ih.1⟩
      have hu' := eigen_recurrence hu (-(k : ℤ))
      have hw' := eigen_recurrence hw (-(k : ℤ))
      have hu'' : (u : ℤ → ℂ) (-(k : ℤ) - 1)
          = (E - (amPotential lam alpha theta (-(k : ℤ)) : ℂ)) * (u : ℤ → ℂ) (-(k : ℤ))
            - (u : ℤ → ℂ) (-(k : ℤ) + 1) := by linear_combination hu'
      have hw'' : (w : ℤ → ℂ) (-(k : ℤ) - 1)
          = (E - (amPotential lam alpha theta (-(k : ℤ)) : ℂ)) * (w : ℤ → ℂ) (-(k : ℤ))
            - (w : ℤ → ℂ) (-(k : ℤ) + 1) := by linear_combination hw'
      rw [hu'', hw'', ih.1, ih.2]
  ext n
  exact (key n).1

/-- Every eigenvalue of the almost Mathieu operator has multiplicity at most `2`: the
eigenspace for `E` has rank at most `2`, since an eigenvector is determined by its values
at `0` and `1`. -/
