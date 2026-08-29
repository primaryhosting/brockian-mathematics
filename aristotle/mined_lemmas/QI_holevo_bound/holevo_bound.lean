/-
# Holevo Bound
Category: Frontier Qi
Target: QI.holevo_bound
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/
import Mathlib

/-!
# Holevo Bound
Category: Frontier Qi
Target: QI.holevo_bound
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace QI

open Matrix Finset ComplexOrder

/-! ## Classical information quantities -/

variable {ι X I Y : Type*}

/-- Shannon entropy of a finite (sub)probability vector, `H(p) = -∑ p i log (p i)`. -/

theorem holevo_bound {X : Type*} [Fintype X] (Y : Type) [Fintype Y] [Nonempty Y]
    (p : X → ℝ) (hp0 : ∀ x, 0 ≤ p x) (hp1 : ∑ x, p x = 1)
    (ρ : X → Matrix n n ℂ) (hρ : ∀ x, IsDensity (ρ x))
    (hcomm : SimultaneouslyDiagonalizable ρ) :
    accessibleInfo p ρ Y ≤ holevoChi p ρ := by
  classical
  rw [accessibleInfo]
  refine csSup_le ⟨mutualInfo (measJoint p ρ
    (fun y => if y = Classical.arbitrary Y then 1 else 0)), ?_⟩ ?_
  · refine ⟨_, ⟨fun y => ?_, ?_⟩, rfl⟩
    · by_cases h : y = Classical.arbitrary Y
      · simp only [h, if_pos]
        exact Matrix.PosSemidef.one
      · simp only [h, if_neg, not_false_iff]
        exact Matrix.PosSemidef.zero
    · simp
  · rintro t ⟨E, hE, rfl⟩
    exact holevo_bound_of_POVM p hp0 ρ hρ hcomm E hE

/-! ## Non-vacuity

The hypotheses of `holevo_bound` are satisfiable: here is a concrete qubit ensemble meeting
all of them. -/

/-- The two computational basis states of a qubit. -/
