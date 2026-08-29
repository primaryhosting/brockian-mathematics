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

set_option maxHeartbeats 8000000
set_option maxRecDepth 4000
set_option synthInstance.maxHeartbeats 20000
set_option synthInstance.maxSize 128

set_option relaxedAutoImplicit false
set_option autoImplicit false

set_option pp.fullNames true
set_option pp.structureInstances true
set_option pp.coercions.types true
set_option pp.piBinderTypes true

set_option grind.warning false

namespace Frontier

open scoped ENNReal

/-! ## The Hilbert space `ℓ²(ℤ, ℝ)` -/

/-- The Hilbert space `ℓ²(ℤ)` (real scalars) on which the almost Mathieu operator acts. -/
abbrev L2Z : Type := lp (fun _ : ℤ => ℝ) 2

/-! ## Multiplication and shift operators on `ℓ²(ℤ)` -/


theorem totallyDisconnected_of_interior_eq_empty {S : Set ℝ} (h : interior S = ∅) :
    IsTotallyDisconnected S := by
  intro t hts htpre
  have key : ∀ a b : ℝ, a ∈ t → b ∈ t → a < b → False := by
    intro a b ha hb hab
    have hord : t.OrdConnected := htpre.ordConnected
    have hsub : Set.Icc a b ⊆ S := (hord.out ha hb).trans hts
    have : Set.Ioo a b ⊆ interior S := by
      rw [← interior_Icc]
      exact interior_mono hsub
    have hx : (a + b) / 2 ∈ Set.Ioo a b := ⟨by linarith, by linarith⟩
    have := this hx
    rw [h] at this
    exact this
  intro x hx y hy
  rcases lt_trichotomy x y with hlt | heq | hgt
  · exact absurd (key x y hx hy hlt) not_false
  · exact heq
  · exact absurd (key y x hy hx hgt) not_false

/-- A totally disconnected subset of `ℝ` has empty interior. -/
