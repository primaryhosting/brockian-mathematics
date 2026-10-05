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


theorem interior_eq_empty_of_volume_eq_zero {S : Set ℝ}
    (h : MeasureTheory.volume S = 0) : interior S = ∅ := by
  by_contra hne
  obtain ⟨x, hx⟩ := Set.nonempty_iff_ne_empty.2 hne
  have hpos : 0 < MeasureTheory.volume (interior S) :=
    isOpen_interior.measure_pos MeasureTheory.volume ⟨x, hx⟩
  have hle : MeasureTheory.volume (interior S) ≤ MeasureTheory.volume S :=
    MeasureTheory.measure_mono interior_subset
  rw [h] at hle
  exact absurd (le_antisymm hle (zero_le _)) hpos.ne'

/-- A second Lean-checked reduction of the Ten Martini Problem: it suffices to prove, for
positive coupling, irrational flux in `(0,1)` and phase in `[0,1)`, that the spectrum is
nonempty, has Lebesgue measure zero, and has no isolated points. -/
