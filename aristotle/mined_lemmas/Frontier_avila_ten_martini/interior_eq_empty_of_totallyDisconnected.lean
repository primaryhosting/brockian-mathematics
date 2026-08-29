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


theorem interior_eq_empty_of_totallyDisconnected {S : Set ℝ} (h : IsTotallyDisconnected S) :
    interior S = ∅ := by
  by_contra hne
  obtain ⟨x, hx⟩ := Set.nonempty_iff_ne_empty.2 hne
  obtain ⟨e, he, hball⟩ := Metric.isOpen_iff.1 isOpen_interior x hx
  have hsub : Set.Ioo (x - e) (x + e) ⊆ S := by
    rw [← Real.ball_eq_Ioo]
    exact hball.trans interior_subset
  have hss := h _ hsub isPreconnected_Ioo
  have h1 : x ∈ Set.Ioo (x - e) (x + e) := ⟨by linarith, by linarith⟩
  have h2 : x + e / 2 ∈ Set.Ioo (x - e) (x + e) := ⟨by linarith, by linarith⟩
  have := hss h1 h2
  linarith

/-! ## The Ten Martini Problem -/

/-- **The Ten Martini Problem** (Avila–Jitomirskaya): for every nonzero coupling `λ`,
every irrational flux `α` and every phase `θ`, the spectrum of the almost Mathieu
operator is a Cantor set. -/
