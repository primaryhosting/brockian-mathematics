import Mathlib

/-!
# Figalli OT Regularity
Category: Frontier — Fields Medal Work
Target: Frontier.figalli_OT_regularity
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
set_option pp.funBinderTypes true
set_option pp.letVarTypes true
set_option pp.piBinderTypes true

set_option grind.warning false

namespace Frontier

/-!
## Setting

We formalize the one-dimensional base case of the Ma–Trudinger–Wang / Figalli regularity
theory for optimal transport.

The transport cost is the quadratic cost `c x y = (x - y)^2 / 2`.  For this cost Brenier's

theorem exists_delta_right {T : ℝ → ℝ} {a r ε : ℝ} (hr : 0 < r) (hε : 0 < ε)
    (hmono : MonotoneOn T (Set.Icc (a - r) (a + r)))
    (hoc : (T '' Set.Icc (a - r) (a + r)).OrdConnected) :
    ∃ δ > 0, ∀ y ∈ Set.Icc a (a + δ), T y ≤ T a + ε := by
  have ha : a ∈ Set.Icc (a - r) (a + r) := ⟨by linarith, by linarith⟩
  by_cases h : ∀ y ∈ Set.Icc a (a + r), T y ≤ T a + ε
  · exact ⟨r, hr, h⟩
  · push_neg at h
    obtain ⟨x, hx, hxT⟩ := h
    have hxmem : x ∈ Set.Icc (a - r) (a + r) := ⟨by linarith [hx.1], hx.2⟩
    have hm : T a + ε / 2 ∈ Set.Icc (T a) (T x) := by
      constructor
      · linarith
      · linarith
    have hmem : T a + ε / 2 ∈ T '' Set.Icc (a - r) (a + r) :=
      hoc.out (Set.mem_image_of_mem T ha) (Set.mem_image_of_mem T hxmem) hm
    obtain ⟨c, hc, hcT⟩ := hmem
    have hac : a < c := by
      by_contra hle
      push_neg at hle
      have := hmono hc ha hle
      rw [hcT] at this
      linarith
    refine ⟨c - a, by linarith, ?_⟩
    intro y hy
    have hyc : y ≤ c := by have := hy.2; linarith
    have hymem : y ∈ Set.Icc (a - r) (a + r) :=
      ⟨by linarith [hy.1], le_trans hyc hc.2⟩
    have := hmono hymem hc hyc
    rw [hcT] at this
    linarith

/-- One-sided (left) estimate, the mirror image of `Frontier.exists_delta_right`. -/
