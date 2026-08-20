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


theorem isTotallyDisconnected_of_interior_eq_empty {S : Set ℝ} (h : interior S = ∅) :
    IsTotallyDisconnected S := by
  intro t hts ht x hx y hy
  by_contra hxy
  rcases lt_or_gt_of_ne hxy with hlt | hlt
  · have hIcc : Set.Icc x y ⊆ t := ht.ordConnected.out hx hy
    have : Set.Ioo x y ⊆ interior S :=
      (isOpen_Ioo.subset_interior_iff).mpr
        (fun z hz => hts (hIcc (Set.Ioo_subset_Icc_self hz)))
    rw [h] at this
    exact absurd (this (Set.mem_Ioo.mpr ⟨by linarith, by linarith⟩ :
      (x + y) / 2 ∈ Set.Ioo x y)) (Set.notMem_empty _)
  · have hIcc : Set.Icc y x ⊆ t := ht.ordConnected.out hy hx
    have : Set.Ioo y x ⊆ interior S :=
      (isOpen_Ioo.subset_interior_iff).mpr
        (fun z hz => hts (hIcc (Set.Ioo_subset_Icc_self hz)))
    rw [h] at this
    exact absurd (this (Set.mem_Ioo.mpr ⟨by linarith, by linarith⟩ :
      (x + y) / 2 ∈ Set.Ioo y x)) (Set.notMem_empty _)

/-- A nonempty compact subset of `ℝ` with empty interior and no isolated points is a
Cantor set. -/
