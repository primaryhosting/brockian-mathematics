import Mathlib

/-!
# Heine Borel
Category: Pure Mathematics
Target: Math.heine_borel
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

set_option grind.warning false

open Metric Bornology

namespace Math

variable {n : ℕ}

/-- Each coordinate of a vector in `ℝ^n` is bounded in absolute value by its Euclidean norm. -/
theorem euclidean_abs_coord_le_norm (x : EuclideanSpace ℝ (Fin n)) (i : Fin n) :
    |x i| ≤ ‖x‖ := by
  simpa using PiLp.norm_apply_le (p := 2) x i

/-- `ℝ^n` with the Euclidean norm is homeomorphic to the product `Fin n → ℝ`. -/
noncomputable def euclideanHomeomorphPi : EuclideanSpace ℝ (Fin n) ≃ₜ (Fin n → ℝ) :=
  (PiLp.continuousLinearEquiv 2 ℝ fun _ : Fin n => ℝ).toHomeomorph

/-- A closed box `[-R, R]^n` in `ℝ^n` is compact: it is a finite product of compact
intervals, hence compact in the product topology, which agrees with the Euclidean topology. -/
theorem isCompact_euclidean_box (R : ℝ) :
    IsCompact {x : EuclideanSpace ℝ (Fin n) | ∀ i, x i ∈ Set.Icc (-R) R} := by
  have h : IsCompact (Set.univ.pi fun _ : Fin n => Set.Icc (-R) R) :=
    isCompact_univ_pi fun _ => isCompact_Icc
  have h2 := (euclideanHomeomorphPi (n := n)).isCompact_preimage.2 h
  convert h2 using 1
  ext x
  simp only [Set.mem_setOf_eq, Set.mem_preimage, Set.mem_univ_pi]
  rfl

/-- **Heine–Borel theorem**: a subset of `ℝ^n` is compact if and only if it is closed
and bounded. -/
theorem heine_borel (s : Set (EuclideanSpace ℝ (Fin n))) :
    IsCompact s ↔ IsClosed s ∧ IsBounded s := by
  constructor
  · intro hs
    exact ⟨hs.isClosed, hs.isBounded⟩
  · rintro ⟨hclosed, hbdd⟩
    obtain ⟨R, hR⟩ := (isBounded_iff_subset_closedBall (0 : EuclideanSpace ℝ (Fin n))).1 hbdd
    refine (isCompact_euclidean_box (n := n) R).of_isClosed_subset hclosed ?_
    intro x hx
    have hxR : ‖x‖ ≤ R := by
      have := hR hx
      simpa [Metric.mem_closedBall, dist_eq_norm] using this
    intro i
    have h1 : |x i| ≤ R := le_trans (euclidean_abs_coord_le_norm x i) hxR
    exact Set.mem_Icc.2 ⟨by linarith [abs_le.1 h1], (abs_le.1 h1).2⟩

end Math

#print axioms Math.heine_borel

