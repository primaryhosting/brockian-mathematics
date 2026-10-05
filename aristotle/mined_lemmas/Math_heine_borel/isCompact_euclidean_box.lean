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
