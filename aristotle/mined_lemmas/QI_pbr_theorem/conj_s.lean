import Mathlib

/-!
# Pbr Theorem
Category: Frontier Qi
Target: QI.pbr_theorem
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

namespace QI

open Complex Finset

/-! ## The two-qubit vectors used in the PBR argument -/

/-- The normalisation constant `1/√2`. -/

@[simp] lemma conj_s : (starRingEnd ℂ) s = s := Complex.conj_ofReal _

/-- A single-qubit vector. -/
abbrev Vec2 := Fin 2 → ℂ

/-- A two-qubit vector, indexed by pairs of qubit indices. -/
abbrev Vec4 := Fin 2 × Fin 2 → ℂ

/-- `|0⟩`. -/
