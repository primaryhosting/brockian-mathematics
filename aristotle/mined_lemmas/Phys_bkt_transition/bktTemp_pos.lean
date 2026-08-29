import Mathlib

/-!
# Bkt Transition
Category: Frontier Phys
Target: Phys.bkt_transition
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

namespace Phys

/-! ## The two–dimensional XY model -/

/-- Sites of the two-dimensional square lattice `ℤ²`. -/
abbrev Site : Type := ℤ × ℤ

/-- The XY-model Hamiltonian `H(θ) = -J ∑_{⟨xy⟩} cos (θ x - θ y)` for a finite collection
of nearest-neighbour bonds. -/

theorem bktTemp_pos {J : ℝ} (hJ : 0 < J) : 0 < bktTemp J := by
  have := Real.pi_pos
  simp only [bktTemp]
  positivity

/-- The spin-wave (Kosterlitz–Thouless) anomalous exponent `η(T) = T / (2πJ)`, governing the
power-law decay `⟨s₀ · s_r⟩ ∼ r^{-η}` of correlations in the quasi-long-range-ordered phase. -/
