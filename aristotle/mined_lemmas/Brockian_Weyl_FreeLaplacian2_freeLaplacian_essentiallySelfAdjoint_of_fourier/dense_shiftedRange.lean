import Mathlib

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

import Mathlib

/-!
# A basic criterion for essential self-adjointness

Let `T` be a densely defined symmetric operator on a complex Hilbert space `H`.
If the ranges of `T + i` and `T - i` are both dense, then the adjoint `T†` is
self-adjoint, i.e. `T` is essentially self-adjoint.

Provenance: Aristotle theorem prover (Harmonic)
-/

open scoped ComplexConjugate
open LinearPMap MeasureTheory Filter Topology

namespace Brockian.Weyl

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

local notation "⟪" x ", " y "⟫" => inner ℂ x y

/-- The range of `T + z` for a partially defined operator `T` and a scalar `z`. -/

theorem dense_shiftedRange {z : ℂ} (hz : z.im ≠ 0) :
    Dense (Brockian.Weyl.shiftedRange freeLaplacian z) := by
  refine Dense.mono ?_ dense_range_schwartzToL2
  rintro _ ⟨h, rfl⟩
  obtain ⟨u, hu⟩ := Brockian.Weyl.exists_schwartz_neg_deriv_two_add_smul hz h
  refine ⟨⟨schwartzToL2 u, mem_freeLaplacian_domain u⟩, ?_⟩
  show freeLaplacian ⟨schwartzToL2 u, mem_freeLaplacian_domain u⟩ + z • (schwartzToL2 u)
    = schwartzToL2 h
  rw [freeLaplacian_apply, freeLaplacianSchwartz_apply, ← hu]
  simp

/-- **The free Laplacian on the Schwartz space is essentially self-adjoint.**

The operator `-d²/dx²` on `L²(ℝ)` with domain the Schwartz functions has a self-adjoint adjoint,
i.e. it is essentially self-adjoint.

The name records that the proof proceeds via the Fourier transform: the hypothesis about the
Fourier transform (solvability of `-u'' ± i u = h` on the Schwartz space) is discharged here,
so the statement is unconditional. -/
