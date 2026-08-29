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
# Schrodinger Essentially Self Adjoint Of Weak Regularity
Category: Brockian (Literature Discharge)
Target: Brockian.Weyl.DeficiencyODE.schrodinger_essentiallySelfAdjoint_of_weakRegularity
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

/-!
## Overview

We work with unbounded operators on a complex inner product space `H`, presented as linear maps
`T : D →ₗ[ℂ] H` out of a submodule `D` (the operator domain).

For a densely defined symmetric operator `T`, essential self-adjointness is equivalent to the
symmetry of the adjoint `T†` (equivalently: `T† = T††`, i.e. the closure `T̄ = T††` is
self-adjoint).  Since the adjoint of an unbounded operator is only defined on the set of vectors
`y` for which a representing vector `z` exists, we encode `z = T† y` through the relation
`IsAdjointPair T y z`, and encode symmetry of `T†` as `AdjointIsSymmetric T`.  This avoids any
use of choice and is exactly the classical criterion.

The main result is the (bounded) Kato–Rellich theorem in the concrete Schrödinger setting: on
`L²(ℝ)`, if the kinetic part `T` (e.g. `-d²/dx²` on a core such as `Cc^∞` or the Schwartz space)
is essentially self-adjoint, then adding a potential `V` of *weak regularity* — merely a.e. measurable
and essentially bounded, with no continuity or differentiability assumed — preserves essential
self-adjointness. In particular the deficiency spaces of the Schrödinger operator `-Δ + V` are
trivial, i.e. its deficiency indices vanish (Weyl's deficiency-index criterion).
-/

open MeasureTheory

noncomputable section

namespace Brockian.Weyl.DeficiencyODE

section Abstract

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

/-- `IsAdjointPair T y z` says that `z` represents the adjoint `T† y`, i.e.
`⟪T x, y⟫ = ⟪x, z⟫` for all `x` in the domain of `T`. -/

theorem deficiency_eq_zero {D : Submodule ℂ H} {T : D →ₗ[ℂ] H}
    (hT : EssentiallySelfAdjoint T) {c : ℂ} (hc : c.im ≠ 0) {v : H}
    (hv : ∀ x : D, inner ℂ (T x - c • (x : H)) v = 0) : v = 0 := by
  have hpair : IsAdjointPair T v ((starRingEnd ℂ) c • v) := by
    intro x
    have hx := hv x
    rw [inner_sub_left, inner_smul_left, sub_eq_zero] at hx
    rw [hx, inner_smul_right]
  have hsym := hT.adjointSymmetric v ((starRingEnd ℂ) c • v) v ((starRingEnd ℂ) c • v)
    hpair hpair
  rw [inner_smul_left, inner_smul_right, RingHomCompTriple.comp_apply, RingHom.id_apply] at hsym
  have hcc : c - (starRingEnd ℂ) c ≠ 0 := by
    intro h
    apply hc
    have : (c - (starRingEnd ℂ) c).im = 0 := by rw [h]; simp
    simp [Complex.sub_im, Complex.conj_im] at this
    linarith
  have hzero : (inner ℂ v v : ℂ) = 0 := by
    have : (c - (starRingEnd ℂ) c) * (inner ℂ v v : ℂ) = 0 := by linear_combination hsym
    rcases mul_eq_zero.mp this with h | h
    · exact absurd h hcc
    · exact h
  simpa using inner_self_eq_zero.mp hzero

/-- Weyl's deficiency criterion in the form we get here: for an essentially self-adjoint operator
`T` and non-real `c`, the range of `T - c` is dense. -/
