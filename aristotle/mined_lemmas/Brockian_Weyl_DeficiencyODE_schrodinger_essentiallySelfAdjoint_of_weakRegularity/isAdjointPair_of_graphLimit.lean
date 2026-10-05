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

/-
# Schrodinger Essentially Self Adjoint Of Weak Regularity
Category: Brockian (Literature Discharge)
Target: Brockian.Weyl.DeficiencyODE.schrodinger_essentiallySelfAdjoint_of_weakRegularity
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/
import Mathlib

/-!
# Schrodinger Essentially Self Adjoint Of Weak Regularity
Category: Brockian (Literature Discharge)
Target: Brockian.Weyl.DeficiencyODE.schrodinger_essentiallySelfAdjoint_of_weakRegularity
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open scoped BigOperators
open scoped Real
open scoped Nat
open scoped Classical
open scoped Pointwise
open scoped ComplexInnerProductSpace

set_option maxHeartbeats 8000000
set_option maxRecDepth 4000
set_option synthInstance.maxHeartbeats 20000
set_option synthInstance.maxSize 128

set_option relaxedAutoImplicit false
set_option autoImplicit false

set_option grind.warning false

namespace Brockian.Weyl.DeficiencyODE

open Filter Topology

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

/-- A linear operator `T` with domain the submodule `D` of a complex Hilbert space is
*symmetric* if `⟪T x, y⟫ = ⟪x, T y⟫` for all `x, y` in the domain. -/

theorem isAdjointPair_of_graphLimit (hsym : IsSymmetricOn D T) {p q : H}
    (h : GraphLimit D T p q) : IsAdjointPair D T p q := by
  obtain ⟨x, hx, hTx⟩ := h
  intro z
  have h1 : Tendsto (fun n => ⟪T z, (x n : H)⟫) atTop (𝓝 ⟪T z, p⟫) :=
    tendsto_const_nhds.inner hx
  have h2 : Tendsto (fun n => ⟪(z : H), T (x n)⟫) atTop (𝓝 ⟪(z : H), q⟫) :=
    tendsto_const_nhds.inner hTx
  have he : (fun n => ⟪T z, (x n : H)⟫) = fun n => ⟪(z : H), T (x n)⟫ :=
    funext fun n => hsym _ _
  rw [he] at h1
  exact tendsto_nhds_unique h1 h2

/-- The Pythagoras identity `‖T x + c x‖² = ‖T x‖² + ‖c x‖²` for purely imaginary `c`. -/
