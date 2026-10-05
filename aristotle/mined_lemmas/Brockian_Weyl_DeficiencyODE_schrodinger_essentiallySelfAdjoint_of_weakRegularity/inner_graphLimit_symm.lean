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

theorem inner_graphLimit_symm (hsym : IsSymmetricOn D T) {p q p' q' : H}
    (h : GraphLimit D T p q) (h' : GraphLimit D T p' q') : ⟪q, p'⟫ = ⟪p, q'⟫ := by
  obtain ⟨x, hx, hTx⟩ := h
  obtain ⟨y, hy, hTy⟩ := h'
  have h1 : Tendsto (fun n => ⟪T (x n), (y n : H)⟫) atTop (𝓝 ⟪q, p'⟫) := hTx.inner hy
  have h2 : Tendsto (fun n => ⟪(x n : H), T (y n)⟫) atTop (𝓝 ⟪p, q'⟫) := hx.inner hTy
  have he : (fun n => ⟪T (x n), (y n : H)⟫) = fun n => ⟪(x n : H), T (y n)⟫ :=
    funext fun n => hsym _ _
  rw [he] at h1
  exact tendsto_nhds_unique h1 h2

/-- Every point of the graph closure is an adjoint pair. -/
