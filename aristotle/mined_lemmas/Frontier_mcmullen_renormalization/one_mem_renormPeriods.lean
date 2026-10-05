/-
# Mcmullen Renormalization
Category: Frontier — Fields Medal Work
Target: Frontier.mcmullen_renormalization
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

open scoped BigOperators
open scoped Real
open scoped Nat
open scoped Classical
open scoped Pointwise

set_option maxHeartbeats 8000000
set_option maxRecDepth 4000
set_option synthInstance.maxHeartbeats 400000
set_option synthInstance.maxSize 128

set_option relaxedAutoImplicit false
set_option autoImplicit false

namespace Frontier

/-! ## Quadratic-like maps

Following Douady–Hubbard and McMullen, a *quadratic-like map* is a holomorphic proper
degree-two branched covering `f : U → V` between simply connected planar domains with
`closure U` a compact subset of `V`.  We encode "proper of degree two, branched over the
unique critical value" by the fibre conditions `fiber_crit` and `fiber_two`. -/

/-- A quadratic-like map `f : U → V` with critical point `c`. -/
structure QuadraticLike (f : ℂ → ℂ) (U V : Set ℂ) (c : ℂ) : Prop where
  /-- The domain is open. -/
  isOpen_U : IsOpen U
  /-- The range is open. -/
  isOpen_V : IsOpen V
  /-- `U` is relatively compact. -/
  isCompact_closure : IsCompact (closure U)
  /-- `U` is compactly contained in `V`. -/
  closure_subset : closure U ⊆ V
  /-- `f` is holomorphic on a neighbourhood of `V`. -/
  analytic : AnalyticOnNhd ℂ f V
  /-- `f` maps `U` into `V`. -/
  mapsTo : Set.MapsTo f U V
  /-- The critical point lies in `U`. -/
  crit_mem : c ∈ U
  /-- `c` is a critical point. -/
  crit_deriv : deriv f c = 0
  /-- The fibre over the critical value is the single (doubled) point `c`. -/
  fiber_crit : {z ∈ U | f z = f c} = {c}
  /-- Every other fibre consists of exactly two points: `f : U → V` is proper of degree 2. -/
  fiber_two : ∀ w ∈ V, w ≠ f c → ∃ a b : ℂ, a ≠ b ∧ {z ∈ U | f z = w} = {a, b}

/-- The filled Julia set of a quadratic-like map `f : U → V`:
points whose whole forward orbit stays in `U`. -/

theorem one_mem_renormPeriods {f : ℂ → ℂ} {U V : Set ℂ} {c : ℂ}
    (hf : QuadraticLike f U V c) (hK : IsConnected (filledJulia f U)) :
    1 ∈ renormPeriods f U c := by
  refine ⟨U, V, Nat.one_pos, ?_, subset_rfl, ?_, ?_⟩
  · rwa [Function.iterate_one]
  · intro i hi
    interval_cases i
    simpa using Set.mapsTo_id U
  · rwa [Function.iterate_one]

/-! ## The tower (reduction) law: periods multiply -/

/-- **Reduction.** If `f` is renormalizable with period `n` and the renormalized map
`f^[n] : U₁ → V₁` is itself renormalizable with period `m`, then `f` is renormalizable
with period `n * m`.  This is the tower law underlying McMullen's inductive analysis of
infinitely renormalizable maps. -/
