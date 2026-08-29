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

def InfinitelyRenormalizable (f : ℂ → ℂ) (U : Set ℂ) (c : ℂ) : Prop :=
  ∀ N : ℕ, ∃ n ∈ renormPeriods f U c, N < n

/-! ## Base case: period one -/

/-- **Base case.** A quadratic-like map with connected filled Julia set is renormalizable
with period `1` (it is its own first renormalization). -/
