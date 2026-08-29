/-
# Mcmullen Renormalization
Category: Frontier — Fields Medal Work
Target: Frontier.mcmullen_renormalization
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/
import Mathlib

/-!
# Mcmullen Renormalization
Category: Frontier — Fields Medal Work
Target: Frontier.mcmullen_renormalization
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

namespace Frontier

/-! ## Quadratic-like maps

A *quadratic-like map* (Douady–Hubbard; the basic object of McMullen's work on
renormalization) is a holomorphic proper degree-two branched cover `f : U → V`
between open subsets of `ℂ` with `U` compactly contained in `V`.  The
degree-two condition is encoded concretely below: there is one critical value,
whose fiber is a single point, and every other value has exactly two
preimages. -/

/-- The quadratic family `z ↦ z ^ 2 + c`. -/

def qmap (c : ℂ) : ℂ → ℂ := fun z => z ^ 2 + c

/-- A quadratic-like map `f : U → V`. -/
structure QuadraticLike (f : ℂ → ℂ) (U V : Set ℂ) : Prop where
  /-- The source is open. -/
  isOpen_source : IsOpen U
  /-- The target is open. -/
  isOpen_target : IsOpen V
  /-- The closure of the source is compact. -/
  isCompact_closure : IsCompact (closure U)
  /-- `U` is compactly contained in `V`. -/
  closure_subset : closure U ⊆ V
  /-- `f` is holomorphic on `U`. -/
  analyticOnNhd : AnalyticOnNhd ℂ f U
  /-- `f` maps `U` into `V`. -/
  mapsTo : Set.MapsTo f U V
  /-- `f : U → V` is a proper branched cover of degree two. -/
  degree_two : ∃ w₀ ∈ V, {z ∈ U | f z = w₀}.ncard = 1 ∧
    ∀ w ∈ V, w ≠ w₀ → {z ∈ U | f z = w}.ncard = 2

/-- The filled Julia set of `f` at radius `R`: points whose whole forward orbit
stays in the closed disk of radius `R`. -/
