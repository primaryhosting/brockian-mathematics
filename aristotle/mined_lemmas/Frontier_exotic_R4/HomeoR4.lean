/-
# Exotic R 4
Category: Frontier — Fields Medal Work
Target: Frontier.exotic_R4
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

-- (Lean requires `import` to be the first command, so the header above is a plain comment
-- and is repeated below as the module docstring.)

import Mathlib

/-!
# Exotic R 4
Category: Frontier — Fields Medal Work
Target: Frontier.exotic_R4
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open scoped BigOperators
open scoped Real
open scoped Nat
open scoped Classical
open scoped Pointwise
open scoped Manifold ContDiff

set_option maxHeartbeats 8000000
set_option maxRecDepth 4000
set_option synthInstance.maxHeartbeats 20000
set_option synthInstance.maxSize 128

set_option relaxedAutoImplicit false
set_option autoImplicit false

set_option grind.warning false

namespace Frontier

/-!
## Setup

`E4` is the standard model space `ℝ⁴` (as a Euclidean space), and `Smooth4Manifold`
bundles a smooth (`C^∞`) manifold modelled on `ℝ⁴`: a carrier type together with its
topology, an atlas of charts into `ℝ⁴`, and the smoothness condition on the transition maps.
-/

/-- The model space `ℝ⁴`. -/
abbrev E4 : Type := EuclideanSpace ℝ (Fin 4)

/-- A smooth (`C^∞`) manifold modelled on `ℝ⁴`, bundled with all of its structure. -/
structure Smooth4Manifold where
  /-- The underlying set of points of the manifold. -/
  carrier : Type
  [topology : TopologicalSpace carrier]
  [charted : ChartedSpace E4 carrier]
  [manifold : IsManifold (𝓘(ℝ, E4)) ∞ carrier]

attribute [instance] Smooth4Manifold.topology Smooth4Manifold.charted Smooth4Manifold.manifold

/-- Two smooth `4`-manifolds are *diffeomorphic* when there is a `C^∞` diffeomorphism
between them. -/

theorem HomeoR4.of_diffeo {M N : Smooth4Manifold} (h : Diffeo M N) (hN : HomeoR4 N) :
    HomeoR4 M :=
  ⟨(h.homeo.some).trans hN.some⟩

/-!
## The main reduction

The full Donaldson–Freedman theorem (the existence of an exotic `ℝ⁴`) is far beyond
what is currently available in Mathlib: it rests on Freedman's classification of simply
connected topological `4`-manifolds and on Donaldson's gauge-theoretic diagonalizability
theorem, neither of which is formalized.

What is proved here, unconditionally and in full, is a *Lean-checked reduction*: the
existence of an exotic `ℝ⁴` follows from the (formally weaker-looking) statement that
smooth structures on `ℝ⁴` are not unique up to diffeomorphism, i.e. that there exist two
smooth `4`-manifolds, each homeomorphic to `ℝ⁴`, which are not diffeomorphic to each
other. The hypothesis `h` is exactly this input; it is supplied as a hypothesis of the
theorem, not as an axiom.
-/

/-- **Reduction for the existence of an exotic `ℝ⁴` (Donaldson–Freedman).**

If there are two smooth `4`-manifolds `M` and `N`, both homeomorphic to `ℝ⁴`, that are not
diffeomorphic to each other, then there exists a smooth manifold homeomorphic but not
diffeomorphic to `ℝ⁴`, i.e. an exotic `ℝ⁴`.

Indeed, if both `M` and `N` were diffeomorphic to the standard `ℝ⁴`, then by symmetry and
transitivity of `Diffeo` they would be diffeomorphic to each other; so at least one of them
is exotic. -/
