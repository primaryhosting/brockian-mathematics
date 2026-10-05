/-
# Poincare 3 Sphere
Category: Frontier — Moonshot
Target: Frontier.poincare_3sphere
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Poincare 3 Sphere
Category: Frontier — Moonshot
Target: Frontier.poincare_3sphere
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

set_option autoImplicit false

open Metric Set Topology Module

namespace Frontier

universe u

/-- The 3-sphere, realized as the unit sphere in 4-dimensional Euclidean space. -/
abbrev Sphere3 : Type := Metric.sphere (0 : EuclideanSpace ℝ (Fin 4)) 1

/-- `M` is a *closed 3-manifold*: a compact, Hausdorff, second countable space which is
locally homeomorphic to `ℝ³` (equivalently, a compact 3-manifold without boundary). -/

theorem sphere3_exists_punctured_homeomorph_euclidean :
    ∃ p : Sphere3, Nonempty ({x : Sphere3 // x ≠ p} ≃ₜ EuclideanSpace ℝ (Fin 3)) :=
  ⟨⟨EuclideanSpace.single 0 1, by simp⟩, ⟨spherePuncturedHomeomorph _⟩⟩

/-! ### The reduction -/

/-- **Lean-checked reduction of the Poincaré conjecture.**

The Poincaré conjecture — every simply-connected closed 3-manifold is homeomorphic to `S³` —
is *equivalent* to the punctured-sphere criterion: every simply-connected closed 3-manifold has
a point whose complement is homeomorphic to `ℝ³`.

The nontrivial direction proved here (`←`) is the reduction proper: it upgrades a purely local
statement (one puncture is Euclidean) to a global homeomorphism with `S³`, via the uniqueness of
the one-point compactification of a compact Hausdorff space and the identification of the
one-point compactification of `ℝ³` with `S³` (stereographic projection). The direction (`→`)
uses that the 3-sphere itself is a closed 3-manifold with punctures homeomorphic to `ℝ³`. -/
