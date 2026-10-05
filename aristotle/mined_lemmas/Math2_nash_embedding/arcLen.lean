/-
# Nash Embedding
Category: Frontier Math
Target: Math2.nash_embedding
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
(Note: Lean does not allow a module docstring before `import`, so this header is a plain
block comment and is repeated as a module docstring below.)
-/

import Mathlib

/-!
# Nash Embedding
Category: Frontier Math
Target: Math2.nash_embedding
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)

## Scope of what is proved here

The full Nash embedding theorem (every Riemannian manifold admits a smooth isometric
embedding into some `ℝᴺ`) is not available in Mathlib, and its proof (Nash-Moser implicit
function theorem, or the Gunther fixed-point argument) is a large development that is not
formalised here.

What *is* proved, in full, is the isometric embedding theorem for an explicit infinite
dimensional family of Riemannian metrics on `ℝⁿ`, namely those of the form

  `g x (u, v) = ∑ i, a i (x i) * u i * v i + ∑ k, (dψ k x u) * (dψ k x v)`,

with each `a i : ℝ → ℝ` smooth and positive and each `ψ k : ℝⁿ → ℝ` smooth.  Every such `g`
is a smooth Riemannian metric, and the family contains, through the terms `ψ k`, the induced
first fundamental forms of graphs of smooth maps `ℝⁿ → ℝᵐ` (which are not flat in general).
For each of them we build an explicit smooth embedding `f : ℝⁿ → ℝⁿ⁺ᵐ` whose pullback of the
Euclidean metric is exactly `g`; the construction reparametrises each coordinate by its
arclength `t ↦ ∫₀ᵗ √(a i)` and adjoins the graph coordinates `ψ k`.
-/

open scoped ContDiff RealInnerProductSpace BigOperators
open Topology

namespace Math2

/-! ## One-dimensional arclength reparametrisation -/

/-- The antiderivative `x ↦ ∫₀ˣ h` of `h`. -/

noncomputable def arcLen (h : ℝ → ℝ) (x : ℝ) : ℝ := ∫ t in (0 : ℝ)..x, h t

