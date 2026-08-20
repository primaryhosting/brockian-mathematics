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

set_option maxHeartbeats 1000000

namespace Frontier

open Set

/-!
## Quadratic-like maps

Following Douady–Hubbard and McMullen (*Complex Dynamics and Renormalization*),
a **quadratic-like map** is a holomorphic proper degree-two branched covering
`f : V → U` between topological disks with `V ⋐ U`, whose unique critical point we
normalise to be `0`.

The structure below records the data and the properties that are used in the
statements proved here: `V ⊆ U` open subsets of `ℂ`, `f` analytic on a neighbourhood
of each point of `V`, `f` maps `V` into `U` and *onto* `U` (properness/surjectivity),
every fibre over `U` has at most two points (degree `≤ 2`), and `0 ∈ V` is a
critical point of `f`.
-/

/-- A quadratic-like map, presented as the data of the two domains `V ⊆ U ⊆ ℂ` and the
holomorphic map `f : V → U`, which is surjective, has fibres of cardinality at most two
and has a critical point at the origin. -/
structure QuadraticLike where
  /-- The map. -/
  f : ℂ → ℂ
  /-- The target (range) disk. -/
  U : Set ℂ
  /-- The source disk, compactly contained in `U` in the classical definition. -/
  V : Set ℂ
  isOpen_U : IsOpen U
  isOpen_V : IsOpen V
  subset_UV : V ⊆ U
  mapsTo : Set.MapsTo f V U
  surjOn : U ⊆ f '' V
  analytic : AnalyticOnNhd ℂ f V
  crit_mem : (0 : ℂ) ∈ V
  deriv_crit : deriv f 0 = 0
  fiber_encard_le_two : ∀ w ∈ U, {z ∈ V | f z = w}.encard ≤ 2

/-- `R` is a **renormalization of period `n`** of the quadratic-like map `Q`: `R` is itself
a quadratic-like map, its underlying map is the `n`-th iterate of `Q`, and its domains are
contained in those of `Q`.  (This is the combinatorial skeleton of McMullen's definition:
`Q.f^[n] : R.V → R.U` is again quadratic-like around the critical point.) -/

theorem renormalizable_one (Q : QuadraticLike) : Renormalizable Q 1 :=
  ⟨Q, isRenormalizationOf_self_one Q⟩

/-!
## The reduction: renormalization periods multiply

A renormalization of a renormalization is a renormalization, of the product period.
This is the formal counterpart of the fact that an infinitely renormalizable map has a
nested sequence of renormalization periods `n₁ ∣ n₂ ∣ ⋯`.
-/

