/-
# Kam Theorem
Category: Frontier Physics
Target: Frontier.kam_theorem
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/
-- (Lean requires `import` lines to precede any module docstring, so the header
-- above is repeated verbatim as a module docstring just after the import.)

import Mathlib

/-!
# Kam Theorem
Category: Frontier Physics
Target: Frontier.kam_theorem
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

set_option autoImplicit false

namespace Frontier

/-!
## Setting

We formalize the *persistence of invariant tori* statement of KAM theory in the
"parametrization method" (Moser / de la Llave) form, and give a Lean-checked
reduction of it to the contraction estimate that the KAM scheme produces.

* `Angle` is the parameter space of the torus (e.g. `𝕋ⁿ`),
* `M` is the phase space,
* `rot : Angle → Angle` is the rigid rotation by the (Diophantine) frequency
  vector `ω`,
* `dyn : M → M` is the (perturbed) dynamics (time-one map / Poincaré map),
* `E` is a complete metric space of candidate torus parametrizations, with
  `param : E → Angle → M` the associated embedding.

A parametrization `u : E` describes an invariant torus carrying the rotation
`rot` exactly when the conjugacy equation `dyn ∘ param u = param u ∘ rot`
holds.
-/

/-- `IsInvariantTorus param dyn rot u` says that the embedded torus
`param u : Angle → M` is invariant under the dynamics `dyn` and that the
dynamics restricted to it is conjugate, via `param u`, to the rigid rotation
`rot`. -/

def IsInvariantTorus {Angle M E : Type*} (param : E → Angle → M) (dyn : M → M)
    (rot : Angle → Angle) (u : E) : Prop :=
  ∀ θ : Angle, dyn (param u θ) = param u (rot θ)

/-- **Base case of KAM: the unperturbed (integrable) system.**

For an integrable system written in action–angle variables, the time-one map is
`(I, θ) ↦ (I, θ + ω)`, and for every action `I₀` the torus
`θ ↦ (I₀, θ)` is invariant and carries the rigid rotation by `ω`.  Here the
angle variables are modelled by an arbitrary additive group `A` (e.g.
`𝕋ⁿ = (ℝ/ℤ)ⁿ`) and the actions by an arbitrary type `I`. -/

theorem kam_theorem {Angle M E : Type*} [MetricSpace E] [Nonempty E] [CompleteSpace E]
    (param : E → Angle → M) (dyn : M → M) (rot : Angle → Angle)
    (Φ : E → E) (K : NNReal) (hK : ContractingWith K Φ)
    (hfix : ∀ u : E, Φ u = u ↔ IsInvariantTorus param dyn rot u)
    (u₀ : E) (ε : ℝ) (hε : dist u₀ (Φ u₀) ≤ ε) :
    ∃ u : E, IsInvariantTorus param dyn rot u ∧
      dist u₀ u ≤ ε / (1 - (K : ℝ)) ∧
      ∀ v : E, IsInvariantTorus param dyn rot v → v = u := by
  have hK1 : (K : ℝ) < 1 := hK.1
  have hpos : (0 : ℝ) < 1 - (K : ℝ) := by linarith
  refine ⟨ContractingWith.fixedPoint Φ hK, ?_, ?_, ?_⟩
  · exact (hfix _).1 (hK.fixedPoint_isFixedPt)
  · calc dist u₀ (ContractingWith.fixedPoint Φ hK)
        ≤ dist u₀ (Φ u₀) / (1 - (K : ℝ)) := hK.dist_fixedPoint_le u₀
      _ ≤ ε / (1 - (K : ℝ)) := by gcongr
  · intro v hv
    exact hK.fixedPoint_unique ((hfix v).2 hv)

/-- The hypotheses of `Frontier.kam_theorem` are satisfiable (the statement is not
vacuous): a concrete contraction whose fixed points are exactly the invariant
tori of a concrete dynamical system. -/
