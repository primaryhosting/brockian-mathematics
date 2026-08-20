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
theorem integrable_isInvariantTorus {I A : Type*} [AddCommGroup A] (I₀ : I) (ω : A) :
    IsInvariantTorus (E := Unit) (fun _ θ => (I₀, θ)) (fun p => (p.1, p.2 + ω))
      (fun θ => θ + ω) () := by
  intro θ
  rfl

/-- **KAM theorem (persistence of invariant tori), reduced to the contraction
estimate.**

Assume that the KAM/Newton scheme for the dynamics `dyn` has been carried out,
i.e. that we are given an operator `Φ : E → E` on a complete space of torus
parametrizations whose fixed points are exactly the invariant tori carrying the
rotation `rot` (hypothesis `hfix`), and which is a contraction with constant
`K < 1` (hypothesis `hK`).  Suppose the approximately invariant torus `u₀`
(the unperturbed torus) has residual error at most `ε`, i.e.
`dist u₀ (Φ u₀) ≤ ε` — this is the smallness-of-perturbation hypothesis.

Then a genuine invariant torus exists, it is the *unique* one, and it lies
within `ε / (1 - K)` of the unperturbed torus: the invariant torus persists and
is `O(ε)`-close to the unperturbed one.

The proof is Banach's fixed point theorem in the quantitative form available in
Mathlib: `ContractingWith.fixedPoint`, `ContractingWith.fixedPoint_isFixedPt`,
`ContractingWith.dist_fixedPoint_le` and `ContractingWith.fixedPoint_unique`. -/
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
theorem kam_hypotheses_satisfiable :
    ∃ (Φ : ℝ → ℝ) (K : NNReal), ContractingWith K Φ ∧
      (∀ u : ℝ, Φ u = u ↔
        IsInvariantTorus (fun (u : ℝ) (_ : Unit) => u) (fun m : ℝ => m / 2) id u) := by
  refine ⟨fun u => u / 2, 1 / 2, ⟨by norm_num, LipschitzWith.of_dist_le_mul ?_⟩, ?_⟩
  · intro x y
    rw [Real.dist_eq, Real.dist_eq, ← sub_div, abs_div]
    norm_num
    linarith
  · intro u
    exact ⟨fun h _ => by simpa using h, fun h => by simpa using h ()⟩

end Frontier

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

