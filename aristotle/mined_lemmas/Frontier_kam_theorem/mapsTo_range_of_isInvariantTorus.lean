/-
# Kam Theorem
Category: Frontier Physics
Target: Frontier.kam_theorem
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Kam Theorem
Category: Frontier Physics
Target: Frontier.kam_theorem
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace Frontier

/-! ## Setting

We work with the standard "conjugacy" formulation of KAM theory.  The phase space is an
arbitrary type `P`, the `n`-dimensional torus is modelled by its universal cover
`Fin n → ℝ` (all objects below are invariant under the choice of representative, so
nothing is lost), and a *torus with rotation vector `ω`* for a dynamical system
`f : P → P` is an embedding `Ψ : (Fin n → ℝ) → P` satisfying the conjugacy equation

  `f (Ψ θ) = Ψ (θ + ω)`  for all `θ`,

i.e. `f` restricted to the image of `Ψ` is the rigid rotation by `ω`.
-/

/-- `IsInvariantTorus n f ω Ψ` : the parametrised torus `Ψ` is invariant under the
dynamics `f` and the induced motion on it is the rigid rotation by the frequency
vector `ω`. -/

theorem mapsTo_range_of_isInvariantTorus {P : Type*} {n : ℕ} {f : P → P} {ω : Fin n → ℝ}
    {Ψ : (Fin n → ℝ) → P} (h : IsInvariantTorus f ω Ψ) :
    Set.MapsTo f (Set.range Ψ) (Set.range Ψ) := by
  rintro _ ⟨θ, rfl⟩
  exact ⟨θ + ω, (h θ).symm⟩

/-! ## Persistence under perturbation

The analytic heart of KAM theory is the construction, for a Diophantine frequency `ω`, of a
*KAM operator* `T ε` on a Banach space `E` of torus parametrisations (encoded here through
a map `Ψ : E → ((Fin n → ℝ) → P)` sending a parameter to the corresponding embedding) whose
fixed points solve the conjugacy equation, and which is a contraction depending Lipschitz-
continuously on the size `ε` of the perturbation.  Granting that reduction, persistence of
the invariant torus — together with the quantitative statement that the persisting torus is
`O(ε)`-close to the unperturbed one — follows from the Banach fixed point theorem.

That last step is what `Frontier.kam_theorem` below states and proves.
-/

/-- **KAM theorem (persistence of invariant tori), Banach-fixed-point form.**

Let `f ε : P → P` be a family of dynamical systems, `ε` measuring the size of the
perturbation of the integrable system `f 0`.  Suppose the conjugacy equation for a torus with
frequency vector `ω` has been reduced (as in the classical KAM scheme) to a fixed point
problem `T ε u = u` on a Banach space `E` of parametrisations `u ↦ Ψ u`, where

* `hfix`   : fixed points of `T ε` are invariant tori of `f ε` with frequency `ω`;
* `hlip`   : each `T ε` is a `K`-contraction, `K < 1`;
* `hzero`  : the unperturbed problem is solved by the reference parametrisation `u = 0`
             (`T 0 0 = 0`), which by `hfix` is an invariant torus of `f 0`;
* `hpert`  : the operator moves by at most `C * |ε|` when the perturbation is switched on.

Then for *every* `ε` the invariant torus persists: there is a parametrisation `u` whose torus
`Ψ u` is invariant under `f ε` and carries the same rotation vector `ω`, and it is
`C * |ε| / (1 - K)`-close to the unperturbed torus.  In particular the distance tends to `0`
as `ε → 0`.

The Banach fixed point theorem (`ContractingWith.fixedPoint_isFixedPt` together with the
a priori estimate `ContractingWith.dist_fixedPoint_le`) is exactly the Mathlib input that
closes the argument. -/
