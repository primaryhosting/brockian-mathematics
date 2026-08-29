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

/-
# Schrodinger Essentially Self Adjoint Of Weak Regularity
Category: Brockian (Literature Discharge)
Target: Brockian.Weyl.DeficiencyODE.schrodinger_essentiallySelfAdjoint_of_weakRegularity
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/
import Mathlib

/-!
# Schrodinger Essentially Self Adjoint Of Weak Regularity
Category: Brockian (Literature Discharge)
Target: Brockian.Weyl.DeficiencyODE.schrodinger_essentiallySelfAdjoint_of_weakRegularity
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open scoped BigOperators
open scoped Real
open scoped Nat
open scoped Classical
open scoped Pointwise
open scoped ComplexInnerProductSpace

set_option maxHeartbeats 8000000
set_option maxRecDepth 4000
set_option synthInstance.maxHeartbeats 20000
set_option synthInstance.maxSize 128

set_option relaxedAutoImplicit false
set_option autoImplicit false

set_option grind.warning false

namespace Brockian.Weyl.DeficiencyODE

open Filter Topology

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

/-- A linear operator `T` with domain the submodule `D` of a complex Hilbert space is
*symmetric* if `⟪T x, y⟫ = ⟪x, T y⟫` for all `x, y` in the domain. -/

theorem essentiallySelfAdjoint_of_weakRegularity [CompleteSpace H] (hsym : IsSymmetricOn D T)
    (hreg : WeakRegularity D T) : EssentiallySelfAdjoint D T := by
  have key : ∀ u v : H, IsAdjointPair D T u v → GraphLimit D T u v := by
    intro u v huv
    obtain ⟨p, q, hpq, hEq⟩ :=
      exists_graphLimit hsym hreg (Or.inl rfl) (v + Complex.I • u)
    have hpq' : IsAdjointPair D T p q := isAdjointPair_of_graphLimit hsym hpq
    have hvq : v - q = -(Complex.I • (u - p)) := by
      have : q + Complex.I • p = v + Complex.I • u := hEq
      rw [smul_sub]
      linear_combination (norm := module) -this
    have hw : IsAdjointPair D T (u - p) (-(Complex.I • (u - p))) := by
      intro z
      rw [inner_sub_right, huv z, hpq' z, ← inner_sub_right, ← hvq]
    have hw0 : u - p = 0 := hreg _ (Or.inr hw)
    have hup : u = p := sub_eq_zero.mp hw0
    have hvq0 : v = q := by
      have h1 : v - q = 0 := by rw [hvq, hw0, smul_zero, neg_zero]
      exact sub_eq_zero.mp h1
    rw [hup, hvq0]
    exact hpq
  intro u v u' v' h1 h2
  exact inner_graphLimit_symm hsym (key u v h1) (key u' v' h2)

/-- **Schrödinger operators are essentially self-adjoint under weak regularity.**

`T = K + P` is a Schrödinger operator on a complex Hilbert space `H`, written as the sum of a
symmetric kinetic part `K` and a symmetric potential part `P`, both defined on a common domain
`D`.  If `T` is weakly regular — the limit-point condition, i.e. the deficiency ODEs
`T† u = ± i u` have no nontrivial weak solutions in `H` — then `T` is essentially self-adjoint.

Formerly this was stated with the essential-self-adjointness criterion assumed as a named
hypothesis; here that hypothesis is discharged (see
`Brockian.Weyl.DeficiencyODE.essentiallySelfAdjoint_of_weakRegularity`), making the statement
unconditional. -/
