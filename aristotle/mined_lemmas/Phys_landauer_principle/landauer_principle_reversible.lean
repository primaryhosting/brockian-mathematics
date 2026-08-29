/-
# Landauer Principle
Category: Frontier Phys
Target: Phys.landauer_principle
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
set_option synthInstance.maxHeartbeats 20000
set_option synthInstance.maxSize 128

set_option relaxedAutoImplicit false
set_option autoImplicit false

set_option grind.warning false

/-!
# Landauer Principle
Category: Frontier Phys
Target: Phys.landauer_principle
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)

Erasing one bit of information dissipates at least `k T log 2` of heat.

The setting formalised here is the standard statistical-mechanical derivation:

* the memory is a two-state system (`Bool`), initially in the uniform state
  (one bit of information, entropy `log 2`);
* the heat bath is a finite system with energies `E`, initially in the Gibbs
  state at inverse temperature `beta = 1 / (k T)`;
* system and bath are initially uncorrelated;
* the joint system is isolated, so its Shannon entropy does not decrease
  (in particular this holds, with equality, for reversible microscopic
  dynamics, i.e. for a bijection of the joint state space);
* the process is an *erasure*: the final marginal state of the memory is a
  point mass.

Then the heat `Q` absorbed by the bath is at least `k T log 2`.

The proof uses: invariance of Shannon entropy under relabelling, additivity on
product distributions, subadditivity (both consequences of Gibbs' inequality)
and the maximum-entropy property of the Gibbs state.
-/

namespace Phys

open Finset

/-- A probability distribution on a finite type. -/
structure IsProbDist {α : Type*} [Fintype α] (p : α → ℝ) : Prop where
  nonneg : ∀ a, 0 ≤ p a
  sum_one : ∑ a, p a = 1

/-- Shannon entropy (in nats) of a distribution on a finite type. -/

theorem landauer_principle_reversible {B : Type*} [Fintype B] [Nonempty B]
    (E : B → ℝ) (k T : ℝ) (hk : 0 < k) (hT : 0 < T)
    (gam : B → ℝ) (hgam : gam = gibbsState E (1 / (k * T)))
    (dyn : Equiv.Perm (Bool × B)) (r1 : Bool × B → ℝ)
    (hr1 : ∀ x, r1 x = (1 / 2 : ℝ) * gam (dyn.symm x).2)
    (Q : ℝ) (hQ : Q = ∑ b, (marg2 r1 b - gam b) * E b) :
    k * T * (Real.log 2 - shannonEntropy (marg1 r1)) ≤ Q := by
  set r0 : Bool × B → ℝ := fun x => (1 / 2 : ℝ) * gam x.2 with hr0_def
  have hgamP : IsProbDist gam := by rw [hgam]; exact gibbsState_isProbDist E (1 / (k * T))
  have hr0P : IsProbDist r0 := by
    refine ⟨fun x => mul_nonneg (by norm_num) (hgamP.nonneg x.2), ?_⟩
    rw [hr0_def, Fintype.sum_prod_type]
    simp only [← Finset.mul_sum, hgamP.sum_one, mul_one]
    rw [Fintype.sum_bool]; norm_num
  have hr1_eq : r1 = fun x => r0 (dyn.symm x) := funext hr1
  have hr1P : IsProbDist r1 := by
    refine ⟨fun x => by rw [hr1_eq]; exact hr0P.nonneg _, ?_⟩
    rw [hr1_eq, ← hr0P.sum_one]
    exact dyn.symm.sum_comp r0
  have hsecond : shannonEntropy r0 ≤ shannonEntropy r1 := by
    rw [hr1_eq, shannonEntropy_comp_equiv dyn.symm r0]
  exact heat_ge_entropy_decrease E k T hk hT gam hgam r0 r1 (fun _ => rfl) hr1P hsecond Q hQ

/-! ### Non-vacuity

The hypotheses of `landauer_principle` are satisfiable: a memory bit really can be erased
into a sufficiently cold four-state bath without decreasing the joint entropy. -/

/-- Energies of the witness bath: one ground state and three states of energy `10`. -/
