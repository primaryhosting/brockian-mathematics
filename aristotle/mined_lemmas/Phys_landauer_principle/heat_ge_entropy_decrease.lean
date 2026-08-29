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

theorem heat_ge_entropy_decrease {B : Type*} [Fintype B] [Nonempty B]
    (E : B → ℝ) (k T : ℝ) (hk : 0 < k) (hT : 0 < T)
    (gam : B → ℝ) (hgam : gam = gibbsState E (1 / (k * T)))
    (r0 r1 : Bool × B → ℝ)
    (hr0 : ∀ x, r0 x = (1 / 2 : ℝ) * gam x.2)
    (hr1P : IsProbDist r1)
    (hsecond : shannonEntropy r0 ≤ shannonEntropy r1)
    (Q : ℝ) (hQ : Q = ∑ b, (marg2 r1 b - gam b) * E b) :
    k * T * (Real.log 2 - shannonEntropy (marg1 r1)) ≤ Q := by
  set beta : ℝ := 1 / (k * T) with hbeta_def
  have hkT : 0 < k * T := mul_pos hk hT
  have hpS : IsProbDist (fun _ : Bool => (1 : ℝ) / 2) := by
    refine ⟨fun _ => by norm_num, ?_⟩
    rw [Fintype.sum_bool]; norm_num
  have hgamP : IsProbDist gam := by rw [hgam]; exact gibbsState_isProbDist E beta
  -- the initial joint distribution is the product of the uniform bit and the Gibbs state
  have hr0_eq : r0 = fun x : Bool × B => (fun _ : Bool => (1 : ℝ) / 2) x.1 * gam x.2 := funext hr0
  have hH0 : shannonEntropy r0 = Real.log 2 + shannonEntropy gam := by
    rw [hr0_eq, shannonEntropy_prod _ _ hpS hgamP, shannonEntropy_uniform_bool]
  -- subadditivity of the joint entropy
  have hsub := shannonEntropy_subadditive r1 hr1P
  -- maximum-entropy property of the Gibbs state, applied to the final bath state
  have hmax := entropy_le_of_isProbDist E beta (marg2 r1) (marg2_isProbDist hr1P)
  -- the initial bath state is the Gibbs state
  have hHgam : shannonEntropy gam = beta * (∑ b, gam b * E b) + Real.log (partitionFn E beta) := by
    rw [hgam]; exact entropy_gibbsState E beta
  have hQ' : Q = (∑ b, marg2 r1 b * E b) - ∑ b, gam b * E b := by
    rw [hQ]
    simp only [sub_mul]
    rw [Finset.sum_sub_distrib]
  have hkey : Real.log 2 - shannonEntropy (marg1 r1) ≤ beta * Q := by
    rw [hH0, hHgam] at hsecond
    rw [hQ', mul_sub]
    linarith [hsecond, hsub, hmax]
  have hmul : k * T * (Real.log 2 - shannonEntropy (marg1 r1)) ≤ k * T * (beta * Q) :=
    mul_le_mul_of_nonneg_left hkey (le_of_lt hkT)
  have hbq : k * T * (beta * Q) = Q := by
    rw [hbeta_def]; field_simp
  linarith [hmul, hbq.le, hbq.ge]

/-- **Landauer's principle.**

If a one-bit memory, initially in the uniform state and uncorrelated with a heat bath which
is in its Gibbs state at temperature `T`, is *erased* (its final marginal state is the point
mass at `s₀`) by a process during which the joint entropy of memory and bath does not
decrease, then the heat `Q` absorbed by the bath is at least `k T log 2`. -/
