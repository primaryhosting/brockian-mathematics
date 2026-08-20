/-
# Lieb Thirring Stability
Category: Frontier Physics
Target: Frontier.lieb_thirring_stability
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Lieb Thirring Stability
Category: Frontier Physics
Target: Frontier.lieb_thirring_stability
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

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

set_option pp.fullNames false
set_option pp.structureInstances true
set_option pp.coercions.types false
set_option pp.funBinderTypes true
set_option pp.letVarTypes true
set_option pp.piBinderTypes true

set_option grind.warning false

namespace Frontier

open MeasureTheory

/-!
## Setting

We work in three-dimensional configuration space.  A many-body fermionic state is
described here by the two quantities that enter the Lieb–Thirring argument:

* its total kinetic energy `T = ⟨Ψ, (-Δ₁ - ⋯ - Δ_N) Ψ⟩`,
* its one-body density `ρ`, normalised by `∫ ρ = N`.

The deep analytic input of the theory — the Lieb–Thirring inequality at `γ = 1` in
dimension `3` — is recorded as the predicate `LiebThirringBound`.  It is stated in
its *variational* form, which is the form in which it is used, and which is
equivalent to the eigenvalue-sum formulation by the min–max principle: for every
external potential `V`, the energy of the state in `-Δ + V` is bounded below by
`- L ∫ V₋^{5/2}`.

Everything below this input is proved here:

* `legendre_pointwise` — the pointwise Legendre/Young inequality, obtained from
  Mathlib's `Real.young_inequality` for the Hölder-conjugate pair `(5/2, 5/3)`;
* `kinetic_energy_bound` — the duality passage to the Thomas–Fermi-type kinetic
  energy inequality `T ≥ K_L ∫ ρ^{5/3}`, with the explicit constant
  `K_L = (3/5)(2/(5L))^{2/3}`;
* `liebThirringBound_of_kinetic` — the converse, showing that the two forms are in
  fact equivalent (so the hypothesis is not vacuous);
* `integral_rpow_four_thirds_le` — the Hölder interpolation
  `∫ ρ^{4/3} ≤ (∫ρ)^{1/2} (∫ρ^{5/3})^{1/2}`, obtained from Mathlib's
  `MeasureTheory.integral_mul_le_Lp_mul_Lq_of_nonneg`;
* `lieb_thirring_stability` — stability of matter of the second kind,
  `E ≥ -C·(N + K)`.
-/

/-- Configuration space of a single particle: three-dimensional Euclidean space. -/
abbrev Space : Type := EuclideanSpace ℝ (Fin 3)

/-- The negative part `V₋ = max (-V) 0` of a potential (a nonnegative function). -/

theorem kinetic_energy_bound {L T : ℝ} {ρ : Space → ℝ} (hL : 0 < L)
    (hρ0 : ∀ x, 0 ≤ ρ x) (hint53 : Integrable (fun x => ρ x ^ ((5 : ℝ) / 3)))
    (hLT : LiebThirringBound L T ρ) :
    ltKineticConst L * ∫ x, ρ x ^ ((5 : ℝ) / 3) ≤ T := by
  have hApos : (0:ℝ) < 2 / (5 * L) := by positivity
  set A : ℝ := 2 / (5 * L) with hA
  set c : ℝ := A ^ ((2 : ℝ) / 3) with hc
  have hcpos : 0 < c := Real.rpow_pos_of_pos hApos _
  set V : Space → ℝ := fun x => -(c * ρ x ^ ((2 : ℝ) / 3)) with hV
  have hnp : ∀ x, potNegPart V x = c * ρ x ^ ((2 : ℝ) / 3) := by
    intro x
    show max (-(V x)) 0 = _
    simp only [hV, neg_neg]
    exact max_eq_left (mul_nonneg hcpos.le (Real.rpow_nonneg (hρ0 x) _))
  have hB : ∀ x, potNegPart V x * ρ x = c * ρ x ^ ((5 : ℝ) / 3) := by
    intro x
    rw [hnp, mul_assoc]
    congr 1
    nth_rewrite 2 [← Real.rpow_one (ρ x)]
    rw [← Real.rpow_add' (hρ0 x) (by norm_num)]
    norm_num
  have hC : ∀ x, potNegPart V x ^ ((5 : ℝ) / 2)
      = c ^ ((5 : ℝ) / 2) * ρ x ^ ((5 : ℝ) / 3) := by
    intro x
    rw [hnp, Real.mul_rpow hcpos.le (Real.rpow_nonneg (hρ0 x) _),
      ← Real.rpow_mul (hρ0 x)]
    norm_num
  have hi1 : Integrable (fun x => potNegPart V x * ρ x) := by
    simp only [hB]; exact hint53.const_mul _
  have hi2 : Integrable (fun x => potNegPart V x ^ ((5 : ℝ) / 2)) := by
    simp only [hC]; exact hint53.const_mul _
  have key := hLT V hi1 hi2
  simp only [hB, hC, integral_const_mul] at key
  have hpow : c ^ ((5 : ℝ) / 2) = c * A := by
    have h1 : c ^ ((5 : ℝ) / 2) = A ^ ((5 : ℝ) / 3) := by
      rw [hc, ← Real.rpow_mul hApos.le]; norm_num
    rw [h1, show (5 : ℝ) / 3 = 2 / 3 + 1 by norm_num, Real.rpow_add hApos,
      Real.rpow_one, ← hc]
  rw [hpow] at key
  set S : ℝ := ∫ x, ρ x ^ ((5 : ℝ) / 3) with hSdef
  have hS : 0 ≤ S := integral_nonneg fun x => Real.rpow_nonneg (hρ0 x) _
  have hLA : L * A = 2 / 5 := by rw [hA]; field_simp
  have hrw : L * (c * A * S) = (2 / 5) * (c * S) := by
    have h : L * (c * A * S) = (L * A) * (c * S) := by ring
    rw [h, hLA]
  have hK : ltKineticConst L = (3 / 5) * c := rfl
  rw [hK]
  nlinarith [key, hrw]

/-- The converse of `kinetic_energy_bound`: the kinetic energy inequality with the
constant `K_L` implies back the Lieb–Thirring variational bound with constant `L`.

In particular the hypothesis `LiebThirringBound` is *not* vacuous: it holds for a
pair `(T, ρ)` exactly when the Thomas–Fermi bound `T ≥ K_L ∫ ρ^{5/3}` does. -/
