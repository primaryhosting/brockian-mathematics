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

set_option pp.fullNames true
set_option pp.structureInstances true
set_option pp.coercions.types true
set_option pp.funBinderTypes true
set_option pp.letVarTypes true
set_option pp.piBinderTypes true

set_option grind.warning false

/-!
## Lieb–Thirring and stability of matter

The Lieb–Thirring kinetic energy inequality states that, for an antisymmetric `N`-particle
wave function in three dimensions with one-particle density `ρ`, the kinetic energy obeys

  `T ≥ K ∫ ρ(x) ^ (5/3) dx`

with a constant `K > 0` that is *independent of the particle number* `N`.  Stability of
matter is deduced from this by combining it with the electrostatic (one-body) energy
`- ∫ V ρ` via the Thomas–Fermi bound: the resulting energy functional is bounded below by
`- C(K) ∫ V ^ (5/2)`, again uniformly in `N`.

This file formalizes that deduction — the Lieb–Thirring ⇒ stability reduction — in a
discretized (quadrature) form, in which integrals are replaced by finite weighted sums
`∑ i ∈ s, w i * f i` with nonnegative weights `w`.  The Lieb–Thirring kinetic bound is a
hypothesis (`Frontier.LiebThirringKinetic`), and everything else is proved:

* `Frontier.thomas_fermi_pointwise`  : the pointwise Young/Thomas–Fermi inequality
  `V * t ≤ K * t ^ (5/3) + tfConst K * V ^ (5/2)`;
* `Frontier.thomas_fermi_pointwise_sharp` : the constant `tfConst K` in it is optimal;
* `Frontier.lieb_thirring_stability` : the resulting lower bound on the energy;
* `Frontier.lieb_thirring_stability_uniform_in_particle_number` : the same bound, stated
  for a density normalized to `N` particles, with a right-hand side that does not depend
  on `N` — this uniformity is the content of stability of matter.
-/

namespace Frontier

/-- The Thomas–Fermi constant associated with a Lieb–Thirring constant `K`:
`tfConst K = (2/5) * (3/5) ^ (3/2) * K ^ (-3/2)`.  It is the sharp constant in
`V * t ≤ K * t ^ (5/3) + tfConst K * V ^ (5/2)` (see `thomas_fermi_pointwise`), i.e.

  `min_{t ≥ 0} (K * t ^ (5/3) - V * t) = - tfConst K * V ^ (5/2)`. -/
noncomputable def tfConst (K : ℝ) : ℝ :=
  (2 / 5) * (3 / 5 : ℝ) ^ (3 / 2 : ℝ) * K ^ (-(3 / 2) : ℝ)

/-- The Lieb–Thirring kinetic energy inequality, in discretized form: the kinetic energy
`T` of a state with one-particle density `ρ` is at least `K * ∑ w i * ρ i ^ (5/3)`, the
constant `K` being independent of the number of particles. -/
def LiebThirringKinetic {ι : Type*} (K : ℝ) (s : Finset ι) (w ρ : ι → ℝ) (T : ℝ) : Prop :=
  K * ∑ i ∈ s, w i * ρ i ^ (5 / 3 : ℝ) ≤ T

/-- The energy of a state with kinetic energy `T` and one-particle density `ρ` in the
attractive one-body potential `-V`. -/
def energy {ι : Type*} (T : ℝ) (s : Finset ι) (w V ρ : ι → ℝ) : ℝ :=
  T - ∑ i ∈ s, w i * V i * ρ i

/-- **Pointwise Thomas–Fermi (Young) inequality.**  For `K > 0` and `t, V ≥ 0`,
`V * t ≤ K * t ^ (5/3) + tfConst K * V ^ (5/2)`; equivalently
`K * t ^ (5/3) - V * t ≥ - tfConst K * V ^ (5/2)`. -/
theorem thomas_fermi_pointwise (K t V : ℝ) (hK : 0 < K) (ht : 0 ≤ t) (hV : 0 ≤ V) :
    V * t ≤ K * t ^ (5 / 3 : ℝ) + tfConst K * V ^ (5 / 2 : ℝ) := by
  rw [tfConst]
  set a : ℝ := (5 * K / 3) ^ (3 / 5 : ℝ) with ha
  have hbase : (0 : ℝ) < 5 * K / 3 := by positivity
  have hapos : 0 < a := Real.rpow_pos_of_pos hbase _
  have hy : (5 / 3 : ℝ).HolderConjugate (5 / 2) := by
    rw [Real.holderConjugate_iff]; norm_num
  have h := Real.young_inequality (a * t) (V / a) hy
  rw [abs_of_nonneg (by positivity), abs_of_nonneg (by positivity)] at h
  have hmul : (a * t) * (V / a) = V * t := by field_simp
  rw [hmul, Real.mul_rpow hapos.le ht, Real.div_rpow hV hapos.le] at h
  have h1 : a ^ (5 / 3 : ℝ) = 5 * K / 3 := by
    rw [ha, ← Real.rpow_mul hbase.le]; norm_num
  have h2 : a ^ (5 / 2 : ℝ) = (5 / 3 : ℝ) ^ (3 / 2 : ℝ) * K ^ (3 / 2 : ℝ) := by
    rw [ha, ← Real.rpow_mul hbase.le]
    norm_num
    rw [show (5 * K / 3 : ℝ) = (5 / 3 : ℝ) * K by ring, Real.mul_rpow (by norm_num) hK.le]
  have h3 : (3 / 5 : ℝ) ^ (3 / 2 : ℝ) = ((5 / 3 : ℝ) ^ (3 / 2 : ℝ))⁻¹ := by
    rw [← Real.inv_rpow (by norm_num)]; norm_num
  have h4 : K ^ (-(3 / 2) : ℝ) = (K ^ (3 / 2 : ℝ))⁻¹ := Real.rpow_neg hK.le _
  rw [h1, h2] at h
  rw [h3, h4]
  have hK32 : (0 : ℝ) < K ^ (3 / 2 : ℝ) := Real.rpow_pos_of_pos hK _
  have h53 : (0 : ℝ) < (5 / 3 : ℝ) ^ (3 / 2 : ℝ) := Real.rpow_pos_of_pos (by norm_num) _
  calc V * t
      ≤ 5 * K / 3 * t ^ (5 / 3 : ℝ) / (5 / 3)
          + V ^ (5 / 2 : ℝ) / ((5 / 3 : ℝ) ^ (3 / 2 : ℝ) * K ^ (3 / 2 : ℝ)) / (5 / 2) := h
    _ = K * t ^ (5 / 3 : ℝ)
          + 2 / 5 * ((5 / 3 : ℝ) ^ (3 / 2 : ℝ))⁻¹ * (K ^ (3 / 2 : ℝ))⁻¹ * V ^ (5 / 2 : ℝ) := by
        field_simp

/-- **Sharpness of the Thomas–Fermi constant.**  The inequality
`thomas_fermi_pointwise` is an equality at `t = (3 * V / (5 * K)) ^ (3/2)`, so
`tfConst K` cannot be lowered. -/
theorem thomas_fermi_pointwise_sharp (K V : ℝ) (hK : 0 < K) (hV : 0 ≤ V) :
    ∃ t : ℝ, 0 ≤ t ∧ V * t = K * t ^ (5 / 3 : ℝ) + tfConst K * V ^ (5 / 2 : ℝ) := by
  rcases eq_or_lt_of_le hV with h0 | hVpos
  · refine ⟨0, le_rfl, ?_⟩
    simp [← h0, Real.zero_rpow, tfConst]
  refine ⟨(3 * V / (5 * K)) ^ (3 / 2 : ℝ), Real.rpow_nonneg (by positivity) _, ?_⟩
  set B : ℝ := 3 * V / (5 * K) with hB
  have hBpos : 0 < B := by rw [hB]; positivity
  have e1 : (B ^ (3 / 2 : ℝ)) ^ (5 / 3 : ℝ) = B ^ (5 / 2 : ℝ) := by
    rw [← Real.rpow_mul hBpos.le]; norm_num
  have e2 : B ^ (5 / 2 : ℝ) = B ^ (3 / 2 : ℝ) * B := by
    rw [show (5 / 2 : ℝ) = 3 / 2 + 1 by norm_num, Real.rpow_add hBpos, Real.rpow_one]
  have e3 : B ^ (3 / 2 : ℝ) = (3 / 5 : ℝ) ^ (3 / 2 : ℝ) * K ^ (-(3 / 2) : ℝ) * V ^ (3 / 2 : ℝ) := by
    rw [hB, show (3 * V / (5 * K) : ℝ) = (3 / 5 : ℝ) * V * K⁻¹ by field_simp,
      Real.mul_rpow (by positivity) (by positivity),
      Real.mul_rpow (by norm_num) hV,
      ← Real.rpow_neg_one K, ← Real.rpow_mul hK.le]
    ring_nf
  have e4 : V ^ (5 / 2 : ℝ) = V ^ (3 / 2 : ℝ) * V := by
    rw [show (5 / 2 : ℝ) = 3 / 2 + 1 by norm_num, Real.rpow_add hVpos, Real.rpow_one]
  rw [e1, e2, tfConst, e3, e4]
  have hKB : K * B = 3 * V / 5 := by rw [hB]; field_simp
  linear_combination
    (-((3 / 5 : ℝ) ^ (3 / 2 : ℝ) * K ^ (-(3 / 2) : ℝ) * V ^ (3 / 2 : ℝ))) * hKB

/-- **Stability from the Lieb–Thirring inequality.**  If the kinetic energy `T` of a state
with one-particle density `ρ` satisfies the Lieb–Thirring bound with constant `K > 0`, then
the total energy `T - ∑ w V ρ` in the attractive potential `-V` is bounded below by
`- tfConst K * ∑ w * V ^ (5/2)`.  The bound depends only on `K` and on the potential — not
on the state, and in particular not on the number of particles. -/
theorem lieb_thirring_stability {ι : Type*} (K : ℝ) (hK : 0 < K) (s : Finset ι)
    (w ρ V : ι → ℝ) (T : ℝ)
    (hw : ∀ i ∈ s, 0 ≤ w i) (hρ : ∀ i ∈ s, 0 ≤ ρ i) (hV : ∀ i ∈ s, 0 ≤ V i)
    (hT : LiebThirringKinetic K s w ρ T) :
    - tfConst K * ∑ i ∈ s, w i * V i ^ (5 / 2 : ℝ) ≤ energy T s w V ρ := by
  have key : ∑ i ∈ s, w i * V i * ρ i
      ≤ K * ∑ i ∈ s, w i * ρ i ^ (5 / 3 : ℝ)
        + tfConst K * ∑ i ∈ s, w i * V i ^ (5 / 2 : ℝ) := by
    rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
    refine Finset.sum_le_sum ?_
    intro i hi
    have hpt := thomas_fermi_pointwise K (ρ i) (V i) hK (hρ i hi) (hV i hi)
    have hwi := hw i hi
    calc w i * V i * ρ i = w i * (V i * ρ i) := by ring
      _ ≤ w i * (K * ρ i ^ (5 / 3 : ℝ) + tfConst K * V i ^ (5 / 2 : ℝ)) := by
          exact mul_le_mul_of_nonneg_left hpt hwi
      _ = K * (w i * ρ i ^ (5 / 3 : ℝ)) + tfConst K * (w i * V i ^ (5 / 2 : ℝ)) := by ring
  rw [energy]
  have hTle : K * ∑ i ∈ s, w i * ρ i ^ (5 / 3 : ℝ) ≤ T := hT
  linarith

/-- **Stability of matter is uniform in the particle number.**  There is a single constant
`C ≥ 0`, depending only on the Lieb–Thirring constant `K` and on the potential `V`, such
that for *every* particle number `N`, every `N`-particle density `ρ` (normalized by
`∑ w ρ = N`) and every kinetic energy `T` obeying the Lieb–Thirring bound, the energy is at
least `-C`.  The constant is quantified before `N`, which is exactly the uniformity in the
particle number that constitutes stability of matter. -/
theorem lieb_thirring_stability_uniform_in_particle_number {ι : Type*} (K : ℝ) (hK : 0 < K)
    (s : Finset ι) (w V : ι → ℝ)
    (hw : ∀ i ∈ s, 0 ≤ w i) (hV : ∀ i ∈ s, 0 ≤ V i) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (N : ℕ) (ρ : ι → ℝ) (T : ℝ), (∀ i ∈ s, 0 ≤ ρ i) →
      ∑ i ∈ s, w i * ρ i = (N : ℝ) → LiebThirringKinetic K s w ρ T →
      -C ≤ energy T s w V ρ := by
  refine ⟨tfConst K * ∑ i ∈ s, w i * V i ^ (5 / 2 : ℝ), ?_, ?_⟩
  · have h1 : 0 ≤ tfConst K := by
      rw [tfConst]
      positivity
    have h2 : 0 ≤ ∑ i ∈ s, w i * V i ^ (5 / 2 : ℝ) :=
      Finset.sum_nonneg fun i hi => mul_nonneg (hw i hi) (Real.rpow_nonneg (hV i hi) _)
    exact mul_nonneg h1 h2
  · intro _ ρ T hρ _ hT
    have := lieb_thirring_stability K hK s w ρ V T hw hρ hV hT
    linarith [this]

/-- **The stability bound is attained**, hence non-vacuous and sharp: for the one-site
system with unit weight and unit potential there is a density `ρ` and a kinetic energy `T`
saturating both the Lieb–Thirring hypothesis and the conclusion of
`lieb_thirring_stability`. -/
theorem lieb_thirring_stability_attained (K : ℝ) (hK : 0 < K) :
    ∃ (ρ : Unit → ℝ) (T : ℝ), (∀ i ∈ ({()} : Finset Unit), 0 ≤ ρ i) ∧
      LiebThirringKinetic K {()} (fun _ => 1) ρ T ∧
      energy T {()} (fun _ => 1) (fun _ => 1) ρ
        = - tfConst K * ∑ _i ∈ ({()} : Finset Unit), (1 : ℝ) * (1 : ℝ) ^ (5 / 2 : ℝ) := by
  obtain ⟨t, ht0, ht⟩ := thomas_fermi_pointwise_sharp K 1 hK zero_le_one
  refine ⟨fun _ => t, K * t ^ (5 / 3 : ℝ), fun _ _ => ht0, ?_, ?_⟩
  · simp [LiebThirringKinetic]
  · simp only [energy, Finset.sum_singleton, Real.one_rpow, one_mul, mul_one] at *
    linarith

end Frontier

