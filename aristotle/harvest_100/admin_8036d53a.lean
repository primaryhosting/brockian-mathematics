/-
# Bkt Transition
Category: Frontier Phys
Target: Phys.bkt_transition
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Bkt Transition
Category: Frontier Phys
Target: Phys.bkt_transition
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

namespace Phys

/-!
## The Berezinskii–Kosterlitz–Thouless transition of the 2D XY model

The BKT transition is the *topological* phase transition of the two–dimensional XY model
(planar rotators with nearest–neighbour coupling `J` on a two–dimensional lattice of spacing
`a`, confined to a box of linear size `L`).  Its mechanism is the *unbinding of vortices*,
and the transition temperature is located by the classical Kosterlitz–Thouless
*energy–entropy* balance:

* a single vortex of unit topological charge in a box of size `L` costs the elastic energy
  `E(L) = π J log (L / a)` (the spin–wave energy of the winding configuration, obtained by
  integrating `J/2 |∇θ|² = J/(2 r²)` over the annulus `a ≤ r ≤ L`);
* the vortex core can be placed at any of the `(L/a)²` lattice sites, so its entropy is
  `S(L) = k_B log ((L/a)²) = 2 k_B log (L / a)` (we work in units `k_B = 1`);
* hence the free energy of a single free vortex is
  `F(T, L) = E(L) - T S(L) = (π J - 2 T) log (L / a)`.

Below `T_BKT = π J / 2` the free energy of an isolated vortex is positive and *diverges*
with the system size, so vortices only occur in tightly bound neutral pairs: the system is
in the quasi–long–range–ordered (topologically ordered) phase.  Above `T_BKT` the free
energy of an isolated vortex is negative and diverges to `-∞`, so free vortices proliferate
and destroy the quasi–long–range order.  The temperature `T_BKT` is the unique temperature
at which this change of sign occurs; this is the content of `Phys.bkt_transition` below.
-/

/-- Elastic (spin–wave) energy of a single unit–charge vortex of core size `a`
in a two–dimensional box of linear size `L`, at coupling `J`. -/
noncomputable def vortexEnergy (J L a : ℝ) : ℝ := Real.pi * J * Real.log (L / a)

/-- Entropy of a single vortex core in a two–dimensional box of linear size `L`
with lattice spacing `a`: the core may sit at any of the `(L/a)²` sites (units `k_B = 1`). -/
noncomputable def vortexEntropy (L a : ℝ) : ℝ := 2 * Real.log (L / a)

/-- Free energy `E - T S` of a single free (unbound) vortex in the 2D XY model. -/
noncomputable def vortexFreeEnergy (J T L a : ℝ) : ℝ :=
  vortexEnergy J L a - T * vortexEntropy L a

/-- The Berezinskii–Kosterlitz–Thouless temperature `T_BKT = π J / 2` (units `k_B = 1`). -/
noncomputable def bktTemperature (J : ℝ) : ℝ := Real.pi * J / 2

lemma vortexFreeEnergy_eq (J T L a : ℝ) :
    vortexFreeEnergy J T L a = (Real.pi * J - 2 * T) * Real.log (L / a) := by
  unfold vortexFreeEnergy vortexEnergy vortexEntropy
  ring

lemma log_div_pos {L a : ℝ} (ha : 0 < a) (haL : a < L) : 0 < Real.log (L / a) :=
  Real.log_pos ((one_lt_div ha).mpr haL)

lemma bktTemperature_pos {J : ℝ} (hJ : 0 < J) : 0 < bktTemperature J := by
  unfold bktTemperature
  positivity

/-- Below `T_BKT` an isolated vortex has strictly positive free energy: vortices are bound. -/
lemma vortexFreeEnergy_pos_of_lt {J T L a : ℝ} (ha : 0 < a) (haL : a < L)
    (hT : T < bktTemperature J) : 0 < vortexFreeEnergy J T L a := by
  rw [vortexFreeEnergy_eq]
  have h1 : 0 < Real.pi * J - 2 * T := by
    unfold bktTemperature at hT; linarith
  exact mul_pos h1 (log_div_pos ha haL)

/-- Exactly at `T_BKT` the free energy of an isolated vortex vanishes. -/
lemma vortexFreeEnergy_eq_zero_at {J T L a : ℝ} (hT : T = bktTemperature J) :
    vortexFreeEnergy J T L a = 0 := by
  rw [vortexFreeEnergy_eq]
  unfold bktTemperature at hT
  rw [hT]
  ring_nf

/-- Above `T_BKT` an isolated vortex has strictly negative free energy: vortices unbind. -/
lemma vortexFreeEnergy_neg_of_gt {J T L a : ℝ} (ha : 0 < a) (haL : a < L)
    (hT : bktTemperature J < T) : vortexFreeEnergy J T L a < 0 := by
  rw [vortexFreeEnergy_eq]
  have h1 : Real.pi * J - 2 * T < 0 := by
    unfold bktTemperature at hT; linarith
  exact mul_neg_of_neg_of_pos h1 (log_div_pos ha haL)

lemma tendsto_log_div_atTop {a : ℝ} (ha : 0 < a) :
    Filter.Tendsto (fun L : ℝ => Real.log (L / a)) Filter.atTop Filter.atTop :=
  Real.tendsto_log_atTop.comp (Filter.tendsto_id.atTop_div_const ha)

/-- In the low–temperature phase the free energy of an isolated vortex diverges to `+∞`
with the system size: isolated vortices are suppressed in the thermodynamic limit. -/
lemma tendsto_vortexFreeEnergy_atTop {J T a : ℝ} (ha : 0 < a) (hT : T < bktTemperature J) :
    Filter.Tendsto (fun L : ℝ => vortexFreeEnergy J T L a) Filter.atTop Filter.atTop := by
  have h1 : 0 < Real.pi * J - 2 * T := by unfold bktTemperature at hT; linarith
  have := (tendsto_log_div_atTop ha).const_mul_atTop h1
  simpa [vortexFreeEnergy_eq] using this

/-- In the high–temperature phase the free energy of an isolated vortex diverges to `-∞`
with the system size: free vortices proliferate in the thermodynamic limit. -/
lemma tendsto_vortexFreeEnergy_atBot {J T a : ℝ} (ha : 0 < a) (hT : bktTemperature J < T) :
    Filter.Tendsto (fun L : ℝ => vortexFreeEnergy J T L a) Filter.atTop Filter.atBot := by
  have h1 : Real.pi * J - 2 * T < 0 := by unfold bktTemperature at hT; linarith
  have h2 := (tendsto_log_div_atTop ha).const_mul_atTop_of_neg h1
  simpa [vortexFreeEnergy_eq] using h2

/--
**The Berezinskii–Kosterlitz–Thouless topological phase transition of the 2D XY model.**

For every ferromagnetic coupling `J > 0` the two–dimensional XY model has a strictly
positive critical temperature `T_BKT = π J / 2` (in units `k_B = 1`) which is characterised
by the Kosterlitz–Thouless energy–entropy balance for a single topological defect
(a vortex of unit winding number) of core size `a` in a box of linear size `L > a`:

1. `T_BKT > 0`;
2. for `T < T_BKT` an isolated vortex has strictly positive free energy, at `T = T_BKT`
   it vanishes, and for `T > T_BKT` it is strictly negative;
3. in the low–temperature phase the free energy of an isolated vortex diverges to `+∞`
   in the thermodynamic limit `L → ∞`, so free vortices are entirely suppressed and only
   neutral bound pairs survive (quasi–long–range–ordered, topologically ordered phase);
4. in the high–temperature phase it diverges to `-∞`, so free vortices proliferate and
   destroy the quasi–long–range order (disordered phase);
5. `T_BKT` is the *unique* temperature at which this change of sign takes place.
-/
theorem bkt_transition (J : ℝ) (hJ : 0 < J) :
    0 < bktTemperature J ∧
    (∀ T L a : ℝ, 0 < a → a < L →
        (T < bktTemperature J → 0 < vortexFreeEnergy J T L a) ∧
        (T = bktTemperature J → vortexFreeEnergy J T L a = 0) ∧
        (bktTemperature J < T → vortexFreeEnergy J T L a < 0)) ∧
    (∀ T a : ℝ, 0 < a → T < bktTemperature J →
        Filter.Tendsto (fun L : ℝ => vortexFreeEnergy J T L a) Filter.atTop Filter.atTop) ∧
    (∀ T a : ℝ, 0 < a → bktTemperature J < T →
        Filter.Tendsto (fun L : ℝ => vortexFreeEnergy J T L a) Filter.atTop Filter.atBot) ∧
    (∀ Tc : ℝ,
        (∀ T L a : ℝ, 0 < a → a < L →
            (T < Tc → 0 < vortexFreeEnergy J T L a) ∧
            (Tc < T → vortexFreeEnergy J T L a < 0)) →
        Tc = bktTemperature J) := by
  refine ⟨bktTemperature_pos hJ, ?_, ?_, ?_, ?_⟩
  · intro T L a ha haL
    exact ⟨fun hT => vortexFreeEnergy_pos_of_lt ha haL hT,
      fun hT => vortexFreeEnergy_eq_zero_at hT,
      fun hT => vortexFreeEnergy_neg_of_gt ha haL hT⟩
  · intro T a ha hT
    exact tendsto_vortexFreeEnergy_atTop ha hT
  · intro T a ha hT
    exact tendsto_vortexFreeEnergy_atBot ha hT
  · intro Tc hTc
    by_contra hne
    rcases lt_or_gt_of_ne hne with h | h
    · -- `Tc < T_BKT` : pick `T` strictly in between; the two criteria disagree.
      obtain ⟨T, hT1, hT2⟩ := exists_between h
      have hpos : 0 < vortexFreeEnergy J T 2 1 := by
        exact vortexFreeEnergy_pos_of_lt (by norm_num) (by norm_num) hT2
      have hneg : vortexFreeEnergy J T 2 1 < 0 :=
        ((hTc T 2 1 (by norm_num) (by norm_num)).2) hT1
      linarith
    · -- `T_BKT < Tc` : symmetric contradiction.
      obtain ⟨T, hT1, hT2⟩ := exists_between h
      have hneg : vortexFreeEnergy J T 2 1 < 0 :=
        vortexFreeEnergy_neg_of_gt (by norm_num) (by norm_num) hT1
      have hpos : 0 < vortexFreeEnergy J T 2 1 :=
        ((hTc T 2 1 (by norm_num) (by norm_num)).1) hT2
      linarith

end Phys

