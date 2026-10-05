/-!
# Bkt Transition
Category: Frontier Phys
Target: Phys.bkt_transition
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

namespace Phys

open Filter Topology

/-- Energy cost of a single vortex of core size `a` in a 2D XY model of linear size `L`
with spin stiffness `J`: `E = π J log (L / a)`. -/
noncomputable def vortexEnergy (J L a : ℝ) : ℝ := Real.pi * J * Real.log (L / a)

/-- Configurational entropy of a single vortex: the vortex core can be placed in roughly
`(L / a) ^ 2` positions, giving `S = 2 log (L / a)` (in units with `k_B = 1`). -/
noncomputable def vortexEntropy (L a : ℝ) : ℝ := 2 * Real.log (L / a)

/-- Free energy of a single vortex at temperature `T`: `F = E - T S`. -/
noncomputable def vortexFreeEnergy (J T L a : ℝ) : ℝ :=
    vortexEnergy J L a - T * vortexEntropy L a

/-- The Berezinskii–Kosterlitz–Thouless transition temperature `T_BKT = π J / 2`
(in units with `k_B = 1`). -/
noncomputable def bktTemp (J : ℝ) : ℝ := Real.pi * J / 2

lemma vortexFreeEnergy_eq (J T L a : ℝ) :
    vortexFreeEnergy J T L a = 2 * (bktTemp J - T) * Real.log (L / a) := by
  unfold vortexFreeEnergy vortexEnergy vortexEntropy bktTemp
  ring

lemma log_div_pos {L a : ℝ} (ha : 0 < a) (hL : a < L) : 0 < Real.log (L / a) :=
  Real.log_pos ((one_lt_div ha).2 hL)

lemma tendsto_log_div_atTop {a : ℝ} (ha : 0 < a) :
    Tendsto (fun L : ℝ => Real.log (L / a)) atTop atTop :=
  Real.tendsto_log_atTop.comp (tendsto_id.atTop_div_const ha)

/--
**Berezinskii–Kosterlitz–Thouless topological phase transition of the 2D XY model.**

In the Kosterlitz–Thouless vortex-unbinding picture, a single free vortex in a system of
linear size `L` and core size `a` costs energy `π J log (L/a)` and gains entropy
`2 log (L/a)`, so its free energy is `F(T, L) = (π J - 2 T) log (L/a)`.

There is a sharp critical temperature `T_BKT = π J / 2` separating two phases:

* **Low temperature (`T < T_BKT`), bound-vortex / quasi–long-range-ordered phase:**
  the free energy of an isolated vortex is strictly positive and diverges to `+∞` in the
  thermodynamic limit `L → ∞`; free vortices are suppressed and appear only in
  vortex–antivortex pairs.
* **High temperature (`T > T_BKT`), disordered plasma phase:**
  the free energy of an isolated vortex is strictly negative and diverges to `-∞` as
  `L → ∞`; vortices proliferate, destroying quasi-long-range order.
* **At `T = T_BKT`:** energy and entropy exactly balance, `F ≡ 0` for every system size,
  which is what makes the transition a genuine, size-independent threshold.
-/
theorem bkt_transition (J a : ℝ) (hJ : 0 < J) (ha : 0 < a) :
    (∀ T : ℝ, T < bktTemp J →
        (∀ L : ℝ, a < L → 0 < vortexFreeEnergy J T L a) ∧
        Tendsto (fun L : ℝ => vortexFreeEnergy J T L a) atTop atTop) ∧
    (∀ T : ℝ, bktTemp J < T →
        (∀ L : ℝ, a < L → vortexFreeEnergy J T L a < 0) ∧
        Tendsto (fun L : ℝ => vortexFreeEnergy J T L a) atTop atBot) ∧
    (∀ L : ℝ, vortexFreeEnergy J (bktTemp J) L a = 0) ∧
    0 < bktTemp J := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro T hT
    have hc : 0 < 2 * (bktTemp J - T) := by linarith
    constructor
    · intro L hL
      rw [vortexFreeEnergy_eq]
      exact mul_pos hc (log_div_pos ha hL)
    · simp only [vortexFreeEnergy_eq]
      exact (tendsto_log_div_atTop ha).const_mul_atTop hc
  · intro T hT
    have hc : 2 * (bktTemp J - T) < 0 := by linarith
    constructor
    · intro L hL
      rw [vortexFreeEnergy_eq]
      exact mul_neg_of_neg_of_pos hc (log_div_pos ha hL)
    · simp only [vortexFreeEnergy_eq]
      exact (tendsto_log_div_atTop ha).const_mul_atBot_of_neg hc
  · intro L
    rw [vortexFreeEnergy_eq]
    ring
  · have := Real.pi_pos
    unfold bktTemp
    positivity

end Phys

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

