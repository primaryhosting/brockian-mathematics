/-!
# Tknn Chern Hall
Category: Frontier Physics
Target: Frontier.tknn_chern_hall
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

open scoped Real
open Finset

namespace Frontier

/-- The representative of an angle `x` modulo `2π` obtained by subtracting the nearest
multiple of `2π`.  This is the "principal branch" of the logarithm of `exp (i x)`. -/
noncomputable def redAngle (x : ℝ) : ℝ := x - 2 * Real.pi * (round (x / (2 * Real.pi)) : ℤ)

lemma redAngle_eq (x : ℝ) :
    redAngle x = x - 2 * Real.pi * (round (x / (2 * Real.pi)) : ℤ) := rfl

variable {N M : ℕ}

/-- The discrete (lattice) Berry curvature of a `U(1)` gauge field on the Brillouin torus.

The Brillouin zone is discretized as `ZMod N × ZMod M`; `A1` and `A2` are the Berry phases
(link angles) of the occupied Bloch state along the two lattice directions.  The curvature of
a plaquette is the total phase picked up going around it, reduced to the principal branch —
this is the Fukui–Hatsugai–Suzuki lattice field strength. -/
noncomputable def berryCurvature (A1 A2 : ZMod N × ZMod M → ℝ) (k : ZMod N × ZMod M) : ℝ :=
  redAngle (A1 k + A2 (k.1 + 1, k.2) - A1 (k.1, k.2 + 1) - A2 k)

/-- The (first) Chern number of the occupied band: the total Berry curvature over the
Brillouin torus, divided by `2π`. -/
noncomputable def chernNumber [NeZero N] [NeZero M] (A1 A2 : ZMod N × ZMod M → ℝ) : ℝ :=
  (1 / (2 * Real.pi)) * ∑ k : ZMod N × ZMod M, berryCurvature A1 A2 k

/-- The zero-temperature Hall conductance predicted by the Kubo formula (TKNN):
the Chern number of the filled band times the conductance quantum `e²/h`. -/
noncomputable def hallConductance [NeZero N] [NeZero M]
    (A1 A2 : ZMod N × ZMod M → ℝ) (e h : ℝ) : ℝ :=
  chernNumber A1 A2 * (e ^ 2 / h)

/-- The unreduced plaquette phases sum to zero over the whole torus: every link occurs once
with each sign.  (This is the discrete Stokes theorem on a closed surface.) -/
lemma sum_plaquette_raw [NeZero N] [NeZero M] (A1 A2 : ZMod N × ZMod M → ℝ) :
    ∑ k : ZMod N × ZMod M,
      (A1 k + A2 (k.1 + 1, k.2) - A1 (k.1, k.2 + 1) - A2 k) = 0 := by
  have h1 : ∑ k : ZMod N × ZMod M, A1 (k.1, k.2 + 1) = ∑ k : ZMod N × ZMod M, A1 k := by
    refine Fintype.sum_equiv
      ((Equiv.refl (ZMod N)).prodCongr (Equiv.addRight (1 : ZMod M))) _ _ ?_
    intro k
    rfl
  have h2 : ∑ k : ZMod N × ZMod M, A2 (k.1 + 1, k.2) = ∑ k : ZMod N × ZMod M, A2 k := by
    refine Fintype.sum_equiv
      ((Equiv.addRight (1 : ZMod N)).prodCongr (Equiv.refl (ZMod M))) _ _ ?_
    intro k
    rfl
  simp only [Finset.sum_sub_distrib, Finset.sum_add_distrib, h1, h2]
  ring

/-- **Integrality of the lattice Chern number.**  The total Berry curvature over the
Brillouin torus is an integer multiple of `2π`. -/
theorem sum_berryCurvature_eq [NeZero N] [NeZero M] (A1 A2 : ZMod N × ZMod M → ℝ) :
    ∃ C : ℤ, ∑ k : ZMod N × ZMod M, berryCurvature A1 A2 k = 2 * Real.pi * (C : ℝ) := by
  classical
  refine ⟨- ∑ k : ZMod N × ZMod M,
    round ((A1 k + A2 (k.1 + 1, k.2) - A1 (k.1, k.2 + 1) - A2 k) / (2 * Real.pi)), ?_⟩
  have hraw := sum_plaquette_raw A1 A2
  simp only [berryCurvature, redAngle_eq]
  rw [Finset.sum_sub_distrib, hraw, ← Finset.mul_sum]
  push_cast
  ring

/-- **TKNN (Thouless–Kohmoto–Nightingale–den Nijs).**

For any `U(1)` Berry connection on a discretized Brillouin torus, the Chern number of the
filled band is an integer, and the Hall conductance is exactly that integer times the
conductance quantum `e²/h`. -/
theorem tknn_chern_hall [NeZero N] [NeZero M]
    (A1 A2 : ZMod N × ZMod M → ℝ) (e h : ℝ) :
    ∃ C : ℤ, chernNumber A1 A2 = (C : ℝ) ∧
      hallConductance A1 A2 e h = (C : ℝ) * (e ^ 2 / h) := by
  obtain ⟨C, hC⟩ := sum_berryCurvature_eq A1 A2
  have hpi : (2 : ℝ) * Real.pi ≠ 0 := by positivity
  have hchern : chernNumber A1 A2 = (C : ℝ) := by
    rw [chernNumber, hC]
    field_simp
  exact ⟨C, hchern, by rw [hallConductance, hchern]⟩

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

