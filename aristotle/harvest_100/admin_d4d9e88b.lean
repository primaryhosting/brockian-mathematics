import Mathlib

/-!
# Tknn Chern Hall
Category: Frontier Physics
Target: Frontier.tknn_chern_hall
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace Frontier

open Finset

/-!
## Setting

We work with the lattice (Fukui–Hatsugai) formulation of the TKNN theorem on a
discretized Brillouin torus with `N × N` plaquettes.

A Bloch band over the Brillouin torus is described by a discrete Berry connection:
real link phases `Ax i j` (link from `(i,j)` to `(i,j+1)` direction of the second
momentum coordinate) and `Ay i j` (link in the first momentum coordinate).
The *plaquette flux* is the oriented sum of the connection around an elementary
plaquette.  The physical Berry curvature is the plaquette flux reduced to its
principal branch, i.e. with a multiple `2π * n i j` of the phase ambiguity of the
link variables removed; the integers `n i j` are the vortex numbers of the gauge.

The Chern number is `(1/2π)` times the total Berry curvature, and the TKNN
theorem states that the Hall conductance is this Chern number times `e²/h`.
The key mathematical content is that the total plaquette flux over a torus
telescopes to zero, hence the total Berry curvature is exactly `2π` times an
integer, i.e. the Chern number is quantized.
-/

/-- Oriented flux of the discrete Berry connection through the elementary
plaquette with lower left corner `(i, j)`. -/
def plaquetteFlux (Ax Ay : ℤ → ℤ → ℝ) (i j : ℤ) : ℝ :=
  Ax i j + Ay (i + 1) j - Ax i (j + 1) - Ay i j

/-- The total plaquette flux over the `N × N` discretized Brillouin torus. -/
def totalFlux (Ax Ay : ℤ → ℤ → ℝ) (N : ℕ) : ℝ :=
  ∑ i ∈ range N, ∑ j ∈ range N, plaquetteFlux Ax Ay i j

/-- Discrete Berry curvature: the plaquette flux with the `2π`-phase ambiguity
`n i j` of the link variables removed (principal branch). -/
noncomputable def berryCurvature (Ax Ay : ℤ → ℤ → ℝ) (n : ℤ → ℤ → ℤ) (i j : ℤ) : ℝ :=
  plaquetteFlux Ax Ay i j - 2 * Real.pi * (n i j : ℝ)

/-- The total Berry curvature over the `N × N` discretized Brillouin torus. -/
noncomputable def totalCurvature (Ax Ay : ℤ → ℤ → ℝ) (n : ℤ → ℤ → ℤ) (N : ℕ) : ℝ :=
  ∑ i ∈ range N, ∑ j ∈ range N, berryCurvature Ax Ay n i j

/-- The (integer) Chern number of the band, read off from the vortex numbers of
the gauge. -/
def chernNumber (n : ℤ → ℤ → ℤ) (N : ℕ) : ℤ :=
  -∑ i ∈ range N, ∑ j ∈ range N, n i j

/-- The Hall conductance, given by the Kubo formula as `e²/h` times `(1/2π)`
times the total Berry curvature of the filled band. -/
noncomputable def hallConductance (e h : ℝ) (Ax Ay : ℤ → ℤ → ℝ) (n : ℤ → ℤ → ℤ)
    (N : ℕ) : ℝ :=
  (e ^ 2 / h) * ((1 / (2 * Real.pi)) * totalCurvature Ax Ay n N)

/-- Telescoping in one direction, proved by induction on the number of links. -/
theorem sum_telescope (f : ℤ → ℝ) (N : ℕ) :
    ∑ j ∈ range N, (f j - f (j + 1)) = f 0 - f N := by
  induction N with
  | zero => simp
  | succ N ih =>
      rw [Finset.sum_range_succ, ih]
      push_cast
      ring

/-- On a torus the total plaquette flux vanishes: the discrete Berry connection
contributions cancel between neighbouring plaquettes and wrap around by
periodicity. -/
theorem totalFlux_eq_zero (Ax Ay : ℤ → ℤ → ℝ) (N : ℕ)
    (hAx : ∀ i j, Ax i (j + N) = Ax i j) (hAy : ∀ i j, Ay (i + N) j = Ay i j) :
    totalFlux Ax Ay N = 0 := by
  have hx : ∀ i : ℤ, ∑ j ∈ range N, (Ax i j - Ax i (j + 1)) = 0 := by
    intro i
    have hper : Ax i (N : ℤ) = Ax i 0 := by simpa using hAx i 0
    rw [sum_telescope (fun j => Ax i j) N, hper]
    ring
  have hy : ∀ j : ℤ, ∑ i ∈ range N, (Ay (i + 1) j - Ay i j) = 0 := by
    intro j
    have hper : Ay (N : ℤ) j = Ay 0 j := by simpa using hAy 0 j
    have h1 : ∑ i ∈ range N, (Ay ((i : ℤ)) j - Ay ((i : ℤ) + 1) j) = 0 := by
      rw [sum_telescope (fun i => Ay i j) N, hper]
      ring
    have h3 : ∑ i ∈ range N, (Ay ((i : ℤ) + 1) j - Ay ((i : ℤ)) j)
        = -∑ i ∈ range N, (Ay ((i : ℤ)) j - Ay ((i : ℤ) + 1) j) := by
      rw [← Finset.sum_neg_distrib]
      exact Finset.sum_congr rfl (fun i _ => by ring)
    rw [h3, h1, neg_zero]
  have hsplit : totalFlux Ax Ay N
      = (∑ i ∈ range N, ∑ j ∈ range N, (Ax i j - Ax i (j + 1)))
        + ∑ i ∈ range N, ∑ j ∈ range N, (Ay (i + 1) j - Ay i j) := by
    unfold totalFlux plaquetteFlux
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    rw [← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl (fun j _ => by ring)
  have h1 : ∑ i ∈ range N, ∑ j ∈ range N, (Ax (i : ℤ) j - Ax (i : ℤ) (j + 1)) = 0 :=
    Finset.sum_eq_zero (fun i _ => hx i)
  have h2 : ∑ i ∈ range N, ∑ j ∈ range N, (Ay ((i : ℤ) + 1) j - Ay (i : ℤ) j) = 0 := by
    rw [Finset.sum_comm]
    exact Finset.sum_eq_zero (fun j _ => hy j)
  rw [hsplit, h1, h2, add_zero]

/-- **Quantization of the Berry curvature.** The total Berry curvature over the
discretized Brillouin torus is exactly `2π` times the (integer) Chern number. -/
theorem totalCurvature_eq (Ax Ay : ℤ → ℤ → ℝ) (n : ℤ → ℤ → ℤ) (N : ℕ)
    (hAx : ∀ i j, Ax i (j + N) = Ax i j) (hAy : ∀ i j, Ay (i + N) j = Ay i j) :
    totalCurvature Ax Ay n N = 2 * Real.pi * (chernNumber n N : ℝ) := by
  have hsplit : totalCurvature Ax Ay n N
      = totalFlux Ax Ay N
        - 2 * Real.pi * ∑ i ∈ range N, ∑ j ∈ range N, ((n i j : ℝ)) := by
    unfold totalCurvature totalFlux berryCurvature
    rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
  rw [hsplit, totalFlux_eq_zero Ax Ay N hAx hAy, chernNumber]
  push_cast
  ring

/-- **TKNN theorem (lattice formulation).**
The integer quantum Hall conductance of a filled band equals its Chern number
times `e²/h`. -/
theorem tknn_chern_hall (e h : ℝ) (Ax Ay : ℤ → ℤ → ℝ) (n : ℤ → ℤ → ℤ) (N : ℕ)
    (hAx : ∀ i j, Ax i (j + N) = Ax i j) (hAy : ∀ i j, Ay (i + N) j = Ay i j) :
    hallConductance e h Ax Ay n N = (chernNumber n N : ℝ) * (e ^ 2 / h) := by
  rw [hallConductance, totalCurvature_eq Ax Ay n N hAx hAy]
  field_simp

/-- A sanity check that the setting is non-degenerate: a gauge with a single
vortex on a one-plaquette torus carries Chern number `1`, and then the Hall
conductance is exactly one conductance quantum `e²/h`. -/
example (e h : ℝ) : hallConductance e h (fun _ _ => 0) (fun _ _ => 0)
    (fun _ _ => -1) 1 = e ^ 2 / h := by
  have hchern : chernNumber (fun _ _ => -1) 1 = 1 := by decide
  rw [tknn_chern_hall e h _ _ _ 1 (fun _ _ => rfl) (fun _ _ => rfl), hchern]
  norm_num

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

