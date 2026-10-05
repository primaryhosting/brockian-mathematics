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
