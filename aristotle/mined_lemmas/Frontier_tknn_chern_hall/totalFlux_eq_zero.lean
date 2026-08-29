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
