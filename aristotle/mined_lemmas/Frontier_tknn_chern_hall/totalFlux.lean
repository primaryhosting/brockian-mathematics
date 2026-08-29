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

def totalFlux (Ax Ay : ℤ → ℤ → ℝ) (N : ℕ) : ℝ :=
  ∑ i ∈ range N, ∑ j ∈ range N, plaquetteFlux Ax Ay i j

/-- Discrete Berry curvature: the plaquette flux with the `2π`-phase ambiguity
`n i j` of the link variables removed (principal branch). -/
