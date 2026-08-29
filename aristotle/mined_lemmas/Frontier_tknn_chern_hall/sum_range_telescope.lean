/-
# Tknn Chern Hall
Category: Frontier Physics
Target: Frontier.tknn_chern_hall
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Tknn Chern Hall
Category: Frontier Physics
Target: Frontier.tknn_chern_hall
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

namespace Frontier

/-!
## The TKNN (Thouless–Kohmoto–Nightingale–den Nijs) quantization

We work with the standard *lattice* (discretized Brillouin zone) formulation of the
TKNN argument, due to Fukui–Hatsugai–Suzuki.

The Brillouin zone is discretized as a torus with `N × M` plaquettes.  A choice of
smooth gauge for the occupied Bloch bundle produces a *Berry connection*: real link
variables `ax i j` (the Berry phase accumulated along the link from `(i,j)` to
`(i+1,j)`) and `ay i j` (from `(i,j)` to `(i,j+1)`), periodic in both directions
because the Bloch Hamiltonian is periodic on the Brillouin torus.

The Berry *curvature* of a plaquette is the oriented sum of the connection around
its boundary.  The physically meaningful field strength is this curvature taken
modulo `2π` (only `exp (i · phase)` is gauge invariant), i.e. `curvature - 2π * n i j`
for an integer branch assignment `n`.

The content of TKNN is: the Hall conductance is `e²/h` times the integral of the
Berry curvature over the Brillouin zone divided by `2π`, and *that number is an
integer* — the Chern number.  In the lattice formulation this is exactly the
statement that the raw curvature sums to zero around the torus (a telescoping /
Stokes argument), so the total field strength is `-2π` times the integer
`∑ n i j`.
-/

/-- A discrete (lattice) Berry connection on an `N × M` Brillouin torus.
`ax i j` is the Berry phase on the horizontal link out of the site `(i, j)` and
`ay i j` the phase on the vertical link out of `(i, j)`.  Both are periodic. -/
structure BerryConnection (N M : ℕ) where
  /-- Berry phase on the horizontal link from `(i, j)` to `(i+1, j)`. -/
  ax : ℤ → ℤ → ℝ
  /-- Berry phase on the vertical link from `(i, j)` to `(i, j+1)`. -/
  ay : ℤ → ℤ → ℝ
  /-- Periodicity of `ax` in the first (quasi-momentum) direction. -/
  ax_per_x : ∀ i j : ℤ, ax (i + (N : ℤ)) j = ax i j
  /-- Periodicity of `ax` in the second (quasi-momentum) direction. -/
  ax_per_y : ∀ i j : ℤ, ax i (j + (M : ℤ)) = ax i j
  /-- Periodicity of `ay` in the first (quasi-momentum) direction. -/
  ay_per_x : ∀ i j : ℤ, ay (i + (N : ℤ)) j = ay i j
  /-- Periodicity of `ay` in the second (quasi-momentum) direction. -/
  ay_per_y : ∀ i j : ℤ, ay i (j + (M : ℤ)) = ay i j

variable {N M : ℕ}

/-- The Berry curvature of the plaquette with lower-left corner `(i, j)`: the
oriented sum of the connection around the boundary of the plaquette. -/

theorem sum_range_telescope (g : ℤ → ℝ) (K : ℕ) :
    ∑ k ∈ Finset.range K, (g (k : ℤ) - g ((k : ℤ) + 1)) = g 0 - g (K : ℤ) := by
  induction K with
  | zero => simp
  | succ K ih =>
      rw [Finset.sum_range_succ, ih]
      push_cast
      ring

/-- Periodicity forces the value at the period to agree with the value at `0`. -/
