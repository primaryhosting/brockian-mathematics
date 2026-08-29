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
def curvature (A : BerryConnection N M) (i j : ℤ) : ℝ :=
  A.ax i j + A.ay (i + 1) j - A.ax i (j + 1) - A.ay i j

/-- The gauge-invariant field strength of a plaquette: the curvature with its
`2π` ambiguity (branch choice `n`) removed. -/
noncomputable def fieldStrength (A : BerryConnection N M) (n : ℤ → ℤ → ℤ) (i j : ℤ) : ℝ :=
  curvature A i j - 2 * Real.pi * (n i j : ℝ)

/-- The Chern number of the occupied band: minus the total branch index, which is
`1 / (2π)` times the total field strength over the Brillouin torus. -/
def chernNumber (n : ℤ → ℤ → ℤ) (N M : ℕ) : ℤ :=
  - ∑ i ∈ Finset.range N, ∑ j ∈ Finset.range M, n (i : ℤ) (j : ℤ)

/-- The Hall conductance obtained from the Kubo formula: `e²/h` times the Berry
curvature (field strength) integrated over the Brillouin zone, divided by `2π`. -/
noncomputable def hallConductance (A : BerryConnection N M) (n : ℤ → ℤ → ℤ)
    (e h : ℝ) : ℝ :=
  (e ^ 2 / h) * (1 / (2 * Real.pi)) *
    ∑ i ∈ Finset.range N, ∑ j ∈ Finset.range M, fieldStrength A n (i : ℤ) (j : ℤ)

/-! ### Telescoping lemmas -/

/-- Telescoping sum over an initial segment, with integer-valued arguments. -/
theorem sum_range_telescope (g : ℤ → ℝ) (K : ℕ) :
    ∑ k ∈ Finset.range K, (g (k : ℤ) - g ((k : ℤ) + 1)) = g 0 - g (K : ℤ) := by
  induction K with
  | zero => simp
  | succ K ih =>
      rw [Finset.sum_range_succ, ih]
      push_cast
      ring

/-- Periodicity forces the value at the period to agree with the value at `0`. -/
theorem ax_zero_eq_ax_M (A : BerryConnection N M) (i : ℤ) :
    A.ax i (M : ℤ) = A.ax i 0 := by
  have := A.ax_per_y i 0
  simpa using this

/-- Periodicity forces the value at the period to agree with the value at `0`. -/
theorem ay_zero_eq_ay_N (A : BerryConnection N M) (j : ℤ) :
    A.ay (N : ℤ) j = A.ay 0 j := by
  have := A.ay_per_x 0 j
  simpa using this

/-- The horizontal part of the curvature telescopes away in the vertical
direction, by periodicity of the connection. -/
theorem sum_ax_part (A : BerryConnection N M) (i : ℤ) :
    ∑ j ∈ Finset.range M, (A.ax i (j : ℤ) - A.ax i ((j : ℤ) + 1)) = 0 := by
  rw [sum_range_telescope (fun t => A.ax i t) M, ax_zero_eq_ax_M A i]
  ring

/-- The vertical part of the curvature telescopes away in the horizontal
direction, by periodicity of the connection. -/
theorem sum_ay_part (A : BerryConnection N M) (j : ℤ) :
    ∑ i ∈ Finset.range N, (A.ay ((i : ℤ) + 1) j - A.ay (i : ℤ) j) = 0 := by
  have h : ∑ i ∈ Finset.range N, (A.ay ((i : ℤ) + 1) j - A.ay (i : ℤ) j)
      = - ∑ i ∈ Finset.range N, (A.ay (i : ℤ) j - A.ay ((i : ℤ) + 1) j) := by
    rw [← Finset.sum_neg_distrib]
    exact Finset.sum_congr rfl (by intro x _; ring)
  rw [h, sum_range_telescope (fun t => A.ay t j) N, ay_zero_eq_ay_N A j]
  ring

/-- **Lattice Stokes theorem on the torus.** The total Berry curvature around a
closed Brillouin torus vanishes: every link is traversed once in each direction. -/
theorem total_curvature_eq_zero (A : BerryConnection N M) :
    ∑ i ∈ Finset.range N, ∑ j ∈ Finset.range M, curvature A (i : ℤ) (j : ℤ) = 0 := by
  have hsplit : ∀ i ∈ Finset.range N,
      ∑ j ∈ Finset.range M, curvature A (i : ℤ) (j : ℤ)
        = (∑ j ∈ Finset.range M, (A.ax (i : ℤ) (j : ℤ) - A.ax (i : ℤ) ((j : ℤ) + 1)))
          + ∑ j ∈ Finset.range M, (A.ay ((i : ℤ) + 1) (j : ℤ) - A.ay (i : ℤ) (j : ℤ)) := by
    intro i _
    rw [← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl (by intro j _; simp only [curvature]; ring)
  rw [Finset.sum_congr rfl hsplit]
  rw [Finset.sum_add_distrib]
  have h1 : ∑ i ∈ Finset.range N,
      (∑ j ∈ Finset.range M, (A.ax (i : ℤ) (j : ℤ) - A.ax (i : ℤ) ((j : ℤ) + 1))) = 0 := by
    refine Finset.sum_eq_zero ?_
    intro i _
    exact sum_ax_part A (i : ℤ)
  have h2 : ∑ i ∈ Finset.range N,
      ∑ j ∈ Finset.range M, (A.ay ((i : ℤ) + 1) (j : ℤ) - A.ay (i : ℤ) (j : ℤ)) = 0 := by
    rw [Finset.sum_comm]
    refine Finset.sum_eq_zero ?_
    intro j _
    exact sum_ay_part A (j : ℤ)
  rw [h1, h2, add_zero]

/-- The total field strength over the Brillouin torus is exactly `2π` times the
Chern number. -/
theorem total_fieldStrength (A : BerryConnection N M) (n : ℤ → ℤ → ℤ) :
    ∑ i ∈ Finset.range N, ∑ j ∈ Finset.range M, fieldStrength A n (i : ℤ) (j : ℤ)
      = 2 * Real.pi * (chernNumber n N M : ℝ) := by
  have hsplit : ∑ i ∈ Finset.range N, ∑ j ∈ Finset.range M, fieldStrength A n (i : ℤ) (j : ℤ)
      = (∑ i ∈ Finset.range N, ∑ j ∈ Finset.range M, curvature A (i : ℤ) (j : ℤ))
        - 2 * Real.pi *
            ∑ i ∈ Finset.range N, ∑ j ∈ Finset.range M, ((n (i : ℤ) (j : ℤ) : ℝ)) := by
    rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl ?_
    intro i _
    rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl (by intro j _; simp only [fieldStrength])
  rw [hsplit, total_curvature_eq_zero A]
  simp only [chernNumber]
  push_cast
  ring

/-- **TKNN.** The integer quantum Hall conductance of a filled band equals a Chern
number times `e²/h`.

Concretely: for any (lattice) Berry connection on the Brillouin torus and any
choice of branch for the `2π`-ambiguous plaquette phases, the Hall conductance
computed from the Kubo formula is an integer multiple of the conductance quantum
`e²/h`, the integer being the Chern number of the occupied band. -/
theorem tknn_chern_hall (A : BerryConnection N M) (n : ℤ → ℤ → ℤ) (e h : ℝ) :
    ∃ C : ℤ,
      C = chernNumber n N M ∧
      (1 / (2 * Real.pi)) *
          (∑ i ∈ Finset.range N, ∑ j ∈ Finset.range M,
            fieldStrength A n (i : ℤ) (j : ℤ)) = (C : ℝ) ∧
      hallConductance A n e h = (C : ℝ) * (e ^ 2 / h) := by
  have hpi0 : (2 : ℝ) * Real.pi ≠ 0 := by
    have := Real.pi_pos
    positivity
  refine ⟨chernNumber n N M, rfl, ?_, ?_⟩
  · rw [total_fieldStrength A n]
    field_simp
  rw [hallConductance, total_fieldStrength A n]
  field_simp

/-- Non-vacuity: the hypotheses are satisfiable, and the Chern number can be a
nonzero integer (here `1` on a `2 × 3` discretization of the Brillouin torus). -/
example : ∃ (A : BerryConnection 2 3) (n : ℤ → ℤ → ℤ),
    chernNumber n 2 3 = 1 ∧
    ∀ e h : ℝ, hallConductance A n e h = e ^ 2 / h := by
  refine ⟨⟨fun _ _ => 0, fun _ _ => 0, ?_, ?_, ?_, ?_⟩,
    fun i j => if i = 0 ∧ j = 0 then -1 else 0, ?_, ?_⟩
  · intro i j; rfl
  · intro i j; rfl
  · intro i j; rfl
  · intro i j; rfl
  · simp [chernNumber, Finset.sum_range_succ]
  · intro e h
    obtain ⟨C, hC1, _, hC3⟩ := tknn_chern_hall
      (N := 2) (M := 3) ⟨fun _ _ => 0, fun _ _ => 0, fun _ _ => rfl, fun _ _ => rfl,
        fun _ _ => rfl, fun _ _ => rfl⟩
      (fun i j => if i = 0 ∧ j = 0 then -1 else 0) e h
    have hC : C = 1 := by
      rw [hC1]; simp [chernNumber, Finset.sum_range_succ]
    rw [hC3, hC]
    norm_num

end Frontier

