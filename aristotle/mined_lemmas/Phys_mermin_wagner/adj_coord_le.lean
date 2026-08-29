import Mathlib

/-!
# Core of the Mermin–Wagner argument

This file contains the model-independent part of the Mermin–Wagner theorem:
a finite collection of classical `O(2)` spins with an arbitrary nonnegative,
rotation-invariant pair interaction, plus arbitrary single-site terms
(boundary conditions / external fields).

The main result `Phys.abs_magnetization_le` bounds the magnetization at a
distinguished site `o` by the *Dirichlet energy* of any "spin wave" profile
`a : V → ℝ` which equals `π` at `o` and vanishes wherever a single-site term
is present.
-/

open MeasureTheory

noncomputable instance factTwoPi : Fact (0 < 2 * Real.pi) := ⟨by positivity⟩

/-- The state space of a single classical `O(2)` (planar rotator) spin. -/
abbrev Spin := AddCircle (2 * Real.pi)

namespace Phys

section Trig


theorem adj_coord_le {d : ℕ} {x y : Fin d → ℤ} (h : adj x y) (i : Fin d) :
    (x i - y i).natAbs ≤ 1 := by
  unfold adj at h
  calc (x i - y i).natAbs ≤ ∑ j, (x j - y j).natAbs :=
        Finset.single_le_sum (f := fun j => (x j - y j).natAbs) (fun _ _ => Nat.zero_le _)
          (Finset.mem_univ i)
    _ = 1 := h

