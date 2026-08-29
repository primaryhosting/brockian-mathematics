import Mathlib
/-!
# Goodstein Terminates
Category: Frontier — Set Theory
Target: Frontier.Goodstein_terminates
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

set_option grind.warning false

namespace Frontier

open Ordinal

/-! ### Arithmetic preliminaries -/


theorem Goodstein_terminates (n : ℕ) : ∃ k : ℕ, goodstein n k = 0 := by
  by_contra hcon
  push_neg at hcon
  set f : ℕ → Ordinal := fun k => Gv (k + 2) Ordinal.omega0 (goodstein n k) with hf
  have step : ∀ k : ℕ, f (k + 1) < f k := by
    intro k
    have hgk : goodstein n k ≠ 0 := hcon k
    have hxne : bump (k + 2) (k + 3) (goodstein n k) ≠ 0 :=
      bump_ne_zero _ _ _ (by omega) hgk
    have hlt : bump (k + 2) (k + 3) (goodstein n k) - 1
        < bump (k + 2) (k + 3) (goodstein n k) := by omega
    have hwk : ((k + 3 : ℕ) : Ordinal) ≤ Ordinal.omega0 := le_of_lt (Ordinal.nat_lt_omega0 _)
    calc f (k + 1)
        = Gv (k + 3) Ordinal.omega0 (bump (k + 2) (k + 3) (goodstein n k) - 1) := rfl
      _ < Gv (k + 3) Ordinal.omega0 (bump (k + 2) (k + 3) (goodstein n k)) :=
          Gv_strictMono (k + 3) Ordinal.omega0 (by omega) hwk hlt
      _ = Gv (k + 2) Ordinal.omega0 (goodstein n k) :=
          Gv_bump (k + 2) (k + 3) Ordinal.omega0 (by omega) (by omega) _
      _ = f k := rfl
  obtain ⟨a, ha, hmin⟩ := Ordinal.lt_wf.has_min (Set.range f) ⟨f 0, 0, rfl⟩
  obtain ⟨k, rfl⟩ := ha
  exact hmin (f (k + 1)) ⟨k + 1, rfl⟩ (step k)

/-! ### Sanity checks

These confirm that the definitions really implement the Goodstein process:
bumping the base of `4 = 2 ^ 2` from `2` to `3` gives `27 = 3 ^ 3`, the Goodstein
sequence starting at `3` is `3, 3, 3, 2, 1, 0`, and the one starting at `4` begins
`4, 26, 41, 60, ...`.
-/

example : bump 2 3 4 = 27 := by norm_num [bump_def]

example : goodstein 3 5 = 0 := by norm_num [goodstein, bump_def]

example : goodstein 4 3 = 60 := by norm_num [goodstein, bump_def]

end Frontier

