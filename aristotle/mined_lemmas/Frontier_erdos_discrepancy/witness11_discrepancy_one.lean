/-!
# Erdos Discrepancy
Category: Frontier — Prime Numbers
Target: Frontier.erdos_discrepancy
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

/-
This file is written in plain Lean 4 core (no imports), so that the header comment above
can legally be the very first thing in the file.
-/

namespace Frontier

/-- A `±1` sequence: `f n ∈ {1, -1}` for every index `n ≥ 1`. -/

theorem witness11_discrepancy_one :
    ∀ d n : Nat, 1 ≤ d → 1 ≤ n → n * d ≤ 11 → (hapSum witness11 d n).natAbs ≤ 1 := by
  intro d n hd hn hnd
  exact witness11_discrepancy_one_bounded d (by
      have : d ≤ n * d := Nat.le_mul_of_pos_left d hn
      omega) n (by
      have : n ≤ n * d := Nat.le_mul_of_pos_right n hd
      omega) hd hn hnd

end Frontier

import Mathlib
import RequestProject.ErdosDiscrepancy

/-!
# A Lean-checked reduction for the Erdős discrepancy problem

The statement `Frontier.ErdosDiscrepancyStatement` quantifies over all `±1` sequences on
`ℕ`.  Here we check, by a compactness argument on the Cantor space `ℕ → Bool`, that it is
*equivalent* to the family of finitary statements

  for every `C` there is `N` such that every `±1` sequence admits a homogeneous
  arithmetic progression inside `{1, …, N}` with partial sum exceeding `C`.

This is the standard reduction of the Erdős discrepancy problem to a sequence of finite
(in principle mechanically checkable) problems; the case `C = 1`, with `N = 12`, is proved
in `RequestProject/ErdosDiscrepancy.lean`.
-/

namespace Frontier

/-- The finitary form of the Erdős discrepancy statement: for each bound `C` there is a
uniform length `N` inside which every `±1` sequence already exhibits discrepancy `> C`. -/
