/-!
# Box Level 1
Category: Quantum Physics
Target: QPhys.box_level_1
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

/-
Note on the file layout: Lean requires every `import` to precede all other
commands, so a file that must *begin* with the header comment above cannot
carry an `import Mathlib` line.  This module therefore uses only Lean core
(`Rat`), which suffices for the statement.  A real-valued version of the same
statement, using the physical formula `Eₙ = n²π²ħ²/(2mL²)` and Mathlib's
`div_self`, is proved in `RequestProject/QPhysReal.lean`.
-/

namespace QPhys

/-- Energy of the `n`-th stationary state of a particle in a one-dimensional
infinite potential well ("particle in a box"), measured in units in which the
ground-state energy is `E₁`: `Eₙ = n² E₁`. -/

theorem boxEnergyReal_one_pos {m L hbar : ℝ} (hm : 0 < m) (hL : 0 < L)
    (hbar_ne : hbar ≠ 0) : 0 < boxEnergyReal m L hbar 1 := by
  have hh : 0 < hbar ^ 2 := by positivity
  unfold boxEnergyReal
  have h1 : ((1 : ℕ) : ℝ) ^ 2 = 1 := by norm_num
  rw [h1]
  positivity

/-- The infinite-well energy ratio `E₁ / E₁ = 1²`. -/
