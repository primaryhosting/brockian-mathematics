/-!
# Box Level 5
Category: Quantum Physics
Target: QPhys.box_level_5
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

/-
This file must literally *begin* with the header comment above, so it cannot contain any
`import` command (Lean requires imports to be the very first commands of a file).  It is
therefore written against the Lean core prelude only, with the numeric parameters taken in
`Rat`.  The companion file `RequestProject/Main.lean` develops the same statement over `ℝ`
with `Real.pi` and the reduced Planck constant (`QPhys.box_level_5_real`).
-/

namespace QPhys

/-! ### Small arithmetic helpers (core `Rat` only) -/


theorem boxEnergyReal_one_ne_zero {hbar m L : ℝ} (hhbar : hbar ≠ 0) (hm : m ≠ 0) (hL : L ≠ 0) :
    boxEnergyReal hbar m L 1 ≠ 0 := by
  have hpi : Real.pi ≠ 0 := Real.pi_ne_zero
  unfold boxEnergyReal
  push_cast
  rw [one_pow, one_mul]
  exact div_ne_zero (mul_ne_zero (pow_ne_zero 2 hpi) (pow_ne_zero 2 hhbar))
    (mul_ne_zero (mul_ne_zero two_ne_zero hm) (pow_ne_zero 2 hL))

/-- **Box level 5, over the reals.**  For the one-dimensional infinite square well the ratio of
the fifth energy level to the ground-state energy is `5² = 25`, independently of `ħ`, `m`, `L`. -/
