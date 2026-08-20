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


theorem box_level_5_real {hbar m L : ℝ} (hhbar : hbar ≠ 0) (hm : m ≠ 0) (hL : L ≠ 0) :
    boxEnergyReal hbar m L 5 / boxEnergyReal hbar m L 1 = (5 : ℝ) ^ 2 := by
  have hx : boxEnergyReal hbar m L 1 ≠ 0 := boxEnergyReal_one_ne_zero hhbar hm hL
  have h5 : boxEnergyReal hbar m L 5 = (5 : ℝ) ^ 2 * boxEnergyReal hbar m L 1 := by
    unfold boxEnergyReal
    push_cast
    ring
  rw [h5, mul_div_assoc, div_self hx, mul_one]

end QPhys

