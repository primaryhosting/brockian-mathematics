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


theorem boxEnergy_one_ne_zero {h m L : Rat} (hh : h ≠ 0) (hm : m ≠ 0) (hL : L ≠ 0) :
    boxEnergy h m L 1 ≠ 0 := by
  have h8 : (8 : Rat) ≠ 0 := by decide
  unfold boxEnergy
  refine rat_div_ne_zero ?_ (rat_mul_ne_zero (rat_mul_ne_zero h8 hm) (rat_mul_ne_zero hL hL))
  rw [show ((1 : Nat) : Rat) = 1 from by decide, Rat.one_mul, Rat.one_mul]
  exact rat_mul_ne_zero hh hh

/-- **Box level 5.**  For a particle in a one-dimensional infinite square well, the ratio of the
fifth energy level to the ground-state energy equals `5² = 25`, independently of the mass `m`,
the width `L` and Planck's constant `h`. -/
