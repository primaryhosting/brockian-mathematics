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


theorem rat_mul_ne_zero {a b : Rat} (ha : a ≠ 0) (hb : b ≠ 0) : a * b ≠ 0 := by
  intro hab
  rcases Rat.mul_eq_zero.mp hab with h | h
  · exact ha h
  · exact hb h

