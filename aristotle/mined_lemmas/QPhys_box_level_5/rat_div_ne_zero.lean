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


theorem rat_div_ne_zero {a b : Rat} (ha : a ≠ 0) (hb : b ≠ 0) : a / b ≠ 0 := by
  rw [Rat.div_def]
  exact rat_mul_ne_zero ha (rat_inv_ne_zero hb)

/-! ### The infinite square well -/

/-- Energy levels of a particle of mass `m` in a one-dimensional infinite square well
("particle in a box") of width `L`, written with Planck's constant `h`:

`Eₙ = n² h² / (8 m L²)`.

(Equivalently `Eₙ = n² π² ħ² / (2 m L²)` with `ħ = h / (2π)`; see
`QPhys.box_level_5_real` in `RequestProject/Main.lean` for that form over `ℝ`.) -/
