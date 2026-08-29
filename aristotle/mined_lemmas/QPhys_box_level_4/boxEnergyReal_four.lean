/-!
# Box Level 4
Category: Quantum Physics
Target: QPhys.box_level_4
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace QPhys

/-- Energy levels of a particle of mass `m` in a one-dimensional infinite
potential well ("particle in a box") of width `L`:

`E n = n² π² ħ² / (2 m L²)`,

where `pi2` denotes `π²`.  (This file carries the required header comment at
the very top, which Lean does not allow to be followed by `import`, so the
arithmetic is carried out in the exact rational field `Rat`, which is
available without any imports.  A version over the real numbers, with the
genuine `Real.pi` and no rational stand-in, is proved in
`RequestProject/BoxLevel4Real.lean`.) -/

theorem boxEnergyReal_four (hbar m L : ℝ) :
    boxEnergyReal hbar m L 4 = (4 : ℝ) ^ 2 * boxEnergyReal hbar m L 1 := by
  unfold boxEnergyReal
  push_cast
  ring

/-- The infinite-well energy ratio `E₄ / E₁ = 4²`. -/
