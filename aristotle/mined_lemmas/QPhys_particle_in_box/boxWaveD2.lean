import Mathlib

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

set_option pp.fullNames true
set_option pp.structureInstances true
set_option pp.coercions.types true
set_option pp.funBinderTypes true
set_option pp.letVarTypes true
set_option pp.piBinderTypes true

set_option grind.warning false

namespace QPhys

/-- The `n`-th energy level of a particle of mass `m` in an infinite square well of width `L`:
`E_n = n² π² ℏ² / (2 m L²)`. -/

noncomputable def boxWaveD2 (L : ℝ) (n : ℕ) : ℝ → ℝ :=
  fun x => -(Real.sqrt (2 / L) * ((n : ℝ) * Real.pi / L) ^ 2 *
    Real.sin ((n : ℝ) * Real.pi / L * x))

/-- `psi` is a bound state of energy `E` for a particle of mass `m` in the infinite square well
`[0, L]`: it is twice differentiable on `ℝ` (with derivatives `psi'` and `psi''`), it satisfies
the time-independent Schrödinger equation `-(ℏ²/2m) ψ'' = E ψ`, it vanishes at the walls of the
well, and it is not identically zero inside the well. -/
structure IsBoxEigenstate (hbar m L E : ℝ) (psi psi' psi'' : ℝ → ℝ) : Prop where
  hasDerivAt_psi : ∀ x : ℝ, HasDerivAt psi (psi' x) x
  hasDerivAt_psi' : ∀ x : ℝ, HasDerivAt psi' (psi'' x) x
  schrodinger : ∀ x : ℝ, -(hbar ^ 2 / (2 * m)) * psi'' x = E * psi x
  wall_left : psi 0 = 0
  wall_right : psi L = 0
  nontrivial : ∃ x ∈ Set.Icc (0 : ℝ) L, psi x ≠ 0

/-- `boxWaveD1 L n` is the derivative of `boxWave L n`. -/
