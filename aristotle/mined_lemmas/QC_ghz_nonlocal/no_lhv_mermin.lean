import Mathlib

/-!
# Ghz Nonlocal
Category: Quantum Computing
Target: QC.ghz_nonlocal
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open scoped BigOperators
open scoped Real
open scoped Nat
open scoped Classical
open scoped Pointwise
open Matrix

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

namespace QC

/-- Index type for the computational basis of three qubits. -/
abbrev Idx : Type := Fin 2 × Fin 2 × Fin 2

/-- The (unnormalised) 3-qubit GHZ state `|000⟩ + |111⟩`. -/

theorem no_lhv_mermin (L : LHV) :
    ¬ (L.a Setting.X * L.b Setting.Y * L.c Setting.Y = -1 ∧
       L.a Setting.Y * L.b Setting.X * L.c Setting.Y = -1 ∧
       L.a Setting.Y * L.b Setting.Y * L.c Setting.X = -1 ∧
       L.a Setting.X * L.b Setting.X * L.c Setting.X = 1) := by
  obtain ⟨a, b, c, ha, hb, hc⟩ := L
  rintro ⟨h1, h2, h3, h4⟩
  rcases ha Setting.X with hax | hax <;> rcases ha Setting.Y with hay | hay <;>
    rcases hb Setting.X with hbx | hbx <;> rcases hb Setting.Y with hby | hby <;>
    rcases hc Setting.X with hcx | hcx <;> rcases hc Setting.Y with hcy | hcy <;>
    simp only [hax, hay, hbx, hby, hcx, hcy] at h1 h2 h3 h4 <;> omega

/-- Sanity check: local hidden variable models do exist (the impossibility below is not
vacuous), and one can even satisfy any three of the four GHZ predictions. -/
example : ∃ L : LHV,
    L.a Setting.X * L.b Setting.Y * L.c Setting.Y = -1 ∧
    L.a Setting.Y * L.b Setting.X * L.c Setting.Y = -1 ∧
    L.a Setting.Y * L.b Setting.Y * L.c Setting.X = -1 := by
  refine ⟨⟨fun s => if s = Setting.X then -1 else 1, fun s => if s = Setting.X then -1 else 1,
    fun s => if s = Setting.X then -1 else 1,
    fun s => by cases s <;> simp, fun s => by cases s <;> simp,
    fun s => by cases s <;> simp⟩, ?_, ?_, ?_⟩ <;> simp

/--
**GHZ nonlocality (Mermin's paradox).**

The (unnormalised) three-qubit GHZ state `|000⟩ + |111⟩` is a nonzero simultaneous
eigenvector of the four commuting observables `X⊗Y⊗Y`, `Y⊗X⊗Y`, `Y⊗Y⊗X` (eigenvalue `-1`)
and `X⊗X⊗X` (eigenvalue `+1`); hence quantum mechanics predicts these four products of
outcomes with certainty.  Yet no deterministic local hidden variable assignment of
outcomes `±1` to the two possible settings of each party can reproduce all four
predictions simultaneously.
-/
