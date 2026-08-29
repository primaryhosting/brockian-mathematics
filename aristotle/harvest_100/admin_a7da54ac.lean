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
noncomputable def ghz : Idx → ℂ :=
  fun i => if i = (0, 0, 0) then 1 else if i = (1, 1, 1) then 1 else 0

/-- The Pauli `X` matrix. -/
def pauliX : Matrix (Fin 2) (Fin 2) ℂ := !![0, 1; 1, 0]

/-- The Pauli `Y` matrix. -/
noncomputable def pauliY : Matrix (Fin 2) (Fin 2) ℂ := !![0, -Complex.I; Complex.I, 0]

/-- The tensor product `A ⊗ B ⊗ C` of three single-qubit operators. -/
def op3 (A B C : Matrix (Fin 2) (Fin 2) ℂ) : Matrix Idx Idx ℂ :=
  fun i j => A i.1 j.1 * B i.2.1 j.2.1 * C i.2.2 j.2.2

/-- A setting is a choice of measurement direction for one party: `X` or `Y`. -/
inductive Setting : Type
  | X : Setting
  | Y : Setting
  deriving DecidableEq

end QC

namespace QC

lemma ghz_ne_zero : ghz ≠ 0 := by
  intro h
  have := congrFun h ((0 : Fin 2), (0 : Fin 2), (0 : Fin 2))
  simp [ghz] at this

private lemma mulVec_expand (M : Matrix Idx Idx ℂ) (i : Idx) :
    (M *ᵥ ghz) i = M i (0, 0, 0) + M i (1, 1, 1) := by
  simp only [Matrix.mulVec, dotProduct, ghz]
  rw [Fintype.sum_prod_type]
  simp [Fin.sum_univ_succ, Prod.ext_iff, Fintype.sum_prod_type]

/-- Quantum prediction: `X ⊗ Y ⊗ Y` has the GHZ state as eigenvector with eigenvalue `-1`. -/
theorem ghz_XYY : (op3 pauliX pauliY pauliY) *ᵥ ghz = -ghz := by
  funext i
  rw [mulVec_expand]
  fin_cases i <;>
    simp [op3, pauliX, pauliY, ghz, Complex.I_mul_I]

/-- Quantum prediction: `Y ⊗ X ⊗ Y` has the GHZ state as eigenvector with eigenvalue `-1`. -/
theorem ghz_YXY : (op3 pauliY pauliX pauliY) *ᵥ ghz = -ghz := by
  funext i
  rw [mulVec_expand]
  fin_cases i <;>
    simp [op3, pauliX, pauliY, ghz, Complex.I_mul_I]

/-- Quantum prediction: `Y ⊗ Y ⊗ X` has the GHZ state as eigenvector with eigenvalue `-1`. -/
theorem ghz_YYX : (op3 pauliY pauliY pauliX) *ᵥ ghz = -ghz := by
  funext i
  rw [mulVec_expand]
  fin_cases i <;>
    simp [op3, pauliX, pauliY, ghz, Complex.I_mul_I]

/-- Quantum prediction: `X ⊗ X ⊗ X` has the GHZ state as eigenvector with eigenvalue `+1`. -/
theorem ghz_XXX : (op3 pauliX pauliX pauliX) *ᵥ ghz = ghz := by
  funext i
  rw [mulVec_expand]
  fin_cases i <;>
    simp [op3, pauliX, ghz]

/--
A local hidden variable (deterministic) model for the three parties: each party `1, 2, 3`
assigns, for each of its two possible measurement settings, an outcome in `{-1, +1}`,
independently of the settings chosen by the other parties.
-/
structure LHV where
  a : Setting → ℤ
  b : Setting → ℤ
  c : Setting → ℤ
  ha : ∀ s, a s = 1 ∨ a s = -1
  hb : ∀ s, b s = 1 ∨ b s = -1
  hc : ∀ s, c s = 1 ∨ c s = -1

/-- The Mermin contradiction: no deterministic local hidden variable assignment can
reproduce the four GHZ product outcomes. -/
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
theorem ghz_nonlocal :
    (ghz ≠ 0 ∧
      (op3 pauliX pauliY pauliY) *ᵥ ghz = -ghz ∧
      (op3 pauliY pauliX pauliY) *ᵥ ghz = -ghz ∧
      (op3 pauliY pauliY pauliX) *ᵥ ghz = -ghz ∧
      (op3 pauliX pauliX pauliX) *ᵥ ghz = ghz) ∧
    ¬ ∃ L : LHV,
        L.a Setting.X * L.b Setting.Y * L.c Setting.Y = -1 ∧
        L.a Setting.Y * L.b Setting.X * L.c Setting.Y = -1 ∧
        L.a Setting.Y * L.b Setting.Y * L.c Setting.X = -1 ∧
        L.a Setting.X * L.b Setting.X * L.c Setting.X = 1 := by
  refine ⟨⟨ghz_ne_zero, ghz_XYY, ghz_YXY, ghz_YYX, ghz_XXX⟩, ?_⟩
  rintro ⟨L, h⟩
  exact no_lhv_mermin L h

end QC

