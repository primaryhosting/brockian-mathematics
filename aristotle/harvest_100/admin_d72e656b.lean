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

/-!
# The GHZ / Mermin paradox

We formalize the deterministic (all-or-nothing) Bell argument of Greenberger–Horne–Zeilinger,
in the form given by Mermin.

* Quantum side: the three–qubit GHZ state
  `|GHZ⟩ = (|000⟩ - |111⟩)/√2`
  is an eigenvector with eigenvalue `+1` of the observables `X⊗Y⊗Y`, `Y⊗X⊗Y`, `Y⊗Y⊗X`,
  and an eigenvector with eigenvalue `-1` of `X⊗X⊗X`.  Hence quantum mechanics predicts with
  certainty that the product of the three `±1` outcomes is `+1` in the first three experiments
  and `-1` in the last one.

* Local hidden variable side: a deterministic local model assigns, for a fixed value of the
  hidden variable, a value `v i s ∈ {+1,-1}` to the measurement of setting `s` (`false` = `X`,
  `true` = `Y`) at site `i`, independently of what is measured at the other two sites, and the
  outcome of a joint measurement is the product of the local values.  No such assignment can
  reproduce the four quantum predictions.

The final statement `QC.ghz_nonlocal` bundles both halves.
-/

namespace QC

open Matrix
open scoped Kronecker

/-- The Pauli `X` matrix. -/
def pauliX : Matrix (Fin 2) (Fin 2) ℂ := !![0, 1; 1, 0]

/-- The Pauli `Y` matrix. -/
noncomputable def pauliY : Matrix (Fin 2) (Fin 2) ℂ := !![0, -Complex.I; Complex.I, 0]

/-- The three–fold Kronecker (tensor) product of one–qubit operators, acting on the
`8`-dimensional space indexed by `(Fin 2 × Fin 2) × Fin 2`. -/
def kron3 (A B C : Matrix (Fin 2) (Fin 2) ℂ) :
    Matrix ((Fin 2 × Fin 2) × Fin 2) ((Fin 2 × Fin 2) × Fin 2) ℂ := A ⊗ₖ B ⊗ₖ C

/-- The (normalized) GHZ state `(|000⟩ - |111⟩)/√2`, as a vector of amplitudes indexed by the
computational basis of three qubits. -/
noncomputable def ghz : ((Fin 2 × Fin 2) × Fin 2) → ℂ :=
  fun v => if v = ((0, 0), 0) then (Real.sqrt 2 : ℝ)⁻¹
           else if v = ((1, 1), 1) then -((Real.sqrt 2 : ℝ)⁻¹) else 0

/-- The GHZ state is a unit vector. -/
theorem ghz_norm_sq : ∑ i, ‖ghz i‖ ^ 2 = 1 := by
  simp [ghz, Fintype.sum_prod_type, Fin.sum_univ_succ, Complex.norm_real]
  norm_num

theorem ghz_ne_zero : ghz ≠ 0 := by
  intro h
  have := ghz_norm_sq
  rw [h] at this
  simp at this

/-- Quantum prediction: `X⊗Y⊗Y` has the GHZ state as a `+1` eigenvector. -/
theorem xyy_ghz : (kron3 pauliX pauliY pauliY).mulVec ghz = ghz := by
  funext i
  fin_cases i <;>
    simp [kron3, Matrix.mulVec, dotProduct, Fin.sum_univ_succ, pauliX, pauliY, ghz,
      Fintype.sum_prod_type]

/-- Quantum prediction: `Y⊗X⊗Y` has the GHZ state as a `+1` eigenvector. -/
theorem yxy_ghz : (kron3 pauliY pauliX pauliY).mulVec ghz = ghz := by
  funext i
  fin_cases i <;>
    simp [kron3, Matrix.mulVec, dotProduct, Fin.sum_univ_succ, pauliX, pauliY, ghz,
      Fintype.sum_prod_type]

/-- Quantum prediction: `Y⊗Y⊗X` has the GHZ state as a `+1` eigenvector. -/
theorem yyx_ghz : (kron3 pauliY pauliY pauliX).mulVec ghz = ghz := by
  funext i
  fin_cases i <;>
    simp [kron3, Matrix.mulVec, dotProduct, Fin.sum_univ_succ, pauliX, pauliY, ghz,
      Fintype.sum_prod_type]

/-- Quantum prediction: `X⊗X⊗X` has the GHZ state as a `-1` eigenvector. -/
theorem xxx_ghz : (kron3 pauliX pauliX pauliX).mulVec ghz = -ghz := by
  funext i
  fin_cases i <;>
    simp [kron3, Matrix.mulVec, dotProduct, Fin.sum_univ_succ, pauliX, ghz,
      Fintype.sum_prod_type]

/-- A deterministic local hidden variable assignment: `v i s` is the `±1` value that site
`i : Fin 3` would return if the setting `s` (`false` for `X`, `true` for `Y`) were measured
there.  The value does not depend on the settings chosen at the other sites (locality), and it
is fixed in advance (determinism). -/
def IsLHV (v : Fin 3 → Bool → ℝ) : Prop := ∀ i s, v i s = 1 ∨ v i s = -1

/-- The four deterministic quantum predictions, expressed for a hidden variable assignment:
the product of the three local outcomes equals `+1` for the `XYY`, `YXY`, `YYX` experiments and
`-1` for the `XXX` experiment. -/
def MerminPredictions (v : Fin 3 → Bool → ℝ) : Prop :=
  v 0 false * v 1 true * v 2 true = 1 ∧
  v 0 true * v 1 false * v 2 true = 1 ∧
  v 0 true * v 1 true * v 2 false = 1 ∧
  v 0 false * v 1 false * v 2 false = -1

theorem sq_eq_one_of_lhv {v : Fin 3 → Bool → ℝ} (hv : IsLHV v) (i : Fin 3) (s : Bool) :
    v i s * v i s = 1 := by
  rcases hv i s with h | h <;> rw [h] <;> norm_num

/-- **Mermin's contradiction.** No deterministic local hidden variable assignment reproduces the
four GHZ predictions. -/
theorem no_lhv (v : Fin 3 → Bool → ℝ) (hv : IsLHV v) : ¬ MerminPredictions v := by
  rintro ⟨h1, h2, h3, h4⟩
  have e0 := sq_eq_one_of_lhv hv 0 true
  have e1 := sq_eq_one_of_lhv hv 1 true
  have e2 := sq_eq_one_of_lhv hv 2 true
  have key : (v 0 false * v 1 true * v 2 true) * (v 0 true * v 1 false * v 2 true) *
      (v 0 true * v 1 true * v 2 false)
      = (v 0 false * v 1 false * v 2 false) *
        ((v 0 true * v 0 true) * (v 1 true * v 1 true) * (v 2 true * v 2 true)) := by ring
  rw [h1, h2, h3, h4, e0, e1, e2] at key
  norm_num at key

/-- **The GHZ / Mermin paradox.**  The three–qubit GHZ state is a `+1` eigenvector of
`X⊗Y⊗Y`, `Y⊗X⊗Y` and `Y⊗Y⊗X` and a `-1` eigenvector of `X⊗X⊗X`, so quantum mechanics predicts
these four joint measurement outcomes with certainty; yet no deterministic local hidden variable
assignment of `±1` values to the local observables can reproduce all four predictions. -/
theorem ghz_nonlocal :
    ghz ≠ 0 ∧
    (kron3 pauliX pauliY pauliY).mulVec ghz = ghz ∧
    (kron3 pauliY pauliX pauliY).mulVec ghz = ghz ∧
    (kron3 pauliY pauliY pauliX).mulVec ghz = ghz ∧
    (kron3 pauliX pauliX pauliX).mulVec ghz = -ghz ∧
    ∀ v : Fin 3 → Bool → ℝ, IsLHV v → ¬ MerminPredictions v :=
  ⟨ghz_ne_zero, xyy_ghz, yxy_ghz, yyx_ghz, xxx_ghz, no_lhv⟩

end QC

