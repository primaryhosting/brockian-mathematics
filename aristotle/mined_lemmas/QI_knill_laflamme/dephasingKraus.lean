/-
# Knill Laflamme
Category: Frontier Qi
Target: QI.knill_laflamme
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/
import Mathlib

/-!
# Knill Laflamme
Category: Frontier Qi
Target: QI.knill_laflamme
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open scoped BigOperators
open scoped Real
open scoped Nat
open scoped Classical
open scoped Pointwise
open scoped ComplexOrder

set_option maxHeartbeats 8000000
set_option maxRecDepth 4000
set_option synthInstance.maxHeartbeats 400000
set_option synthInstance.maxSize 128

set_option relaxedAutoImplicit false
set_option autoImplicit false

set_option grind.warning false

namespace QI

open Matrix

variable {n m : ℕ}

/-! ## Definitions -/

/-- `P` is (the matrix of) an orthogonal projection onto a nonzero code subspace. -/
structure IsCode (P : Matrix (Fin n) (Fin n) ℂ) : Prop where
  herm : Pᴴ = P
  idem : P * P = P
  ne_zero : P ≠ 0

/-- The Knill–Laflamme conditions for a code with projection `P` and error operators `E`:
there is a matrix of scalars `c` with `P Eₐ† E_b P = c a b • P`. -/

noncomputable def dephasingKraus : Fin 2 → Matrix (Fin 2) (Fin 2) ℂ :=
  fun a => diagonal (fun i => if i = a then 1 else 0)

/-- The full two-dimensional space is not a code correcting the dephasing channel:
the Knill–Laflamme conditions fail, hence by `knill_laflamme` so does correctability. -/
example : ¬ CorrectsErrors (1 : Matrix (Fin 2) (Fin 2) ℂ) dephasingKraus := by
  have hE : ∑ a, (dephasingKraus a)ᴴ * dephasingKraus a = 1 := by
    simp [dephasingKraus, Matrix.diagonal_conjTranspose, Fin.sum_univ_two]
    ext i j
    fin_cases i <;> fin_cases j <;> simp
  rw [knill_laflamme (1 : Matrix (Fin 2) (Fin 2) ℂ) _ ⟨by simp, by simp, one_ne_zero⟩ hE]
  rintro ⟨c, hc⟩
  have h := hc 0 0
  have h1 := congrFun (congrFun h 0) 0
  have h2 := congrFun (congrFun h 1) 1
  simp [dephasingKraus, Matrix.diagonal_conjTranspose] at h1 h2
  rw [← h1] at h2
  exact zero_ne_one h2

end QI

