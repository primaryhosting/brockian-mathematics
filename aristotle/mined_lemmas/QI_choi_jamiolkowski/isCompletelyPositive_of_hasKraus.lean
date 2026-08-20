/-
# Choi Jamiolkowski
Category: Frontier Qi
Target: QI.choi_jamiolkowski
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Choi Jamiolkowski
Category: Frontier Qi
Target: QI.choi_jamiolkowski
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open Matrix
open scoped ComplexOrder

namespace QI

variable {n m : Type} [Fintype n] [DecidableEq n] [Fintype m] [DecidableEq m]

/-- The Choi matrix of a linear map `Φ` between matrix algebras:
`C (i,a) (j,b) = (Φ Eᵢⱼ) a b`, where `Eᵢⱼ` is the matrix unit. -/

theorem isCompletelyPositive_of_hasKraus (Φ : Matrix n n ℂ →ₗ[ℂ] Matrix m m ℂ)
    (h : HasKraus Φ) : IsCompletelyPositive Φ := by
  classical
  obtain ⟨r, K, hK⟩ := h
  intro κ _ X hX
  rw [amplify_eq_sum_krausAmp Φ hK κ X]
  exact Matrix.posSemidef_sum _ fun k _ => hX.mul_mul_conjTranspose_same _

omit [Fintype m] [DecidableEq m] in
