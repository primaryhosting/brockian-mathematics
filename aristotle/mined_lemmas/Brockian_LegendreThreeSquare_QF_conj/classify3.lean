import Mathlib

/-!
# Legendre's three-square theorem

A natural number `n` is a sum of three squares if and only if it is not of the
form `4 ^ a * (8 * b + 7)`.

The proof is self-contained (only core `Mathlib` is used).  The hard direction
goes through the classical route:

* Minkowski's convex body theorem shows that every positive definite integral
  ternary quadratic form of determinant one represents `1`, hence (by descent)
  is of the shape `Nᵀ * N`.
* Dirichlet's theorem on primes in arithmetic progressions together with
  quadratic reciprocity produces, for every `n` with `n % 4 ≠ 0` and
  `n % 8 ≠ 7`, an integer `m > 0` with `n ∣ m + 1` and `-n` a square modulo `m`.
  Out of these data one builds an explicit positive definite integral ternary
  form of determinant one whose `(0,0)` entry is `n`.
-/

namespace Brockian.LegendreThreeSquare

open Matrix MeasureTheory
open scoped ENNReal

/-! ## Integral quadratic forms -/

/-- The value at `v` of the quadratic form attached to the integer matrix `A`. -/

theorem classify3 (A : Matrix (Fin 3) (Fin 3) ℤ) (hsym : A.IsSymm) (hpos : PosDefZ A)
    (hdet : A.det = 1) : ∃ N : Matrix (Fin 3) (Fin 3) ℤ, A = Nᵀ * N := by
  obtain ⟨v, hv⟩ := exists_QF_eq_one3 A hsym hpos hdet
  have hwv : (A.mulVec v) ⬝ᵥ v = 1 := by
    rw [dotProduct_comm]; exact hv
  obtain ⟨U, hUdet, hUcol⟩ := exists_unimodular_col3 v (A.mulVec v) hwv
  set A1 := Uᵀ * A * U with hA1
  have hA1sym : A1.IsSymm := conj_isSymm A U hsym
  have hA1pos : PosDefZ A1 := conj_posDef A U hpos hUdet
  have h00 : A1 0 0 = 1 := by rw [hA1, conj_entry00_3 A U v hUcol]; exact hv
  obtain ⟨V, hVdet, hV⟩ := clear_first3 A1 hA1sym h00
  set W := U * V with hWdef
  have hWdet : W.det = 1 := by rw [hWdef, Matrix.det_mul, hUdet, hVdet, one_mul]
  set p := A1 1 1 - A1 0 1 ^ 2 with hp
  set q := A1 1 2 - A1 0 1 * A1 0 2 with hq
  set r := A1 2 2 - A1 0 2 ^ 2 with hr
  have hW : Wᵀ * A * W = !![1, 0, 0; 0, p, q; 0, q, r] := by
    have hexp : Wᵀ * A * W = Vᵀ * A1 * V := by
      rw [hWdef, hA1, Matrix.transpose_mul]
      simp [Matrix.mul_assoc]
    rw [hexp, hV]
  have hbdet : (!![1, 0, 0; 0, p, q; 0, q, r] : Matrix (Fin 3) (Fin 3) ℤ).det = 1 := by
    rw [← hW, conj_det A W hWdet, hdet]
  have hbpos : PosDefZ (!![1, 0, 0; 0, p, q; 0, q, r] : Matrix (Fin 3) (Fin 3) ℤ) := by
    rw [← hW]; exact conj_posDef A W hpos hWdet
  have h2det : (!![p, q; q, r] : Matrix (Fin 2) (Fin 2) ℤ).det = 1 := by
    have hb := block_det p q r
    rw [hbdet] at hb
    rw [Matrix.det_fin_two_of]
    nlinarith [hb]
  have h2sym : (!![p, q; q, r] : Matrix (Fin 2) (Fin 2) ℤ).IsSymm := by
    ext i j; fin_cases i <;> fin_cases j <;> rfl
  obtain ⟨N2, hN2⟩ := classify2 _ h2sym (block_posDef p q r hbpos) h2det
  obtain ⟨N3, hN3⟩ := block_factor p q r N2 hN2
  exact factor_of_conj A W N3 hWdet (by rw [hW, hN3])

/-! ## The auxiliary ternary form -/

/-- The ternary form used to represent `n`. -/
