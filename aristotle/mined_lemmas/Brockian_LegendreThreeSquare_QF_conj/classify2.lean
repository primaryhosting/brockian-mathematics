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

theorem classify2 (C : Matrix (Fin 2) (Fin 2) ℤ) (hsym : C.IsSymm) (hpos : PosDefZ C)
    (hdet : C.det = 1) : ∃ N : Matrix (Fin 2) (Fin 2) ℤ, C = Nᵀ * N := by
  obtain ⟨v, hv⟩ := exists_QF_eq_one2 C hsym hpos hdet
  -- w = C.mulVec v satisfies w ⬝ᵥ v = QF C v = 1
  let w := C.mulVec v
  have hwv : w ⬝ᵥ v = 1 := by
    have h := hv
    simp [QF, dotProduct] at h
    convert h using 1
    simp [w, Matrix.mulVec]
    ring
  obtain ⟨U, hUdet, hUcol⟩ := exists_unimodular_col2 v w hwv
  -- (Uᵀ * C * U) 0 0 = QF C v = 1
  have h00 : (Uᵀ * C * U) 0 0 = 1 := by
    have := conj_entry00_2 C U v hUcol
    simp [this, hv]
  -- Apply clear_first2
  obtain ⟨V, hVdet, hV⟩ := clear_first2 (Uᵀ * C * U) (conj_isSymm C U hsym) h00
  -- W = U * V, so Wᵀ * C * W = !![1, 0; 0, d]
  let W := U * V
  have hWdet : W.det = 1 := by simp [W, hUdet, hVdet]
  have hW : Wᵀ * C * W = !![1, 0; 0, (Uᵀ * C * U) 1 1 - (Uᵀ * C * U) 0 1 ^ 2] := by
    have : Wᵀ * C * W = Vᵀ * (Uᵀ * C * U) * V := by simp [W, Matrix.mul_assoc]
    rw [this, hV]
  -- The (1,1) entry equals 1 since det is preserved
  let d := (Uᵀ * C * U) 1 1 - (Uᵀ * C * U) 0 1 ^ 2
  have hd : d = 1 := by
    have hdet' := conj_det C W hWdet
    rw [hW] at hdet'
    simp [Matrix.det_fin_two] at hdet'
    have hCdet : C 0 0 * C 1 1 - C 0 1 * C 1 0 = 1 := by simp [Matrix.det_fin_two] at hdet; linarith [hsym.eq]
    linarith
  -- Wᵀ * C * W = 1, so C = (W⁻¹)ᵀ * W⁻¹
  have hWone : Wᵀ * C * W = 1 := by
    rw [hW]
    ext i j; fin_cases i <;> fin_cases j <;> simp <;> linarith [hd]
  -- Use exists_inv_of_det_one to get W⁻¹
  obtain ⟨Winv, hWWinv, hWinvW⟩ := exists_inv_of_det_one W hWdet
  use Winv
  -- C = Winvᵀ * Winv because Wᵀ * C * W = 1
  calc C = 1 * C * 1 := by rw [Matrix.one_mul, Matrix.mul_one]
    _ = (Winvᵀ * Wᵀ) * C * (W * Winv) := by rw [← Matrix.transpose_mul, hWWinv]; simp
    _ = Winvᵀ * (Wᵀ * C * W) * Winv := by simp [Matrix.mul_assoc]
    _ = Winvᵀ * Winv := by rw [hWone]; simp

