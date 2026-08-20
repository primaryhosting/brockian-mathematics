/-
# Knill Laflamme
Category: Frontier Qi
Target: QI.knill_laflamme
Statement: A code corrects an error set iff it satisfies the Knill–Laflamme conditions.
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Knill Laflamme
Category: Frontier Qi
Target: QI.knill_laflamme
Statement: A code corrects an error set iff it satisfies the Knill–Laflamme conditions.
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
set_option synthInstance.maxHeartbeats 20000
set_option synthInstance.maxSize 128

set_option relaxedAutoImplicit false
set_option autoImplicit false

set_option grind.warning false

namespace QI

open Matrix

variable {n A : Type*} [Fintype n] [DecidableEq n] [Fintype A] [DecidableEq A]

/-- A *code* is given by the orthogonal projection `P` onto the code subspace: `P` is
self-adjoint, idempotent, and nonzero (the code subspace is nontrivial). -/
structure IsCodeProjector (P : Matrix n n ℂ) : Prop where
  herm : Pᴴ = P
  idem : P * P = P
  nontrivial : P ≠ 0

/-- The error set `E` is the Kraus family of a quantum channel (trace preserving). -/

lemma corrects_of_knill_laflamme (P : Matrix n n ℂ) (E : A → Matrix n n ℂ)
    (hP : IsCodeProjector P) (hE : IsKrausChannel E)
    (h : KnillLaflammeCondition P E) : Corrects P E := by
  obtain ⟨c, hc⟩ := h
  -- diagonalize the Knill–Laflamme matrix
  have hcM : (Matrix.of c).IsHermitian := kl_isHermitian hP hc
  set U : Matrix A A ℂ := (hcM.eigenvectorUnitary : Matrix A A ℂ) with hUdef
  have hU1 : Uᴴ * U = 1 := by
    have := hcM.eigenvectorUnitary.2.1
    rw [Matrix.star_eq_conjTranspose] at this
    exact this
  have hU2 : U * Uᴴ = 1 := by
    have := hcM.eigenvectorUnitary.2.2
    rw [Matrix.star_eq_conjTranspose] at this
    exact this
  set d : A → ℝ := hcM.eigenvalues with hddef
  have hdiag : Uᴴ * (Matrix.of c) * U = diagonal (RCLike.ofReal ∘ d) := by
    have := hcM.conjStarAlgAut_star_eigenvectorUnitary
    rw [Unitary.conjStarAlgAut_apply] at this
    simpa [hUdef, hddef, Matrix.star_eq_conjTranspose] using this
  set F : A → Matrix n n ℂ := fun y => ∑ b, U b y • E b with hFdef
  have hFF : ∀ x y, P * (F x)ᴴ * F y * P = (if x = y then (d x : ℂ) else 0) • P := by
    intro x y
    rw [hFdef, kl_rotated P E c U hc x y, hdiag, Matrix.diagonal_apply]
    by_cases hxy : x = y
    · subst hxy; simp
    · simp [hxy]
  have hFsum : ∑ y, (F y)ᴴ * F y = 1 := kraus_unitary_sum_one E U hU2 hE
  have hd : ∀ x, 0 ≤ d x := fun x => d_nonneg hP hFF x
  have hzero : ∀ x, d x = 0 → F x * P = 0 := fun x hx => FP_eq_zero hP hFF hx
  refine corrects_of_isRecovery (K := Option A) (R := recFam P F d) ⟨?_, ?_⟩
  · exact recFam_sum_one hP hd hFF
  · intro rho hrho
    have hstep : ∀ k : Option A, ∑ a, recFam P F d k * E a * rho * (E a)ᴴ * (recFam P F d k)ᴴ
        = ∑ y, recFam P F d k * F y * rho * (F y)ᴴ * (recFam P F d k)ᴴ := by
      intro k
      have hL : ∀ (B : Matrix n n ℂ) (G : A → Matrix n n ℂ),
          ∑ a, B * G a * rho * (G a)ᴴ * Bᴴ = B * (∑ a, G a * rho * (G a)ᴴ) * Bᴴ := by
        intro B G
        rw [Matrix.mul_sum, Matrix.sum_mul]
        exact Finset.sum_congr rfl fun a _ => by noncomm_ring
      rw [hL (recFam P F d k) E, hL (recFam P F d k) F,
        kraus_unitary_eq E U hU2 rho]
    rw [Finset.sum_congr rfl fun k (_ : k ∈ Finset.univ) => hstep k]
    exact recFam_recovers hP hd hFF hzero hFsum rho hrho

/-- **Knill–Laflamme theorem.**  A code (given by the projector `P` onto the code subspace)
corrects an error set `E` (i.e. there is a recovery channel undoing the error channel on all
states supported by the code) if and only if the Knill–Laflamme conditions
`P Eₐ† E_b P = c a b • P` hold. -/
