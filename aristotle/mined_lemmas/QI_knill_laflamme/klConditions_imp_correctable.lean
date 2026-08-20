/-
# Knill Laflamme
Category: Frontier Qi
Target: QI.knill_laflamme
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

-- (Lean requires `import` lines to precede any module docstring, so the required header is
-- repeated verbatim as the module docstring immediately below the import.)

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

set_option maxHeartbeats 8000000
set_option maxRecDepth 4000
set_option synthInstance.maxHeartbeats 20000
set_option synthInstance.maxSize 128

set_option relaxedAutoImplicit false
set_option autoImplicit false

set_option grind.warning false

namespace QI

open Matrix ComplexOrder

variable {d ι : Type*} [Fintype d] [DecidableEq d] [Fintype ι] [DecidableEq ι]

/-! ## Definitions -/

/-- The **Knill–Laflamme conditions** for a code with orthogonal projector `P` and a set of
error operators `E i`: `P (E i)ᴴ (E j) P = c i j • P` for some matrix of scalars `c`. -/

theorem klConditions_imp_correctable {P : Matrix d d ℂ} {E : ι → Matrix d d ℂ}
    (hPh : Pᴴ = P) (hPi : P * P = P) (hP0 : P ≠ 0) (hE : ∑ i, (E i)ᴴ * E i = 1)
    (h : KLConditions P E) : Correctable P E := by
  obtain ⟨c, hKL⟩ := h
  obtain ⟨U, dd, hnn, hUsU, hUUs, hdiag, htr⟩ :=
    exists_unitary_diagonalization (kl_posSemidef hPh hPi hP0 hKL)
  obtain ⟨F, hF⟩ : ∃ F : ι → Matrix d d ℂ, F = fun k => ∑ i, U i k • E i := ⟨_, rfl⟩
  have hFKL : ∀ k l, P * (F k)ᴴ * F l * P = (if k = l then (dd k : ℂ) else 0) • P := by
    intro k l
    rw [hF, kl_conj_unitary hKL U k l, hdiag, Matrix.diagonal_apply]
  have hFchan : ∀ ρ, ∑ k, F k * ρ * (F k)ᴴ = ∑ i, E i * ρ * (E i)ᴴ := by
    intro ρ; rw [hF]; exact sum_unitary_kraus U hUUs E ρ
  have hcsum : ∑ i, c i i = 1 := by
    have e1 : ∑ i, (P * (E i)ᴴ * E i * P) = (∑ i, c i i) • P := by
      simp only [hKL, ← Finset.sum_smul]
    have e2 : ∑ i, (P * (E i)ᴴ * E i * P) = P := by
      have hterm : ∀ i : ι, P * (E i)ᴴ * E i * P = P * ((E i)ᴴ * E i) * P := by
        intro i; rw [Matrix.mul_assoc P]
      simp only [hterm]
      rw [← Finset.sum_mul, ← Finset.mul_sum, hE, Matrix.mul_one, hPi]
    exact smul_proj_inj hP0 (by rw [← e1, e2, one_smul])
  have hddsum : ∑ k, (dd k : ℂ) = 1 := by
    rw [← htr, Matrix.trace]
    simpa [Matrix.diag] using hcsum
  obtain ⟨S, hS⟩ : ∃ S : ι → Matrix d d ℂ,
      S = fun k => ((Real.sqrt (dd k) : ℂ))⁻¹ • (P * (F k)ᴴ) := ⟨_, rfl⟩
  have hSadj : ∀ k, (S k)ᴴ = ((Real.sqrt (dd k) : ℂ))⁻¹ • (F k * P) := by
    intro k
    rw [hS]
    simp [conjTranspose_mul, hPh, Complex.conj_ofReal]
  have hF0 : ∀ l, dd l = 0 → F l * P = 0 := by
    intro l hl
    have h1 : (F l * P)ᴴ * (F l * P) = 0 := by
      rw [conjTranspose_mul, hPh, ← Matrix.mul_assoc, hFKL l l, if_pos rfl, hl]
      simp
    exact conjTranspose_mul_self_eq_zero.mp h1
  have hsqrt_mul : ∀ k, ((Real.sqrt (dd k) : ℂ)) * ((Real.sqrt (dd k) : ℂ)) = (dd k : ℂ) := by
    intro k; norm_cast; rw [Real.mul_self_sqrt (hnn k)]
  have hSF : ∀ k l, S k * F l * P = if k = l then ((Real.sqrt (dd k) : ℂ)) • P else 0 := by
    intro k l
    have hrw : S k * F l * P = ((Real.sqrt (dd k) : ℂ))⁻¹ • (P * (F k)ᴴ * F l * P) := by
      rw [hS]; simp
    rw [hrw, hFKL k l]
    by_cases hkl : k = l
    · rw [if_pos hkl, if_pos hkl, smul_smul]
      congr 1
      have := real_inv_sqrt_mul_self (hnn k)
      exact_mod_cast congrArg (fun t : ℝ => (t : ℂ)) this
    · rw [if_neg hkl, if_neg hkl]; simp
  obtain ⟨Q, hQdef⟩ : ∃ Q : Matrix d d ℂ, Q = ∑ k, (S k)ᴴ * S k := ⟨_, rfl⟩
  have hQF : ∀ l, Q * (F l * P) = F l * P := by
    intro l
    rw [hQdef, Finset.sum_mul]
    have hterm : ∀ k : ι, (S k)ᴴ * S k * (F l * P) = if k = l then F l * P else 0 := by
      intro k
      have h1 : (S k)ᴴ * S k * (F l * P) = (S k)ᴴ * (S k * F l * P) := by
        simp [Matrix.mul_assoc]
      rw [h1, hSF k l]
      by_cases hkl : k = l
      · subst hkl
        rw [if_pos rfl, if_pos rfl, hSadj k, Matrix.smul_mul, Matrix.mul_smul, smul_smul,
          Matrix.mul_assoc, hPi]
        rcases eq_or_lt_of_le (hnn k) with h0 | h0
        · rw [hF0 k h0.symm]; simp
        · have hs : (Real.sqrt (dd k) : ℂ) ≠ 0 := by
            simpa using Real.sqrt_ne_zero'.mpr h0
          rw [inv_mul_cancel₀ hs, one_smul]
      · rw [if_neg hkl, if_neg hkl, Matrix.mul_zero]
    simp only [hterm]
    simp
  have hQh : Qᴴ = Q := by
    rw [hQdef, conjTranspose_sum]
    exact Finset.sum_congr rfl fun k _ => by
      rw [conjTranspose_mul, conjTranspose_conjTranspose]
  have hQS : ∀ l, Q * (S l)ᴴ = (S l)ᴴ := by
    intro l; rw [hSadj l, Matrix.mul_smul, hQF l]
  have hQQ : Q * Q = Q := by
    nth_rewrite 2 [hQdef]
    rw [Finset.mul_sum]
    have hterm : ∀ l : ι, Q * ((S l)ᴴ * S l) = (S l)ᴴ * S l := fun l => by
      rw [← Matrix.mul_assoc, hQS l]
    simp only [hterm]
    exact hQdef.symm
  obtain ⟨Rops, hRops⟩ : ∃ Rops : Option ι → Matrix d d ℂ,
      Rops = fun x => x.elim (1 - Q) S := ⟨_, rfl⟩
  have hRnone : Rops none = 1 - Q := by simp [hRops]
  have hRsome : ∀ j, Rops (some j) = S j := by intro j; simp [hRops]
  have hcard : Fintype.card (Option ι) = Fintype.card ι + 1 := by simp
  obtain ⟨e⟩ : Nonempty (Fin (Fintype.card ι + 1) ≃ Option ι) :=
    ⟨(Fintype.equivFinOfCardEq hcard).symm⟩
  refine ⟨Fintype.card ι + 1, fun n => Rops (e n), ?_, ?_⟩
  · rw [Equiv.sum_comp e (fun x => (Rops x)ᴴ * Rops x), Fintype.sum_option, hRnone,
      conjTranspose_sub, conjTranspose_one, hQh]
    have hsq : (1 - Q) * (1 - Q) = 1 - Q := by
      rw [Matrix.sub_mul, Matrix.mul_sub, Matrix.mul_sub, hQQ]
      simp
    rw [hsq]
    have : ∑ j, (Rops (some j))ᴴ * Rops (some j) = Q := by
      rw [hQdef]
      exact Finset.sum_congr rfl fun j _ => by rw [hRsome j]
    rw [this]
    abel
  · intro ρ hρ
    rw [Equiv.sum_comp e (fun x => ∑ i, (Rops x * E i) * ρ * (Rops x * E i)ᴴ)]
    have step1 : ∀ x : Option ι, ∑ i, (Rops x * E i) * ρ * (Rops x * E i)ᴴ
        = ∑ k, (Rops x * F k * P) * ρ * (Rops x * F k * P)ᴴ := by
      intro x
      rw [sum_kraus_conj, ← hFchan ρ, ← sum_kraus_conj]
      exact Finset.sum_congr rfl fun k _ => kraus_restrict hPh (Rops x * F k) hρ
    simp only [step1]
    rw [Fintype.sum_option]
    have hnone : ∑ k, (Rops none * F k * P) * ρ * (Rops none * F k * P)ᴴ = 0 := by
      refine Finset.sum_eq_zero fun k _ => ?_
      have hz : Rops none * F k * P = 0 := by
        rw [hRnone, Matrix.sub_mul, Matrix.one_mul, Matrix.sub_mul,
          Matrix.mul_assoc Q (F k) P, hQF k, sub_self]
      rw [hz]; simp
    rw [hnone, zero_add]
    have hsome : ∀ j : ι, ∑ k, (Rops (some j) * F k * P) * ρ * (Rops (some j) * F k * P)ᴴ
        = (dd j : ℂ) • ρ := by
      intro j
      have hterm : ∀ k : ι, (Rops (some j) * F k * P) * ρ * (Rops (some j) * F k * P)ᴴ
          = if j = k then (dd j : ℂ) • ρ else 0 := by
        intro k
        rw [hRsome j, hSF j k]
        by_cases hjk : j = k
        · rw [if_pos hjk, if_pos hjk, smul_real_proj_conj hPh, hρ, Real.mul_self_sqrt (hnn j)]
        · rw [if_neg hjk, if_neg hjk]; simp
      simp only [hterm]
      simp
    simp only [hsome]
    rw [← Finset.sum_smul, hddsum, one_smul]

/-! ## The Knill–Laflamme theorem -/

/-- **Knill–Laflamme theorem**: a code (given by the orthogonal projector `P` onto a nonzero
code subspace) corrects the error set `E` (which forms a quantum channel,
`∑ i, (E i)ᴴ * E i = 1`) if and only if the Knill–Laflamme conditions
`P (E i)ᴴ (E j) P = c i j • P` hold. -/
