/-
# Shor Code Corrects
Category: Frontier Qi
Target: QI.shor_code_corrects
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/
-- (Lean 4 requires `import` to be the first command, so the header above is written as a
-- plain block comment rather than a `/-!` module docstring.)

import Mathlib

open scoped BigOperators
open scoped Matrix

namespace QI

/-! ## The 9-qubit register

We label the nine qubits by `Site = Fin 3 × Fin 3`: the first coordinate is the *block*
(one of three three-qubit repetition blocks) and the second the position inside the block.
A computational basis state is a bit string `Bits = Site → ZMod 2`, and a state vector is
its amplitude function `Amp = Bits → ℂ`.
-/

abbrev Site : Type := Fin 3 × Fin 3

abbrev Bits : Type := Site → ZMod 2

abbrev Amp : Type := Bits → ℂ

/-- The Hermitian inner product `⟪u, v⟫ = ∑_b conj (u b) * v b`. -/

theorem shor_logical_orthonormal :
    ipf zeroL zeroL = 1 ∧ ipf oneL oneL = 1 ∧ ipf zeroL oneL = 0 ∧ ipf oneL zeroL = 0 := by
  have hz : ∀ s : Fin 3, (0 : Bits) (0, s) = 0 := fun _ => rfl
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [ipf, sum_over_code _ (fun b hb => by simp [zeroL_off hb])]
    simp only [zeroL, if_pos (isCode_rep _), conj_kappa]
    rw [Finset.sum_const, kappa_sq]
    norm_num
  · rw [ipf, sum_over_code _ (fun b hb => by simp [oneL_off hb])]
    have : ∀ c : Fin 3 → ZMod 2,
        (starRingEnd ℂ) (oneL (rep c)) * oneL (rep c) = kappa * kappa := by
      intro c
      simp only [oneL, if_pos (isCode_rep c), map_mul, conj_kappa, conj_sgn]
      rw [show sgn (lw (rep c)) * kappa * (sgn (lw (rep c)) * kappa)
        = sgn (lw (rep c)) * sgn (lw (rep c)) * (kappa * kappa) by ring, sgn_mul_self, one_mul]
    simp only [this]
    rw [Finset.sum_const, kappa_sq]
    norm_num
  · rw [ipf_eq_G]
    exact G_offdiag_zeroL_oneL 0 0 hz
  · rw [ipf_eq_G]
    exact G_offdiag_oneL_zeroL 0 0 hz

/-! ## Sharpness: the hypothesis on the weight of the error cannot be dropped

The operator `Z^{⊗ 9}` (a Pauli `Z` on every one of the nine qubits) is a *logical* bit flip:
it maps `|1_L⟩` to `|0_L⟩`.  Hence the Knill–Laflamme off-diagonal condition genuinely fails
for it, which shows that `shor_code_corrects` is not vacuously true and that the restriction
to errors supported on a single qubit is essential. -/

/-- The all-ones bit string; `Umat 0 allOnes` is `Z` applied to every qubit. -/
