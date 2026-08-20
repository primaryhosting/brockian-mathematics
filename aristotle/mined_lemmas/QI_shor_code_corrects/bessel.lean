import Mathlib
/-!
# Shor Code Corrects
Category: Frontier Qi
Target: QI.shor_code_corrects
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

/-
Note on the header: Lean 4 requires `import` commands to be the very first commands in a
file, and `/-! ... -/` is a module doc-comment *command*, not a comment token.  The
required header block is therefore placed immediately after the single `import Mathlib`
line, which is the closest legal position to the top of the file.
-/

namespace QI

open Finset

noncomputable section

/-! ## The 9-qubit state space -/

/-- Qubit labels: three blocks of three qubits. -/
abbrev Qb := Fin 3 × Fin 3

/-- Computational basis labels for 9 qubits. -/
abbrev Cfg := Qb → Bool

/-- The state space of 9 qubits, `ℂ^(2^9)`. -/
abbrev H := Cfg → ℂ

/-- Hermitian inner product, conjugate linear in the first argument. -/

lemma bessel (φ : H) :
    ip (φ - Qp φ) (φ - Qp φ)
      + ∑ m : J × Bool, (starRingEnd ℂ) (ip (V m) φ) * ip (V m) φ = ip φ φ := by
  have h2 : ip (Qp φ) φ = ∑ m : J × Bool, (starRingEnd ℂ) (ip (V m) φ) * ip (V m) φ := by
    rw [Qp_apply, ip_sum_left]
    exact Finset.sum_congr rfl fun m _ => ip_smul_left _ _ _
  have h1 : ip φ (Qp φ) = ∑ m : J × Bool, (starRingEnd ℂ) (ip (V m) φ) * ip (V m) φ := by
    rw [Qp_apply, ip_sum_right]
    refine Finset.sum_congr rfl fun m _ => ?_
    rw [ip_smul_right, ← ip_conj (V m) φ]
    ring
  have hQ : ip (Qp φ) (Qp φ) = ∑ m : J × Bool, (starRingEnd ℂ) (ip (V m) φ) * ip (V m) φ := by
    rw [Qp_apply, ip_sum_left]
    refine Finset.sum_congr rfl fun m _ => ?_
    rw [ip_smul_left, ip_sum_right]
    have hin : ∀ n : J × Bool,
        ip (V m) (ip (V n) φ • V n) = if m = n then ip (V n) φ else 0 := by
      intro n
      rw [ip_smul_right, V_orthonormal]
      split <;> simp
    rw [Finset.sum_congr rfl (fun n _ => hin n),
      Finset.sum_ite_eq Finset.univ m (fun n => ip (V n) φ), if_pos (Finset.mem_univ m)]
  rw [ip_sub_left, ip_sub_right, ip_sub_right, h1, h2, hQ]
  ring

/-! ## Main theorem

The 9-qubit Shor code corrects an arbitrary single-qubit error:

* the two logical states `L false`, `L true` are orthonormal, so the code space is a
  genuine qubit;
* the family `R` of Kraus operators is trace preserving, i.e. it is a quantum channel
  (`∑ s, ‖R s φ‖² = ‖φ‖²` for every state `φ`);
* for **every** qubit `i`, **every** single-qubit operator `M` (an arbitrary complex
  `2 × 2` matrix, hence an arbitrary Kraus operator of an arbitrary single-qubit noise
  channel) and every branch `s` of the recovery, the recovery returns the original code
  state `α|0_L⟩ + β|1_L⟩` up to a scalar `c` that does not depend on the encoded state.
  Hence the recovery channel restores the encoded state exactly.
-/
