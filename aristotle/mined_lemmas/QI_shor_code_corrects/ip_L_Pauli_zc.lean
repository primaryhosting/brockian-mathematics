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

lemma ip_L_Pauli_zc (a b : Bool) (w : Cfg) :
    ip (L a) (Pauli zc w (L b))
      = (nrm * nrm) * ∏ β : Fin 3, (1 + (if a = b then (1 : ℂ) else -1) * mu w β) := by
  rw [ip_L]
  have step : ∀ c : Fin 3 → Bool,
      L a (blk c) * (Pauli zc w (L b)) (blk c)
        = (nrm * nrm) * ∏ β : Fin 3,
            ((if a = b then (1 : ℂ) else sg (c β)) * (if c β then mu w β else 1)) := by
    intro c
    rw [Pauli_apply, xr_zc, L_blk, L_blk, zph_blk]
    rw [Finset.prod_mul_distrib]
    have hsg : (if a then sgnc c else (1:ℂ)) * (if b then sgnc c else (1:ℂ))
        = ∏ β : Fin 3, (if a = b then (1:ℂ) else sg (c β)) := by
      have hsq : sgnc c * sgnc c = 1 := by
        rw [sgnc, ← Finset.prod_mul_distrib]
        exact Finset.prod_eq_one fun β _ => sg_mul_self _
      cases a <;> cases b
      · simp
      · simp [sgnc]
      · simp [sgnc]
      · simpa using hsq
    calc nrm * (if a then sgnc c else 1) *
            ((∏ β : Fin 3, (if c β then mu w β else 1)) * (nrm * (if b then sgnc c else 1)))
        = (nrm * nrm) * ((if a then sgnc c else (1:ℂ)) * (if b then sgnc c else (1:ℂ)))
            * ∏ β : Fin 3, (if c β then mu w β else 1) := by ring
      _ = (nrm * nrm) * (∏ β : Fin 3, (if a = b then (1:ℂ) else sg (c β)))
            * ∏ β : Fin 3, (if c β then mu w β else 1) := by rw [hsg]
      _ = _ := by rw [mul_assoc, ← Finset.prod_mul_distrib]
  simp_rw [step]
  rw [← Finset.mul_sum]
  congr 1
  -- expand the product of sums
  have := Finset.prod_univ_sum (fun _ : Fin 3 => (Finset.univ : Finset Bool))
      (fun (β : Fin 3) (x : Bool) =>
        (if a = b then (1 : ℂ) else sg x) * (if x then mu w β else 1))
  rw [Fintype.piFinset_univ] at this
  rw [← this]
  refine Finset.prod_congr rfl fun β _ => ?_
  rw [Fintype.sum_bool]
  by_cases hab : a = b <;> simp [hab, sg] <;> ring

/-- The main structural fact: an inner product between two Pauli-corrupted logical states. -/
