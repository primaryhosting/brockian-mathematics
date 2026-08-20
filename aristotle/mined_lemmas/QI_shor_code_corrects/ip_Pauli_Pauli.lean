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

lemma ip_Pauli_Pauli (u1 w1 u2 w2 : Cfg) (x y : H) :
    ip (Pauli u1 w1 x) (Pauli u2 w2 y)
      = zph w1 (xr u1 u2) * ip x (Pauli (xr u1 u2) (xr w1 w2) y) := by
  have hz : ∀ t : Cfg, (starRingEnd ℂ) (zph w1 t) = zph w1 t := by
    intro t
    simp only [zph, map_prod]
    exact Finset.prod_congr rfl fun q _ => by cases (w1 q && t q) <;> simp [sg]
  simp only [ip, Pauli_apply, Finset.mul_sum]
  -- reindex `v ↦ xr v u1`
  rw [← Equiv.sum_comp (Equiv.mk (fun v => xr v u1) (fun v => xr v u1)
      (fun v => by simp [xr_xr]) (fun v => by simp [xr_xr]))]
  refine Finset.sum_congr rfl fun t _ => ?_
  simp only [Equiv.coe_fn_mk, xr_xr, map_mul, hz]
  have h1 : xr (xr t u1) u2 = xr t (xr u1 u2) := by
    funext q; simp [xr]
  rw [h1]
  have h2 : zph w2 (xr t (xr u1 u2)) = zph w2 t * zph w2 (xr u1 u2) := zph_xor_right _ _ _
  linear_combination ((starRingEnd ℂ) (x t) * y (xr t (xr u1 u2))) * zph_shift w1 w2 t (xr u1 u2)

/-! ## Block-constant configurations -/

/-- A configuration is *block constant* if it is constant on each block of three qubits. -/
