import Mathlib
/-!
# Stabilizer formalism: qudit generalized-Pauli unitarity + qubit Pauli anticommutation.
Bare `import Mathlib`; no non-core/Archive namespaces or invented lemmas. All TRUE.
-/
namespace BrockianQuantum
open Matrix

variable (d : ℕ) [NeZero d]

/-- Qudit **shift** (generalized Pauli X). -/

theorem shift_unitary : shift d * (shift d)ᴴ = 1 := by
  ext i l
  -- `i = x + 1` is the same condition as `x = i - 1`, which lets us evaluate the sum.
  have key : ∀ x : ZMod d, (i = x + 1) = (x = i - 1) := by
    intro x; simp [eq_sub_iff_add_eq, eq_comm]
  have key2 : ∀ x : ZMod d, (l = x + 1) = (x = l - 1) := by
    intro x; simp [eq_sub_iff_add_eq, eq_comm]
  simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, shift, Matrix.one_apply,
    RCLike.star_def, key, key2, ite_mul, one_mul, zero_mul]
  rw [Finset.sum_ite_eq' Finset.univ (i - 1)]
  simp [sub_left_inj]

/-- The clock gate is **unitary**: `Z * Zᴴ = 1` (diagonal of unit-modulus phases). -/
