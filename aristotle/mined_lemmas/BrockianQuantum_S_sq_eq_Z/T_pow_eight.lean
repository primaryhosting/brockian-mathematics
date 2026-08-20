import Mathlib
/-!
# Batch 3 — phase gates S, T (Clifford+T). All TRUE; bare `import Mathlib`.
-/
namespace BrockianQuantum
open Matrix

theorem T_pow_eight : T ^ 8 = 1 := by
  have h : T ^ 8 = (T * T) ^ 4 := by noncomm_ring
  rw [h, T_sq_eq_S, S_pow_four]

