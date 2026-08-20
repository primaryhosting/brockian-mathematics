import Mathlib
/-!
# Qudit generalized Pauli group (Weyl–Heisenberg) — the "why five" of quantum computing.
Bare `import Mathlib`; no non-core/Archive namespaces or invented lemmas. TRUE for every dimension d.
-/
namespace BrockianQuantum
open Matrix

variable (d : ℕ) [NeZero d]

/-- Qudit **shift** gate (generalized Pauli X): `X e_j = e_{j+1}` on `ZMod d`. -/

theorem shift_pow_card : (shift d) ^ d = 1 := by
  ext i j
  rw [shift_pow_apply, Matrix.one_apply]
  simp

/-- `exp (2πi m / d)` only depends on `m` modulo `d`. -/
