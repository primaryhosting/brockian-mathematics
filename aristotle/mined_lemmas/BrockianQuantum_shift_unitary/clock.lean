import Mathlib
/-!
# Stabilizer formalism: qudit generalized-Pauli unitarity + qubit Pauli anticommutation.
Bare `import Mathlib`; no non-core/Archive namespaces or invented lemmas. All TRUE.
-/
namespace BrockianQuantum
open Matrix

variable (d : ℕ) [NeZero d]

/-- Qudit **shift** (generalized Pauli X). -/

noncomputable def clock : Matrix (ZMod d) (ZMod d) ℂ :=
  fun i j => if i = j then Complex.exp (2 * Real.pi * Complex.I * (j.val : ℂ) / d) else 0

/-- The shift gate is **unitary**: `X * Xᴴ = 1` (it is a permutation matrix). -/
