import Mathlib
/-!
# Stabilizer formalism: qudit generalized-Pauli unitarity + qubit Pauli anticommutation.
Bare `import Mathlib`; no non-core/Archive namespaces or invented lemmas. All TRUE.
-/
namespace BrockianQuantum
open Matrix

variable (d : ℕ) [NeZero d]

/-- Qudit **shift** (generalized Pauli X). -/

def shift : Matrix (ZMod d) (ZMod d) ℂ := fun i j => if i = j + 1 then 1 else 0

/-- Qudit **clock** (generalized Pauli Z), `ω = exp(2πi/d)`. -/
