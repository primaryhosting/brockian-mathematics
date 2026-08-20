import Mathlib
/-!
# Qudit generalized Pauli group (Weyl–Heisenberg) — the "why five" of quantum computing.
Bare `import Mathlib`; no non-core/Archive namespaces or invented lemmas. TRUE for every dimension d.
-/
namespace BrockianQuantum
open Matrix

variable (d : ℕ) [NeZero d]

/-- Qudit **shift** gate (generalized Pauli X): `X e_j = e_{j+1}` on `ZMod d`. -/

def shift : Matrix (ZMod d) (ZMod d) ℂ := fun i j => if i = j + 1 then 1 else 0

/-- Qudit **clock** gate (generalized Pauli Z): `Z e_j = ω^j e_j`, `ω = exp(2πi/d)`. -/
