import Mathlib
/-!
# Batch 13 — Clifford conjugations (H, S normalize the Pauli group). All TRUE; bare import Mathlib.
-/
namespace BrockianQuantum
open Matrix

noncomputable def PY : Matrix (Fin 2) (Fin 2) ℂ := !![0, -Complex.I; Complex.I, 0]
