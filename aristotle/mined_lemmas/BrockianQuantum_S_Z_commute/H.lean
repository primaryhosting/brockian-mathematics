import Mathlib
/-!
# Batch 13 — Clifford conjugations (H, S normalize the Pauli group). All TRUE; bare import Mathlib.
-/
namespace BrockianQuantum
open Matrix

noncomputable def H : Matrix (Fin 2) (Fin 2) ℂ := !![hc, hc; hc, -hc]
