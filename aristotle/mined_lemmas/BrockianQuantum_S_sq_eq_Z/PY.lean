import Mathlib
/-!
# Batch 3 — phase gates S, T (Clifford+T). All TRUE; bare `import Mathlib`.
-/
namespace BrockianQuantum
open Matrix

noncomputable def PY : Matrix (Fin 2) (Fin 2) ℂ := !![0, -Complex.I; Complex.I, 0]
