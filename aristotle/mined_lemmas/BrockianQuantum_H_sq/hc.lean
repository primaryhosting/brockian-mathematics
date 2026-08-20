import Mathlib
/-!
# Batch 2 — Hadamard gate & basis change. All TRUE; bare `import Mathlib`.
-/
namespace BrockianQuantum
open Matrix

noncomputable def hc : ℂ := (Real.sqrt 2 : ℂ)⁻¹
/-- Hadamard. -/ noncomputable def H : Matrix (Fin 2) (Fin 2) ℂ := !![hc, hc; hc, -hc]
