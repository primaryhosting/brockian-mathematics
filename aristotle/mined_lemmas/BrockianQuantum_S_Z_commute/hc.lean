import Mathlib
/-!
# Batch 13 — Clifford conjugations (H, S normalize the Pauli group). All TRUE; bare import Mathlib.
-/
namespace BrockianQuantum
open Matrix

noncomputable def hc : ℂ := (Real.sqrt 2 : ℂ)⁻¹
