import Mathlib
/-!
# Batch 2 — Hadamard gate & basis change. All TRUE; bare `import Mathlib`.
-/
namespace BrockianQuantum
open Matrix

private lemma hc_conj : (starRingEnd ℂ) hc = hc := by
  simp [hc, ← Complex.ofReal_inv]

