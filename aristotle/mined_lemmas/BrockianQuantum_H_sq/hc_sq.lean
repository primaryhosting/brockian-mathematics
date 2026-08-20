import Mathlib
/-!
# Batch 2 — Hadamard gate & basis change. All TRUE; bare `import Mathlib`.
-/
namespace BrockianQuantum
open Matrix

private lemma hc_sq : hc ^ 2 = 1 / 2 := by rw [pow_two, hc_mul_hc]

/-- `hc` is real, hence fixed by complex conjugation. -/
