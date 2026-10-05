/-
/-!
# Bolzano Weierstrass
Category: Pure Mathematics
Target: Math.bolzano_weierstrass
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/
-/
-- (The header above is wrapped in an outer block comment because Lean 4 requires
-- `import` commands to precede any module docstring `/-! ... -/`.)

import Mathlib

open Filter Topology Bornology

namespace Math

/-- **Bolzano–Weierstrass in `ℝⁿ`**: every bounded sequence in `EuclideanSpace ℝ (Fin n)`
has a convergent subsequence.

The proof uses Mathlib's `tendsto_subseq_of_bounded`, which states that in a proper metric
space any sequence contained in a bounded set has a subsequence converging to a point of the
closure of that set; `EuclideanSpace ℝ (Fin n)` is proper (finite-dimensional, Heine–Borel). -/
theorem bolzano_weierstrass {n : ℕ} (u : ℕ → EuclideanSpace ℝ (Fin n)) (C : ℝ)
    (hC : ∀ k, ‖u k‖ ≤ C) :
    ∃ φ : ℕ → ℕ, StrictMono φ ∧ ∃ L : EuclideanSpace ℝ (Fin n),
      Tendsto (u ∘ φ) atTop (𝓝 L) := by
  obtain ⟨L, -, φ, hφ, hL⟩ := tendsto_subseq_of_bounded
    (isBounded_iff_forall_norm_le.2 ⟨C, fun x hx => by obtain ⟨k, rfl⟩ := hx; exact hC k⟩)
    (fun k => Set.mem_range_self k)
  exact ⟨φ, hφ, L, hL⟩

end Math

import Mathlib

open scoped BigOperators
open scoped Real
open scoped Nat
open scoped Classical
open scoped Pointwise

set_option maxHeartbeats 8000000
set_option maxRecDepth 4000
set_option synthInstance.maxHeartbeats 20000
set_option synthInstance.maxSize 128

set_option relaxedAutoImplicit false
set_option autoImplicit false

set_option pp.fullNames true
set_option pp.structureInstances true
set_option pp.coercions.types true
set_option pp.funBinderTypes true
set_option pp.letVarTypes true
set_option pp.piBinderTypes true

set_option grind.warning false

