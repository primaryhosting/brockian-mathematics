/-
# Simon Algorithm
Category: Frontier Qi
Target: QI.simon_algorithm
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/
-- (Lean requires `import` lines to precede any module docstring, so the header above is
-- repeated as a module docstring immediately after the import.)

import Mathlib

/-!
# Simon Algorithm
Category: Frontier Qi
Target: QI.simon_algorithm
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open scoped BigOperators
open scoped Real
open scoped Nat
open scoped Classical
open scoped Pointwise

set_option maxHeartbeats 8000000
set_option maxRecDepth 4000
set_option synthInstance.maxHeartbeats 40000
set_option synthInstance.maxSize 128

set_option relaxedAutoImplicit false
set_option autoImplicit false

set_option grind.warning false

namespace QI

/-! ## Bit vectors -/

/-- `n`-bit strings, as a vector space over `ZMod 2`. -/
abbrev BV (n : ℕ) := Fin n → ZMod 2

variable {n : ℕ}


lemma not_mem_diffs (Q : Finset (BV n)) {s : BV n} (hs : s ∉ diffs Q) :
    ∀ x ∈ Q, x + s ∉ Q := by
  intro x hx hxs
  refine hs (Finset.mem_image.2 ⟨(x, x + s), Finset.mem_product.2 ⟨hx, hxs⟩, ?_⟩)
  show x + (x + s) = s
  rw [← add_assoc, BV.add_self, zero_add]

/-- **Classical lower bound (raw form).**  A deterministic classical algorithm that always
identifies the hidden shift using `k` queries must satisfy `2 ^ n ≤ k * k + 2`. -/
