import Mathlib
import RequestProject.Main

/-!
# Link with Mathlib's Ackermann function

The Ackermann function `CS.ack` defined in `RequestProject.Main` agrees with
Mathlib's `ack` from `Mathlib/Computability/Ackermann.lean`. Consequently the
totality statement `CS.ackermann_total` also characterises Mathlib's `ack`.
-/

set_option autoImplicit false

namespace CS


theorem ackGraph_mathlib_ack (m n : ℕ) : AckGraph m n (_root_.ack m n) := by
  rw [← ack_eq_mathlib_ack]
  exact ackGraph_ack m n

end CS

/-!
# Ackermann Total
Category: Computer Science
Target: CS.ackermann_total
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

/-
Note on file layout: Lean 4 requires every `import` command to appear at the very
beginning of a file, before any doc comment. Since the required header above is a
module doc comment, this file carries no imports and is fully self-contained
(only Lean core's `Init` is implicitly available). The companion file
`RequestProject/MathlibLink.lean` does import Mathlib and identifies the
Ackermann function defined here with Mathlib's `ack`
(`Mathlib/Computability/Ackermann.lean`).
-/

set_option relaxedAutoImplicit false
set_option autoImplicit false

namespace CS

/-- The lexicographic order on `ℕ × ℕ` is well-founded; this is what justifies the
Ackermann recursion. -/
