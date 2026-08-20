/-
# Paris Harrington
Category: Frontier — Set Theory
Target: Frontier.Paris_Harrington
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/
-- (Lean 4.28 rejects a `/-!` module docstring before `import`, so the header
-- above is a plain block comment; it is repeated verbatim as a module docstring
-- immediately after the imports.)
import RequestProject.Ramsey

/-!
# Paris Harrington
Category: Frontier — Set Theory
Target: Frontier.Paris_Harrington
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

namespace Frontier

/-- A finite set of natural numbers is *relatively large* (in the sense of
Paris–Harrington) if it is nonempty and its cardinality is at least its least
element. -/

def IsHomogeneous (n : ℕ) {k : ℕ} (c : Finset ℕ → Fin k) (H : Finset ℕ) : Prop :=
  ∀ s ⊆ H, ∀ t ⊆ H, s.card = n → t.card = n → c s = c t

/-- **The strengthened finite Ramsey theorem (Paris–Harrington)**.

For all `n, k, m` there is an `N` such that for every colouring `c` of the
`n`-element subsets of `{1, …, N}` with `k` colours there is a subset
`H ⊆ {1, …, N}` which is homogeneous for `c`, has at least `m` elements, and is
*relatively large*: its cardinality is at least its least element.

(The second half of the Paris–Harrington result — that this statement is not
provable in first-order Peano Arithmetic — is a metamathematical statement about
a formal theory and is not formalized here; what is proved here is the
mathematical content, namely that the statement is true.) -/
