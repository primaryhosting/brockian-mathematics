import Mathlib

/-!
# Paris Harrington
Category: Frontier — Set Theory
Target: Frontier.Paris_Harrington
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

/-!
## Remarks on the development

Mathlib (as of this toolchain) contains no Ramsey-type theorem: neither the finite nor
the infinite Ramsey theorem is available, so both are developed here from scratch.
The Mathlib ingredients used are the ultrafilter API
(`Ultrafilter.of`, `Ultrafilter.of_le`, `Ultrafilter.eventually_exists_iff`),
the infinite pigeonhole principle `Finite.exists_infinite_fiber`,
and `Set.Infinite.exists_subset_card_eq`.

The development proves:
* `Frontier.infinite_ramsey` — the infinite Ramsey theorem for `n`-element subsets
  and `k` colours (proved by induction on `n`);
* `Frontier.Paris_Harrington` — the strengthened finite Ramsey theorem, deduced from
  the infinite version by an ultrafilter compactness argument;
* `Frontier.finite_ramsey` — the ordinary finite Ramsey theorem, as a corollary.

The assertion that `Frontier.Paris_Harrington` is *unprovable in Peano Arithmetic* is a
statement about a formal proof system rather than a mathematical statement about the
naturals, and is not formalised here.
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

set_option pp.fullNames false
set_option pp.structureInstances true
set_option pp.coercions.types true
set_option pp.funBinderTypes true
set_option pp.letVarTypes true
set_option pp.piBinderTypes true

set_option grind.warning false

namespace Frontier

/-- A set `T` of naturals is *homogeneous* of colour `α` for the colouring `c` of
`n`-element subsets if every `n`-element subset of `T` gets colour `α`. -/

def IsLarge (H : Finset ℕ) : Prop := ∃ a ∈ H, (∀ y ∈ H, a ≤ y) ∧ a ≤ H.card

/-! ### The infinite Ramsey theorem -/

/-- The elements of `S` above its least element. -/
