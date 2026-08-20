/-!
# Erdos Discrepancy
Category: Frontier — Prime Numbers
Target: Frontier.erdos_discrepancy
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

/-
This file is deliberately self-contained (no imports): a Lean module docstring
must be the first command in a file, so the required header above forces the
file to contain no `import` lines.  Everything below therefore uses only the
Lean 4 core library.  The file `RequestProject/Main.lean` re-states the results
in Mathlib terms (`∑ i ∈ Finset.Icc 1 n, f (i * d)` and `|·|`) and proves that
the two formulations agree.
-/

namespace Frontier

/-- The partial sum of `f` along the homogeneous arithmetic progression with
common difference `d`, over its first `n` terms:  `f d + f (2d) + ⋯ + f (n d)`. -/

theorem erdosDiscrepancyStatement_of_finite
    (H : ∀ C : Nat, ∃ N : Nat, ∀ f : Nat → Int, IsPlusMinusOne f →
      ∃ n d : Nat, 1 ≤ n ∧ 1 ≤ d ∧ n * d ≤ N ∧ C < (hapSum f n d).natAbs) :
    ErdosDiscrepancyStatement := by
  intro f hf C
  obtain ⟨_, hN⟩ := H C
  obtain ⟨n, d, hn, hd, _, hC⟩ := hN f hf
  exact ⟨n, d, hn, hd, hC⟩

end Frontier

import Mathlib
import RequestProject.ErdosDiscrepancy

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

/-!
## Erdős discrepancy: Mathlib-flavoured restatement

`RequestProject/ErdosDiscrepancy.lean` (which must be import-free, since its
required module docstring has to be the first command in the file) develops the
Erdős discrepancy base case using the core-library sum
`((List.range n).map fun i => f ((i+1) * d)).sum`.  Here we check that this
agrees with the Mathlib sum `∑ i ∈ Finset.Icc 1 n, f (i * d)` and restate the
result in Mathlib notation.
-/

namespace Frontier

