/-
# Singular Series Gaps 7280
Category: Brockian Corpus
Target: Brockian.SingularSeriesGaps7280
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/
-- (Header kept verbatim, but as a plain block comment: Lean 4 forbids module
-- doc comments before `import`.)

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

namespace Brockian

/-- A finite set `H` of natural numbers is *admissible* if, for every prime `p`, the
reductions of the elements of `H` modulo `p` omit at least one residue class.
This is exactly the classical condition guaranteeing that the singular series
`𝔖(H)` attached to the tuple `H` does not vanish. -/

theorem exists_admissible_beyond (k N : ℕ) :
    ∃ H : Finset ℕ, H.card = k ∧ (∀ q ∈ H, Nat.Prime q ∧ N < q) ∧ Admissible H := by
  have hinf : {q : ℕ | q.Prime ∧ max k N < q}.Infinite := by
    have h1 : {q : ℕ | q.Prime}.Infinite := Nat.infinite_setOf_prime
    have h2 : ({q : ℕ | q.Prime} \ {q : ℕ | q ≤ max k N}).Infinite :=
      h1.diff (Set.finite_le_nat _)
    refine h2.mono ?_
    intro q hq
    exact ⟨hq.1, not_le.mp hq.2⟩
  obtain ⟨H, hsub, hcard⟩ := hinf.exists_subset_card_eq k
  refine ⟨H, hcard, ?_, ?_⟩
  · intro q hq
    have := hsub hq
    simp only [Set.mem_setOf_eq] at this
    exact ⟨this.1, lt_of_le_of_lt (le_max_right k N) this.2⟩
  · refine SingularSeriesGaps7280 (fun q hq => (hsub hq).1) (fun q hq => ?_)
    have hq' := hsub hq
    simp only [Set.mem_setOf_eq] at hq'
    have : H.card ≤ max k N := by rw [hcard]; exact le_max_left k N
    exact lt_of_le_of_lt this hq'.2

/-- A concrete instance: `{11, 13, 17, 19, 23}` is an admissible 5-tuple. -/
