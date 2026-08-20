/-
# Ramsey 3 5
Category: Pure Mathematics
Target: Math.ramsey_3_5
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/
import Mathlib

/-!
# Ramsey 3 5
Category: Pure Mathematics
Target: Math.ramsey_3_5
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)

(Lean requires `import` to come first in a file, so the header above the import is a plain
block comment and this is the module docstring with the same content.)

Mathlib does not contain Ramsey numbers, so the whole development is built here:
the recursion `R(3,t+1) ≤ t + R(3,t)`, the parity refinement giving `R(3,4) ≤ 9`,
hence `R(3,5) ≤ 14`, and the circulant graph `C₁₃(1,5)` witnessing `R(3,5) > 13`.
-/

set_option maxHeartbeats 2000000

namespace Math

open Finset

/-! ## The Ramsey property -/

/-- `RamseyProp n s t` says that every simple graph on `n` vertices contains either a clique
of size `s` or an independent set of size `t` (equivalently, a clique of size `t` in the
complement).  `R(s,t)` is the least `n` with this property. -/

theorem exists_sorted_three {α : Type} [LinearOrder α] (S : Finset α) (h : S.card = 3) :
    ∃ a b c, a ∈ S ∧ b ∈ S ∧ c ∈ S ∧ a < b ∧ b < c := by
  have f := S.orderIsoOfFin h
  refine ⟨f 0, f 1, f 2, (f 0).2, (f 1).2, (f 2).2, ?_, ?_⟩ <;>
    · exact Subtype.coe_lt_coe.2 (f.strictMono (by decide))

/-- Extract five elements of a `5`-element finset in increasing order. -/
