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

/-
# Razborov Smolensky
Category: Frontier Cs
Target: CS.razborov_smolensky
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/
-- (Lean requires `import` commands to precede any module docstring, so the header above is
-- written as a plain block comment and repeated verbatim as a module docstring below.)

import RequestProject.RS.CircuitApprox
import RequestProject.RS.Smolensky
import RequestProject.RS.Binomial
import RequestProject.RS.Aux
import RequestProject.RS.Sanity

/-!
# Razborov Smolensky
Category: Frontier Cs
Target: CS.razborov_smolensky
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

/-!
The Razborov–Smolensky theorem: for distinct primes `p` and `q`, the Boolean function `MOD p`
(which tests whether the number of `1`s in the input is divisible by `p`) is not computed by any
family of constant-depth, polynomial-size circuits with unbounded fan-in AND, OR, NOT and
`MOD q` gates, i.e. `MOD p ∉ AC⁰[q]`.

The proof combines
* `CS.RS.Circuit.exists_approx`: every `AC⁰[q]` circuit is approximated, on all but a small
  fraction of the inputs, by a low-degree function over a field of characteristic `q`;
* `CS.RS.smolensky_bound`: a low-degree function can agree with `x ↦ ζ^(weight x)` (for `ζ` a
  primitive `p`-th root of unity) only on a set of inputs of size at most
  `∑_{i ≤ n/2 + D} C(n,i)`;
* `CS.RS.modq_mem_AC0q`: a non-vacuity check, exhibiting `MOD q` itself as a depth-one,
  linear-size circuit family of this kind;
* binomial estimates showing that this is less than the number of inputs left over by the
  approximation step.
-/

namespace CS

open Finset CS.RS

/-- Shifting the weight by `(p - r) % p` detects the residue `r` modulo `p`. -/

lemma sum_choose_le (m D : ℕ) :
    ∑ i ∈ Finset.range (m + D + 1), (2*m+1).choose i ≤ 4^m + D * ((2*m+1).choose m) := by
  have hsplit : ∑ i ∈ Finset.range (m + D + 1), (2*m+1).choose i
      = (∑ i ∈ Finset.range (m + 1), (2*m+1).choose i)
        + ∑ i ∈ Finset.Ico (m+1) (m + D + 1), (2*m+1).choose i := by
    simp only [Finset.range_eq_Ico]
    rw [← Finset.sum_Ico_consecutive _ (Nat.zero_le (m+1)) (by omega : m+1 ≤ m + D + 1)]
  rw [hsplit, Nat.sum_range_choose_halfway m]
  refine Nat.add_le_add_left ?_ _
  calc ∑ i ∈ Finset.Ico (m+1) (m + D + 1), (2*m+1).choose i
      ≤ ∑ _i ∈ Finset.Ico (m+1) (m + D + 1), ((2*m+1).choose m) := by
        refine Finset.sum_le_sum (fun i _ => ?_)
        have := Nat.choose_le_middle i (2*m+1)
        rwa [show (2*m+1)/2 = m by omega] at this
    _ = D * ((2*m+1).choose m) := by
        rw [Finset.sum_const, Nat.card_Ico, smul_eq_mul]
        congr 1
        omega

end RS
end CS

