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

lemma finrank_Deg_le (K : Type*) [Field K] (n D : ℕ) :
    Module.finrank K (Deg K n D) ≤ ∑ i ∈ Finset.range (D+1), n.choose i := by
  classical
  have h1 : Deg K n D = LinearMap.range (Fintype.linearCombination K
      (fun T : {T : Finset (Fin n) // T.card ≤ D} => mono K T.1)) := by
    rw [Fintype.range_linearCombination]
    rfl
  rw [h1]
  calc Module.finrank K (LinearMap.range (Fintype.linearCombination K
        (fun T : {T : Finset (Fin n) // T.card ≤ D} => mono K T.1)))
      ≤ Module.finrank K ({T : Finset (Fin n) // T.card ≤ D} → K) :=
        LinearMap.finrank_range_le _
    _ = Fintype.card {T : Finset (Fin n) // T.card ≤ D} :=
        Module.finrank_fintype_fun_eq_card K
    _ = ∑ i ∈ Finset.range (D+1), n.choose i := card_subtype_card_le n D

end RS
end CS

import Mathlib

/-!
# Binomial estimates

The counting estimates needed for the Razborov–Smolensky theorem: the sum of the binomial
coefficients `C(n,i)` for `i ≤ n/2 + D` is at most `2^(n-1) + D * C(n, n/2)`, and the central
binomial coefficient is small compared to `2^n / √n`.
-/

namespace CS
namespace RS

open Finset

/-- A sharp form of `C(2m,m) ≤ 4^m / √(3m+1)`. -/
