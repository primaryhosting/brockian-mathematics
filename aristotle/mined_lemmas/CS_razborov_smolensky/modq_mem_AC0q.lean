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

theorem modq_mem_AC0q (q : ℕ) :
    ∃ (d c N : ℕ) (C : (n : ℕ) → Circuit n),
      (∀ n, N ≤ n → (C n).depth ≤ d) ∧
      (∀ n, N ≤ n → (C n).size ≤ n ^ c + c) ∧
      (∀ n, N ≤ n → ∀ x : Cube n, (C n).eval q x = decide (¬ q ∣ wt x)) :=
  ⟨1, 1, 0, modqCircuit, fun n _ => modqCircuit_depth n,
    fun n _ => by simp, fun n _ x => modqCircuit_eval q n x⟩

end RS
end CS

import RequestProject.RS.Degree
import RequestProject.RS.Circuit

/-!
# Auxiliary lemmas

* a polynomial is eventually dominated by an exponential;
* existence of a primitive `p`-th root of unity in characteristic `q ≠ p`;
* restricting a function on the cube `{0,1}^(n+j)` to the subcube where the last `j`
  coordinates are `1` does not increase the degree.
-/

namespace CS
namespace RS

open Finset Filter

/-- Polynomials are eventually dominated by exponentials. -/
