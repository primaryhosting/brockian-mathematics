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

lemma central_binom_sq (m : ℕ) : (3*m+1) * (Nat.centralBinom m)^2 ≤ 16^m := by
  induction m with
  | zero => simp [Nat.centralBinom]
  | succ m ih =>
      have hkey : (m+1) * (m+1).centralBinom = 2 * (2*m+1) * m.centralBinom :=
        Nat.succ_mul_centralBinom_succ m
      have hsq : ((m+1) * (m+1).centralBinom)^2 = (2 * (2*m+1))^2 * (m.centralBinom)^2 := by
        rw [hkey]; ring
      -- multiply the goal by `(m+1)^2`
      have hgoal : (3*(m+1)+1) * ((m+1) * (m+1).centralBinom)^2 ≤ 16^(m+1) * (m+1)^2 := by
        rw [hsq]
        have harith : (3*(m+1)+1) * (2 * (2*m+1))^2 ≤ 16 * (m+1)^2 * (3*m+1) := by
          nlinarith [sq_nonneg m, Nat.zero_le m]
        calc (3*(m+1)+1) * ((2 * (2*m+1))^2 * (m.centralBinom)^2)
            = ((3*(m+1)+1) * (2 * (2*m+1))^2) * (m.centralBinom)^2 := by ring
          _ ≤ (16 * (m+1)^2 * (3*m+1)) * (m.centralBinom)^2 :=
              Nat.mul_le_mul_right _ harith
          _ = (16 * (m+1)^2) * ((3*m+1) * (m.centralBinom)^2) := by ring
          _ ≤ (16 * (m+1)^2) * 16^m := Nat.mul_le_mul_left _ ih
          _ = 16^(m+1) * (m+1)^2 := by ring
      have hpos : 0 < (m+1)^2 := by positivity
      have hfinal : ((3*(m+1)+1) * ((m+1).centralBinom)^2) * (m+1)^2 ≤ 16^(m+1) * (m+1)^2 := by
        calc ((3*(m+1)+1) * ((m+1).centralBinom)^2) * (m+1)^2
            = (3*(m+1)+1) * ((m+1) * (m+1).centralBinom)^2 := by ring
          _ ≤ 16^(m+1) * (m+1)^2 := hgoal
      exact Nat.le_of_mul_le_mul_right hfinal hpos

