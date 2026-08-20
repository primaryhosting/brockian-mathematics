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

lemma mul_choose_le (m D : ℕ) (hm : 1 ≤ m) (h : 16 * D^2 ≤ m) :
    D * ((2*m+1).choose m) ≤ 2^(2*m-1) := by
  set c1 := (2*m+1).choose m with hc1
  have hcb : (m+1).centralBinom = 2 * c1 := by
    rw [Nat.centralBinom, hc1, show 2*(m+1) = 2*m+2 by ring]
    exact choose_odd_middle m
  have hsq := central_binom_sq (m+1)
  rw [hcb] at hsq
  -- hsq : (3*(m+1)+1) * (2*c1)^2 ≤ 16^(m+1)
  -- work with squares
  have h4 : 4 * (3*m+4) * (D * c1)^2 ≤ 4 * (3*m+4) * (2^(2*m-1))^2 := by
    have hstep1 : 4 * (3*m+4) * (D * c1)^2 = D^2 * ((3*m+4) * (2*c1)^2) := by ring
    have hstep2 : D^2 * ((3*m+4) * (2*c1)^2) ≤ D^2 * 16^(m+1) := by
      refine Nat.mul_le_mul_left _ ?_
      calc (3*m+4) * (2*c1)^2 = (3*(m+1)+1) * (2*c1)^2 := by ring
        _ ≤ 16^(m+1) := hsq
    have hstep3 : D^2 * 16^(m+1) ≤ 4 * (3*m+4) * (2^(2*m-1))^2 := by
      have hex : (2:ℕ)^(2*m-1) * 2^(2*m-1) = 2^(4*m-2) := by
        rw [← pow_add]; congr 1; omega
      have h16 : (16:ℕ)^(m+1) = 16 * 16^m := by ring
      have h16m : (16:ℕ)^m = 4 * 2^(4*m-2) := by
        have h2 : (16:ℕ)^m = 2^(4*m) := by
          rw [show (16:ℕ) = 2^4 by norm_num, ← pow_mul, Nat.mul_comm]
        rw [h2, show 4*m = 2 + (4*m-2) by omega, pow_add]
        norm_num
      have hD : 16 * D^2 ≤ 3*m+4 := by omega
      calc D^2 * 16^(m+1) = (16 * D^2) * 16^m := by rw [h16]; ring
        _ ≤ (3*m+4) * 16^m := Nat.mul_le_mul_right _ hD
        _ = (3*m+4) * (4 * 2^(4*m-2)) := by rw [h16m]
        _ = 4 * (3*m+4) * (2^(2*m-1))^2 := by rw [← hex]; ring
    exact le_trans (le_of_eq hstep1) (le_trans hstep2 hstep3)
  have hpos : 0 < 4 * (3*m+4) := by omega
  have hsq2 : (D * c1)^2 ≤ (2^(2*m-1))^2 := Nat.le_of_mul_le_mul_left h4 hpos
  exact (Nat.pow_le_pow_iff_left (n := 2) (by norm_num)).1 hsq2

/-- The sum of binomial coefficients up to `m + D` where `n = 2m+1`. -/
