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

lemma mono_mul (T U : Finset (Fin n)) : mono K T * mono K U = mono K (T ∪ U) := by
  funext x
  simp only [Pi.mul_apply, mono_apply_eq]
  by_cases h : ∀ i ∈ T ∪ U, x i = true
  · have hT : ∀ i ∈ T, x i = true := fun i hi => h i (mem_union_left _ hi)
    have hU : ∀ i ∈ U, x i = true := fun i hi => h i (mem_union_right _ hi)
    rw [if_pos hT, if_pos hU, if_pos h, one_mul]
  · have hcopy := h
    push_neg at hcopy
    obtain ⟨i, hi, hxi⟩ := hcopy
    rw [if_neg h]
    rcases mem_union.1 hi with hi' | hi'
    · have h1 : ¬ (∀ j ∈ T, x j = true) := fun hc => hxi (hc i hi')
      rw [if_neg h1, zero_mul]
    · have h1 : ¬ (∀ j ∈ U, x j = true) := fun hc => hxi (hc i hi')
      rw [if_neg h1, mul_zero]

/-- The set of monomials of degree at most `D`. -/
