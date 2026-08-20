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

lemma natCast_pow_q_sub_one (K : Type*) [Field K] (q : ℕ) [Fact q.Prime] [CharP K q] (m : ℕ) :
    ((m : K))^(q-1) = if q ∣ m then 0 else 1 := by
  have hq2 : 2 ≤ q := (Fact.out : q.Prime).two_le
  by_cases h : q ∣ m
  · have h0 : (m : K) = 0 := (CharP.cast_eq_zero_iff K q m).2 h
    rw [if_pos h, h0, zero_pow (by omega)]
  · have h0 : (m : K) ≠ 0 := fun hc => h ((CharP.cast_eq_zero_iff K q m).1 hc)
    have hmod : m ^ q ≡ m [MOD q] := by
      have hz : ((m ^ q : ℕ) : ZMod q) = ((m : ℕ) : ZMod q) := by
        push_cast; exact ZMod.pow_card _
      exact (ZMod.natCast_eq_natCast_iff _ _ _).1 hz
    have hle : m ≤ m ^ q := Nat.le_self_pow (by omega) m
    have hdvd : q ∣ m ^ q - m := (Nat.modEq_iff_dvd' hle).1 hmod.symm
    have hzero : ((m ^ q - m : ℕ) : K) = 0 := (CharP.cast_eq_zero_iff K q _).2 hdvd
    rw [Nat.cast_sub hle] at hzero
    have hf : ((m : K))^q = (m : K) := by
      rw [← Nat.cast_pow]; exact sub_eq_zero.1 hzero
    rw [if_neg h]
    have hq : q = (q - 1) + 1 := by omega
    rw [hq, pow_succ] at hf
    exact mul_right_cancel₀ h0 (hf.trans (one_mul _).symm)

