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

lemma exists_root_of_unity (q p : ℕ) [hq : Fact (Nat.Prime q)] (hp : Nat.Prime p) (hpq : p ≠ q) :
    ∃ zeta : AlgebraicClosure (ZMod q), zeta ^ p = 1 ∧ zeta ≠ 1 := by
  have hp2 := hp.two_le
  set K := AlgebraicClosure (ZMod q)
  have hpK : (p : K) ≠ 0 := by
    intro h
    have hd := (CharP.cast_eq_zero_iff K q p).1 h
    exact hpq ((Nat.prime_dvd_prime_iff_eq hq.out hp).1 hd).symm
  set g : K[X] := ∑ i ∈ Finset.range p, X ^ i with hg
  have hcoef : g.coeff (p-1) = 1 := by
    rw [hg, Polynomial.finset_sum_coeff]
    rw [Finset.sum_eq_single (p-1)]
    · simp
    · intro b _ hbne
      rw [Polynomial.coeff_X_pow]
      exact if_neg (by omega)
    · intro h
      exact absurd (Finset.mem_range.2 (by omega)) h
  have hdeg : g.degree ≠ 0 := by
    intro h0
    have hle : p - 1 ≤ g.natDegree :=
      Polynomial.le_natDegree_of_ne_zero (by rw [hcoef]; exact one_ne_zero)
    have hnd : g.natDegree = 0 :=
      Polynomial.natDegree_eq_zero_iff_degree_le_zero.2 (le_of_eq h0)
    omega
  obtain ⟨z, hz⟩ := IsAlgClosed.exists_root g hdeg
  have hzval : ∑ i ∈ Finset.range p, z ^ i = 0 := by
    have h := hz
    rw [Polynomial.IsRoot, hg] at h
    simpa using h
  refine ⟨z, ?_, ?_⟩
  · have h := geom_sum_mul z p
    rw [hzval, zero_mul] at h
    linear_combination -h
  · intro h1
    rw [h1] at hzval
    simp at hzval
    exact hpK (by exact_mod_cast hzval)

section Extension

variable {K : Type*} [Field K] {n j : ℕ}

/-- Extend an input of length `n` by `j` coordinates equal to `true`. -/
