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

lemma zeta_sum {K : Type*} [Field K] (zeta : K) (p : ℕ) (hp : 0 < p) (hzp : zeta ^ p = 1)
    (t : ℕ) :
    ∑ r ∈ Finset.range p, zeta ^ r * ind K (decide (p ∣ t + (p - r) % p)) = zeta ^ t := by
  classical
  have hu : t % p < p := Nat.mod_lt _ hp
  rw [Finset.sum_eq_single (t % p)]
  · have hd : p ∣ t + (p - t % p) % p := (dvd_shift p t (t % p) hp hu).2 rfl
    rw [decide_eq_true hd]
    simp only [ind_true, mul_one]
    conv_rhs => rw [show t = p * (t / p) + t % p from (Nat.div_add_mod t p).symm]
    rw [pow_add, pow_mul, hzp, one_pow, one_mul]
  · intro r hr hrne
    have hnd : ¬ (p ∣ t + (p - r) % p) := by
      intro hd
      exact hrne ((dvd_shift p t r hp (Finset.mem_range.1 hr)).1 hd)
    rw [decide_eq_false hnd]
    simp
  · intro h
    exact absurd (Finset.mem_range.2 hu) h

/-- **Razborov–Smolensky theorem.**  For distinct primes `p` and `q`, the function `MOD p`
is not computed by any family of polynomial-size, constant-depth circuits with unbounded
fan-in AND, OR, NOT and `MOD q` gates; that is, `MOD p ∉ AC⁰[q]`. -/
