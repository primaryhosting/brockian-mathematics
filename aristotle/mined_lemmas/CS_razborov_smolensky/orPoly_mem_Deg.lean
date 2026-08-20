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

lemma orPoly_mem_Deg (q : ℕ) {K : Type*} [Field K] {n m l E : ℕ} (S : Fin l → Finset (Fin m))
    (u : Fin m → Fn K n) (hu : ∀ t, u t ∈ Deg K n E) :
    orPoly q S u ∈ Deg K n (l * ((q - 1) * E)) := by
  classical
  have hfac : ∀ k : Fin l,
      (fun x => (1 : K) - (∑ t ∈ S k, u t x)^(q-1)) ∈ Deg K n ((q-1) * E) := by
    intro k
    have hsum : (fun x => ∑ t ∈ S k, u t x) ∈ Deg K n E := by
      have : (fun x => ∑ t ∈ S k, u t x) = ∑ t ∈ S k, u t := by
        funext x; rw [Finset.sum_apply]
      rw [this]
      exact Submodule.sum_mem _ (fun t _ => hu t)
    have hpow : (fun x => (∑ t ∈ S k, u t x)^(q-1)) ∈ Deg K n ((q-1) * E) := by
      have := pow_mem_Deg (q-1) hsum
      have hrw : (fun x => ∑ t ∈ S k, u t x)^(q-1) = (fun x => (∑ t ∈ S k, u t x)^(q-1)) := by
        funext x; rw [Pi.pow_apply]
      rwa [hrw] at this
    exact Submodule.sub_mem _ (const_mem_Deg 1 _) hpow
  have hprod : (fun x => ∏ k : Fin l, ((1 : K) - (∑ t ∈ S k, u t x)^(q-1)))
      ∈ Deg K n (l * ((q-1) * E)) := by
    have hrw : (fun x => ∏ k : Fin l, ((1 : K) - (∑ t ∈ S k, u t x)^(q-1)))
        = ∏ k : Fin l, (fun x => (1 : K) - (∑ t ∈ S k, u t x)^(q-1)) := by
      funext x; rw [Finset.prod_apply]
    rw [hrw]
    have := prod_mem_Deg' (Finset.univ : Finset (Fin l))
      (fun k => (fun x => (1 : K) - (∑ t ∈ S k, u t x)^(q-1))) ((q-1)*E) (fun k _ => hfac k)
    simpa using this
  have : orPoly q S u = (fun _ => (1:K)) - (fun x => ∏ k : Fin l, ((1 : K) - (∑ t ∈ S k, u t x)^(q-1))) := by
    funext x; simp [orPoly]
  rw [this]
  exact Submodule.sub_mem _ (const_mem_Deg 1 _) hprod

end RS
end CS

import Mathlib

/-!
# Low-degree functions on the Boolean cube

We work with functions from the Boolean cube `Fin n → Bool` to a field `K`, and define
the submodule `Deg K n D` of functions of "degree at most `D`", namely the `K`-span of the
multilinear monomials `x ↦ ∏ i ∈ T, x i` with `#T ≤ D`.
-/

namespace CS
namespace RS

open Finset

/-- The Boolean cube on `n` coordinates. -/
abbrev Cube (n : ℕ) := Fin n → Bool

/-- Functions from the Boolean cube to `K`. -/
abbrev Fn (K : Type*) (n : ℕ) := Cube n → K

variable {K : Type*} [Field K] {n : ℕ}

/-- The indicator of a Boolean value inside a field. -/
