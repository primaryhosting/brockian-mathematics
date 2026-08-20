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

lemma Deg_top : Deg K n n = ⊤ := by
  classical
  rw [eq_top_iff]
  rintro f -
  have hdelta : ∀ y : Cube n, (fun x : Cube n => if x = y then (1 : K) else 0) ∈ Deg K n n := by
    intro y
    have hfac : (fun x : Cube n => if x = y then (1 : K) else 0)
        = ∏ i : Fin n, (fun x : Cube n => if x i = y i then (1 : K) else 0) := by
      funext x
      rw [Finset.prod_apply]
      by_cases hx : x = y
      · subst hx; simp
      · have hex : ∃ i, x i ≠ y i := by
          by_contra hc
          push_neg at hc
          exact hx (funext hc)
        obtain ⟨i, hi⟩ := hex
        rw [if_neg hx]
        exact (Finset.prod_eq_zero (Finset.mem_univ i) (by simp [hi])).symm
    rw [hfac]
    have hcoord : ∀ i : Fin n, (fun x : Cube n => if x i = y i then (1 : K) else 0) ∈ Deg K n 1 := by
      intro i
      cases hyi : y i
      · have he : (fun x : Cube n => if x i = false then (1 : K) else 0)
            = (fun _ => (1:K)) - (fun x : Cube n => ind K (x i)) := by
          funext x; cases hxi : x i <;> simp [ind, hxi]
        rw [he]
        exact Submodule.sub_mem _ (const_mem_Deg 1 1) (coord_mem_Deg i)
      · have he : (fun x : Cube n => if x i = true then (1 : K) else 0)
            = (fun x : Cube n => ind K (x i)) := by
          funext x; cases x i <;> simp [ind]
        rw [he]
        exact coord_mem_Deg i
    have hp := prod_mem_Deg' (Finset.univ : Finset (Fin n))
      (fun i => (fun x : Cube n => if x i = y i then (1 : K) else 0)) 1 (fun i _ => hcoord i)
    simpa using hp
  have hf : f = ∑ y : Cube n, (f y) • (fun x : Cube n => if x = y then (1 : K) else 0) := by
    funext x
    rw [Finset.sum_apply]
    rw [Finset.sum_eq_single x]
    · simp
    · intro b _ hb
      simp [Ne.symm hb]
    · intro h; exact absurd (Finset.mem_univ x) h
  rw [hf]
  exact Submodule.sum_mem _ (fun y _ => Submodule.smul_mem _ _ (hdelta y))

end RS
end CS

import RequestProject.RS.Approx

/-!
# Gate-by-gate approximation of a circuit

`gate_step` shows that, given approximations of all gates below gate `i` which are correct on a
set `A` of inputs, gate `i` itself can be approximated by a function of degree `((q-1)*ℓ)^(depth)`
which is wrong on at most `2^n / 2^ℓ` of the inputs in `A`.
-/

namespace CS
namespace RS

open Finset
open scoped Classical

variable {K : Type*} [Field K] {n : ℕ}

