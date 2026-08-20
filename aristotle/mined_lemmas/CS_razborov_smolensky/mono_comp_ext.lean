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

lemma mono_comp_ext (T : Finset (Fin (n+j))) (x : Cube n) :
    mono K T (ext n j x)
      = mono K (univ.filter (fun a : Fin n => Fin.castAdd j a ∈ T)) x := by
  classical
  set y : Cube (n+j) := ext n j x with hy
  set T'' := (univ.filter (fun a : Fin n => Fin.castAdd j a ∈ T)).image (Fin.castAdd j) with hT''
  have hsub : T'' ⊆ T := by
    intro i hi
    rw [hT''] at hi
    obtain ⟨a, ha, rfl⟩ := Finset.mem_image.1 hi
    exact (Finset.mem_filter.1 ha).2
  have h1 : mono K T y = ∏ i ∈ T, ind K (y i) := rfl
  rw [h1, ← Finset.prod_sdiff hsub]
  have hrest : ∏ i ∈ T \ T'', ind K (y i) = 1 := by
    refine Finset.prod_eq_one (fun i hi => ?_)
    rw [Finset.mem_sdiff] at hi
    refine Fin.addCases (motive := fun i => i ∈ T → i ∉ T'' → ind K (y i) = 1) ?_ ?_ i hi.1 hi.2
    · intro a haT haT''
      exact absurd (Finset.mem_image.2 ⟨a, Finset.mem_filter.2 ⟨Finset.mem_univ a, haT⟩, rfl⟩) haT''
    · intro b _ _
      rw [hy, ext, Fin.append_right]
      simp [ind]
  rw [hrest, one_mul, hT'', Finset.prod_image (fun a _ b _ h => Fin.castAdd_injective _ _ h)]
  show ∏ a ∈ univ.filter (fun a : Fin n => Fin.castAdd j a ∈ T), ind K (y (Fin.castAdd j a))
      = ∏ a ∈ univ.filter (fun a : Fin n => Fin.castAdd j a ∈ T), ind K (x a)
  refine Finset.prod_congr rfl (fun a _ => ?_)
  rw [hy, ext_left]

/-- Restricting to the subcube where the last `j` coordinates are `1` preserves low degree. -/
