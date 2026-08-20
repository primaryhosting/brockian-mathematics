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

theorem Circuit.exists_approx (q : ℕ) [Fact q.Prime] {K : Type*} [Field K] [CharP K q] {n : ℕ}
    (C : Circuit n) (l : ℕ) (hl : 1 ≤ l) :
    ∃ g : Fn K n, g ∈ Deg K n (((q-1)*l)^C.depth) ∧
      2^l * ((univ : Finset (Cube n)).filter (fun x => g x ≠ ind K (C.eval q x))).card
        ≤ C.size * 2^n := by
  classical
  obtain ⟨f, hdeg, hbad⟩ := C.approx_upto (K := K) q l hl C.size le_rfl
  refine ⟨f C.out, hdeg C.out C.out_lt, le_trans (Nat.mul_le_mul_left _ (Finset.card_le_card ?_))
    hbad⟩
  intro x hx
  rw [Finset.mem_filter] at hx ⊢
  exact ⟨hx.1, ⟨C.out, C.out_lt, hx.2⟩⟩

end RS
end CS

import RequestProject.RS.Dimension
import RequestProject.RS.Circuit

/-!
# Smolensky's dimension argument

If a low-degree function `g` computes `x ↦ ζ^(weight x)` on a set `G` of inputs, where `ζ` is a
root of unity different from `1`, then `G` cannot be much bigger than half of the cube.
-/

namespace CS
namespace RS

open Finset

