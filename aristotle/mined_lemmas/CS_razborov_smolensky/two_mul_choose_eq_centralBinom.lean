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

import Mathlib
import RequestProject.RS.Degree

/-!
# Probabilistic polynomial approximation of `AC⁰[q]` circuits

The Razborov–Smolensky approximation lemma: a circuit of size `s` and depth `d` over
`{¬, ∧, ∨, MOD q}` can be approximated over a field of characteristic `q` by a function of
degree `(ℓ (q-1))^d` which errs on at most `s · 2^(n-ℓ)` inputs.
-/

set_option maxHeartbeats 1000000

namespace CS

open Finset

variable {F : Type*} [Field F] {n q : ℕ}

/-- The set of inputs on which `g` differs from the Boolean function `h`. -/

lemma two_mul_choose_eq_centralBinom (m : ℕ) :
    2 * (2 * m + 1).choose m = Nat.centralBinom (m + 1) := by
  have h : (2 * (m + 1)).choose (m + 1) = (2 * m + 1).choose m + (2 * m + 1).choose (m + 1) := by
    have h' : 2 * (m + 1) = (2 * m + 1) + 1 := by ring
    rw [h', Nat.choose_succ_succ]
  have hsymm : (2 * m + 1).choose (m + 1) = (2 * m + 1).choose m := by
    have := Nat.choose_symm (n := 2 * m + 1) (k := m + 1) (by omega)
    simpa [show 2 * m + 1 - (m + 1) = m by omega] using this.symm
  rw [Nat.centralBinom, h, hsymm]
  ring

end CS

import Mathlib
import RequestProject.RS.Circuits
import RequestProject.RS.Counting

/-!
# Low degree functions on the Boolean cube

We work with functions `Cube n → F` for a field `F`, and define `Deg F n k` to be the
`F`-subspace spanned by the multilinear monomials `∏ i ∈ A, x i` with `#A ≤ k`.

The main result of this file is `CS.card_le_of_approx`: Smolensky's dimension argument.
-/

namespace CS

open Finset

variable {F : Type*} [Field F] {n : ℕ}

/-- `boolF b` is `1` if `b` is true and `0` otherwise. -/
