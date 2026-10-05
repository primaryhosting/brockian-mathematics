import RequestProject.Circuits
import RequestProject.LowDegree

/-!
# MOD_p is not approximable by low degree functions over a field of characteristic q

This is the second half of Smolensky's argument: if the function `x ↦ ζ^{|x|}`
(`ζ` a primitive `p`-th root of unity in a field `F` of characteristic `q`) agrees
with a function of degree `D` on a set `G` of inputs, then `G` is small.
-/

namespace CS

open Finset

open scoped Classical

variable {F : Type*} [Field F] {n : ℕ}

/-- The monomial `∏_{i ∈ S} ζ^{x_i}` in the transformed variables. -/

def AC0mod (q : ℕ) (F : ∀ n, (Fin n → Bool) → Bool) : Prop :=
  ∃ (d c : ℕ) (C : ∀ n, Circuit n),
    (∀ n, (C n).depth ≤ d) ∧ (∀ n, (C n).size ≤ n ^ c + c) ∧
      ∀ n x, (C n).eval q x = F n x

end CS

import Mathlib

/-!
# Low degree functions on the Boolean cube

We work with the `F`-algebra of functions from the Boolean cube `Fin n → Bool` to a
field `F`, and with the subspaces `LD F n D` spanned by the multilinear monomials of
degree at most `D`.  This replaces multivariate polynomials: since we only ever care
about the *values* of polynomials on the cube, working with the spanned function
spaces directly is more convenient.
-/

namespace CS

open Finset

open scoped Classical

variable {F : Type*} [Field F] {n : ℕ}

/-- A boolean, as an element of `F`. -/
