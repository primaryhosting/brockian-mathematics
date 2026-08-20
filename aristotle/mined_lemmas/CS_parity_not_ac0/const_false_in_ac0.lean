import RequestProject.OrApprox

/-!
# Approximating a whole `AC⁰` circuit by a low degree polynomial

Gate by gate (in topological order) we replace each gate by a low degree
function over `ZMod 3`, accumulating an exceptional set of inputs.  A circuit of
depth `d` with `s` gates is approximated by a function of degree `(2ℓ)^d`
outside a set of at most `s · 2^{n-ℓ}` inputs.
-/

namespace CS

open Finset

variable {n : ℕ}

/-- The vector of gate values of a circuit on a given input. -/

theorem const_false_in_ac0 : InAC0 (fun _ _ => false) := by
  refine ⟨0, 0, fun n => ⟨⟨1, fun _ => Gate.const false, ⟨0, by omega⟩, ?_⟩, ?_, ?_, ?_⟩⟩
  · intro i j hj
    simp [Gate.refs] at hj
  · simp
  · exact ⟨fun _ => 0, fun _ => le_refl 0, fun i j hj => by simp [Gate.refs] at hj⟩
  · exact fun x => ⟨fun _ => false, fun i => rfl, rfl⟩

end CS

import RequestProject.Circuits

/-!
# Low degree functions on the Boolean cube over `ZMod 3`

We encode a bit `b` by `sgn b = ±1 ∈ ZMod 3` and consider the monomial functions
`mon S x = ∏ i ∈ S, sgn (x i)`.  Since `sgn b ^ 2 = 1`, these `2 ^ n` functions
span the whole space of functions `Cube n → ZMod 3`, and multiplication of
monomials corresponds to symmetric difference of index sets.

`Deg n D` is the space of functions spanned by monomials of degree at most `D`;
it plays the role of "polynomials of total degree ≤ D" over the cube.
-/

namespace CS

open Finset

instance : Fact (Nat.Prime 3) := ⟨by norm_num⟩

variable {n : ℕ}

/-- The `±1` encoding of a bit inside `ZMod 3`. -/
