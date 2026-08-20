import Mathlib

/-!
# The no-deleting theorem

We model a finite-dimensional quantum system by `EuclideanSpace ℂ ι` and the tensor product
of two such systems by `EuclideanSpace ℂ (ι × κ)`, with the product state `tens x y` given
by `(tens x y) (i, j) = x i * y j`.

A *deleting machine* would be a unitary `U` acting on (system) ⊗ (system) ⊗ (ancilla) such
that, for every unit state `ψ`,
`U (ψ ⊗ ψ ⊗ a) = ψ ⊗ blank ⊗ a'`,
i.e. the second copy of `ψ` is erased and replaced by a fixed *blank* state, while the
ancilla ends up in a fixed state `a'` (independent of `ψ`).

`QI.no_deleting` shows no such unitary exists.
-/

namespace QI

/-- The product (tensor) of two finite-dimensional state vectors. -/

theorem inner_tens_tens {ι κ : Type*} [Fintype ι] [Fintype κ]
    (x x' : EuclideanSpace ℂ ι) (y y' : EuclideanSpace ℂ κ) :
    inner ℂ (tens x y) (tens x' y') = inner ℂ x x' * inner ℂ y y' := by
  simp only [tens, PiLp.inner_apply, Fintype.sum_prod_type,
    RCLike.inner_apply, map_mul, Finset.sum_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring

/-- The state `|0⟩` of a qubit. -/
