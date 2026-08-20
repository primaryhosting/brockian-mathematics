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

theorem inner_ket0_ketD : inner ℂ ket0 ketD = (3/5 : ℂ) := by
  simp [ket0, ketD, PiLp.inner_apply, RCLike.inner_apply,
    EuclideanSpace.single_apply]

/-- **No-deleting theorem.** There is no unitary `U` on
(system) ⊗ (system) ⊗ (ancilla) which, for every unit state `ψ`, maps `ψ ⊗ ψ ⊗ a` to
`ψ ⊗ blank ⊗ a'`, where the blank state `blank` and the final ancilla state `a'` do not
depend on `ψ`.  In other words, an unknown quantum state cannot be deleted. -/
