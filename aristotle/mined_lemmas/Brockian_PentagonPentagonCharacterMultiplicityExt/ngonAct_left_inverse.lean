import RequestProject.PentagonExt

/-!
# Decomposition of the vertex representation of a regular `n`-gon, `n` odd

For an odd number of vertices `n = 2m+1`, the permutation character of `DihedralGroup n`
acting on the vertices of the regular `n`-gon decomposes as the trivial character plus the
`m` two-dimensional characters `rotChar n 1, …, rotChar n m`.

For `n = 5` this is the classical pentagon statement `5 = 1 + 2 + 2`.
-/

open Finset

namespace Brockian

open DihedralGroup

variable {n : ℕ}

/-- For an odd `n`-gon every reflection fixes exactly one vertex. -/

lemma ngonAct_left_inverse (g : DihedralGroup n) (x : ZMod n) :
    ngonAct n g⁻¹ (ngonAct n g x) = x := by
  rw [← ngonAct_mul, inv_mul_cancel, ngonAct_one]

/-- The vertex action of the dihedral group, as a homomorphism into the permutations
of the vertex set. -/
