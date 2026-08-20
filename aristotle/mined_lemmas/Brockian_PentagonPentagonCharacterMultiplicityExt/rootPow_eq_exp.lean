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

lemma rootPow_eq_exp (n : ℕ) [NeZero n] (j : ℕ) (k : ZMod n) :
    rootPow n j k = Complex.exp (2 * Real.pi * Complex.I * (j * k.val) / n) := by
  have h : ((j : ZMod n) * k) = ((j * k.val : ℕ) : ZMod n) := by
    push_cast [ZMod.natCast_val, ZMod.ringHom_map_cast]
    simp
  rw [rootPow, h, show ((j * k.val : ℕ) : ZMod n) = ((j * k.val : ℤ) : ZMod n) by push_cast; ring,
    ZMod.stdAddChar_coe]
  push_cast
  ring_nf

/-- The two-dimensional complex representation of `DihedralGroup n` with parameter `j`:
the rotation `r i` acts diagonally by the root of unity `exp (2π I j i / n)` and its inverse,
and the reflections swap the two eigenlines. -/
