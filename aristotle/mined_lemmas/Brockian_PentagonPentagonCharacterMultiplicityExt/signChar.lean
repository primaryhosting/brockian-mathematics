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

def signChar (n : ℕ) : DihedralGroup n → ℝ
  | DihedralGroup.r _ => 1
  | DihedralGroup.sr _ => -1

/-- The character of the two-dimensional rotation representation with parameter `j`:
it takes the value `2 cos (2π j i / n)` on the rotation `r i` and `0` on every reflection. -/
