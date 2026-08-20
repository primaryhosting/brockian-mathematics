import Mathlib

/-!
# Hückel π-energies of the cycle graph `C n`

The adjacency (Hückel) matrix of the cycle graph `C n` (`n ≥ 3`) has spectrum
`{2 cos (2 π k / n) : k = 0, …, n-1}`, and its characteristic polynomial is
`∏ k, (X - 2 cos (2 π k / n))`.
-/

namespace Chem

open Matrix Polynomial Complex

/-- The primitive `n`-th root of unity `exp (2 π i / n)`. -/

noncomputable def cycleRoot (n : ℕ) : ℂ := Complex.exp (2 * (Real.pi : ℂ) * Complex.I / (n : ℂ))

/-- The `k`-th Hückel π-energy level of the cycle `C n`, in units of the resonance
integral `β` (measured from the Coulomb integral `α`): `2 cos (2 π k / n)`. -/
