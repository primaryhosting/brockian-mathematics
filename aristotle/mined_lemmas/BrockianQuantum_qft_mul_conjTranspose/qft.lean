import Mathlib
/-!
# The quantum Fourier transform on ℤ/d is unitary (up to the normalization d).
Bare `import Mathlib`; may use Mathlib's ZMod additive-character / Gauss-sum machinery. TRUE.
-/
namespace BrockianQuantum
open Matrix

variable (d : ℕ) [NeZero d]

/-- The **quantum Fourier transform** matrix on `ZMod d`: `W j k = ω^{jk}`, `ω = exp(2πi/d)`. -/

noncomputable def qft : Matrix (ZMod d) (ZMod d) ℂ :=
  fun j k => Complex.exp (2 * Real.pi * Complex.I * ((j.val * k.val : ℕ) : ℂ) / d)

/-- The QFT is unitary up to normalization: `W * Wᴴ = d • 1`
(character orthogonality `∑_{k} ω^{(j−l)k} = d·[j = l]`). -/
