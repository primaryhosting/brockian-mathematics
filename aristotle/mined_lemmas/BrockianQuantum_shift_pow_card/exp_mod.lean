import Mathlib
/-!
# Qudit generalized Pauli group (Weyl–Heisenberg) — the "why five" of quantum computing.
Bare `import Mathlib`; no non-core/Archive namespaces or invented lemmas. TRUE for every dimension d.
-/
namespace BrockianQuantum
open Matrix

variable (d : ℕ) [NeZero d]

/-- Qudit **shift** gate (generalized Pauli X): `X e_j = e_{j+1}` on `ZMod d`. -/

private theorem exp_mod (m : ℕ) :
    Complex.exp (2 * Real.pi * Complex.I * ((m % d : ℕ) : ℂ) / d)
      = Complex.exp (2 * Real.pi * Complex.I * (m : ℂ) / d) := by
  have hd : (d : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne d)
  conv_rhs => rw [show m = d * (m / d) + m % d from (Nat.div_add_mod m d).symm]
  push_cast
  rw [show (2 * (Real.pi : ℂ) * Complex.I * ((d : ℂ) * ((m / d : ℕ) : ℂ) + ((m % d : ℕ) : ℂ)) / d)
      = 2 * (Real.pi : ℂ) * Complex.I * ((m % d : ℕ) : ℂ) / d
        + ((m / d : ℕ) : ℂ) * (2 * (Real.pi : ℂ) * Complex.I) by field_simp; ring]
  rw [Complex.exp_add, Complex.exp_nat_mul]
  simp

/-- Stepping the clock phase: `ω ^ ((j+1).val) = ω * ω ^ (j.val)` with `ω = exp (2πi/d)`. -/
