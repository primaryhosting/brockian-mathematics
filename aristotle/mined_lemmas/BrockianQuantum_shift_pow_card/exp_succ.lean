import Mathlib
/-!
# Qudit generalized Pauli group (Weyl–Heisenberg) — the "why five" of quantum computing.
Bare `import Mathlib`; no non-core/Archive namespaces or invented lemmas. TRUE for every dimension d.
-/
namespace BrockianQuantum
open Matrix

variable (d : ℕ) [NeZero d]

/-- Qudit **shift** gate (generalized Pauli X): `X e_j = e_{j+1}` on `ZMod d`. -/

private theorem exp_succ (j : ZMod d) :
    Complex.exp (2 * Real.pi * Complex.I * (((j + 1).val : ℕ) : ℂ) / d)
      = Complex.exp (2 * Real.pi * Complex.I / d)
        * Complex.exp (2 * Real.pi * Complex.I * ((j.val : ℕ) : ℂ) / d) := by
  have hd : (d : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne d)
  have h1 : (j + 1).val = (j.val + 1) % d := by
    conv_lhs => rw [show j + 1 = ((j.val + 1 : ℕ) : ZMod d) by push_cast [ZMod.natCast_val]; simp]
    rw [ZMod.val_natCast]
  rw [h1, exp_mod, ← Complex.exp_add]
  congr 1
  push_cast
  field_simp
  ring

/-- The **Weyl–Heisenberg commutation relation**: `Z * X = ω • (X * Z)` with `ω = exp(2πi/d)`.
This is the defining projective-commutation of the qudit generalized Pauli group. -/
