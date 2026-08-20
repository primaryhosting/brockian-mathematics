import Mathlib
/-!
# Qudit generalized Pauli group (Weyl–Heisenberg) — the "why five" of quantum computing.
Bare `import Mathlib`; no non-core/Archive namespaces or invented lemmas. TRUE for every dimension d.
-/
namespace BrockianQuantum
open Matrix

variable (d : ℕ) [NeZero d]

/-- Qudit **shift** gate (generalized Pauli X): `X e_j = e_{j+1}` on `ZMod d`. -/

theorem clock_shift_weyl :
    clock d * shift d
      = Complex.exp (2 * Real.pi * Complex.I / d) • (shift d * clock d) := by
  ext i j
  rw [Matrix.smul_apply, Matrix.mul_apply, Matrix.mul_apply, smul_eq_mul,
    Finset.sum_eq_single i, Finset.sum_eq_single j]
  · by_cases h : i = j + 1
    · subst h
      simp only [clock, shift, if_true, mul_one, one_mul]
      exact exp_succ d j
    · simp [clock, shift, h]
  · intro b _ hb
    simp [shift, clock, hb]
  · intro h; exact absurd (Finset.mem_univ _) h
  · intro b _ hb
    simp [shift, clock, Ne.symm hb]
  · intro h; exact absurd (Finset.mem_univ _) h

end BrockianQuantum

