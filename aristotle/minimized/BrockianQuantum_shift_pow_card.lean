import Mathlib
/-!
# Qudit generalized Pauli group (Weyl–Heisenberg) — the "why five" of quantum computing.
Bare `import Mathlib`; no non-core/Archive namespaces or invented lemmas. TRUE for every dimension d.
-/
namespace BrockianQuantum
open Matrix

variable (d : ℕ) [NeZero d]

/-- Qudit **shift** gate (generalized Pauli X): `X e_j = e_{j+1}` on `ZMod d`. -/

def shift : Matrix (ZMod d) (ZMod d) ℂ := fun i j => if i = j + 1 then 1 else 0

/-- Qudit **clock** gate (generalized Pauli Z): `Z e_j = ω^j e_j`, `ω = exp(2πi/d)`. -/

noncomputable def clock : Matrix (ZMod d) (ZMod d) ℂ :=
  fun i j => if i = j then Complex.exp (2 * Real.pi * Complex.I * (j.val : ℂ) / d) else 0

/-- Entrywise description of the powers of the shift gate: `X ^ n` sends `e_j` to `e_{j+n}`. -/

private theorem shift_pow_apply (n : ℕ) (i j : ZMod d) :
    ((shift d) ^ n) i j = if i = j + (n : ZMod d) then 1 else 0 := by
  induction n generalizing j with
  | zero => simp [Matrix.one_apply]
  | succ n ih =>
    rw [pow_succ, Matrix.mul_apply, Finset.sum_eq_single (j + 1)]
    · rw [ih]
      simp only [shift]
      push_cast
      ring_nf
    · intro b _ hb
      simp only [shift, if_neg hb, mul_zero]
    · intro h; exact absurd (Finset.mem_univ _) h

/-- The shift gate has order dividing `d`: `X ^ d = 1`. -/

theorem shift_pow_card : (shift d) ^ d = 1 := by
  ext i j
  rw [shift_pow_apply, Matrix.one_apply]
  simp

/-- `exp (2πi m / d)` only depends on `m` modulo `d`. -/
