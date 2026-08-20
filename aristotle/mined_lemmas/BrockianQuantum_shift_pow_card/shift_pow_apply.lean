import Mathlib
/-!
# Qudit generalized Pauli group (Weyl–Heisenberg) — the "why five" of quantum computing.
Bare `import Mathlib`; no non-core/Archive namespaces or invented lemmas. TRUE for every dimension d.
-/
namespace BrockianQuantum
open Matrix

variable (d : ℕ) [NeZero d]

/-- Qudit **shift** gate (generalized Pauli X): `X e_j = e_{j+1}` on `ZMod d`. -/

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
