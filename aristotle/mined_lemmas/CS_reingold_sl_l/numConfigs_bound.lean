import Mathlib
import RequestProject.ReingoldSlL

/-!
## Existence of universal exploration sequences

The hypothesis `CS.HasPolyUES` used in `RequestProject/ReingoldSlL.lean` asks for universal
exploration sequences of *polynomial* length; producing such short sequences is the deep part
of Reingold's theorem and is not formalised.  Here we prove, unconditionally, that universal
exploration sequences of *some* finite length always exist (`CS.exists_ues`).  This shows that
the notion is satisfiable — the only missing ingredient in `CS.HasPolyUES` is the polynomial
length bound.
-/

set_option autoImplicit false

namespace CS

namespace RotGraph

variable {n d : ℕ}

/-- The walk of length `k` only depends on the first `k` offsets. -/

lemma numConfigs_bound {n d T c : ℕ} (hd1 : 1 ≤ d) (hT : T ≤ (n * d + 1) ^ c) :
    n * d * (n * ((T + 1) * 2)) ≤ (n * d + 2) ^ (c + 5) := by
  rcases Nat.eq_zero_or_pos n with hn0 | hn0
  · simp [hn0]
  set B := n * d + 2
  have hB2 : 2 ≤ B := by omega
  have hn : n ≤ B :=
    le_trans (by simpa using Nat.mul_le_mul (le_refl n) hd1) (Nat.le_add_right _ 2)
  have hd : d ≤ B :=
    le_trans (by simpa using Nat.mul_le_mul hn0 (le_refl d)) (Nat.le_add_right _ 2)
  have hpow : (n * d + 1) ^ c ≤ B ^ c := Nat.pow_le_pow_left (by omega) c
  have hone : 1 ≤ B ^ c := Nat.one_le_pow _ _ (by omega)
  have hT' : T + 1 ≤ B ^ (c + 1) := by
    have hBc : B ^ (c + 1) = B ^ c * B := by ring
    calc T + 1 ≤ B ^ c + 1 := by omega
      _ ≤ B ^ c * 2 := by omega
      _ ≤ B ^ c * B := Nat.mul_le_mul_left _ hB2
      _ = B ^ (c + 1) := hBc.symm
  calc n * d * (n * ((T + 1) * 2))
      ≤ B * B * (B * (B ^ (c + 1) * B)) := by
        refine Nat.mul_le_mul (Nat.mul_le_mul hn hd) (Nat.mul_le_mul hn (Nat.mul_le_mul hT' hB2))
    _ = B ^ (c + 5) := by ring

