import Mathlib
/-!
# Squarefree count via the Möbius sieve.
Uses Mathlib's `ArithmeticFunction.moebius` (μ). Bare `import Mathlib`; no non-core/Archive
namespaces or invented lemmas.
-/
namespace BrockianSieve

open Finset ArithmeticFunction
open scoped ArithmeticFunction.Moebius

/-- `∑_{d ∣ n} μ d = 1` if `n = 1` and `0` otherwise. -/

private lemma sum_moebius_divisors (n : ℕ) :
    ∑ d ∈ n.divisors, (μ d : ℤ) = if n = 1 then 1 else 0 := by
  have h := congrArg (fun f => f n) (ArithmeticFunction.moebius_mul_coe_zeta)
  simp only [ArithmeticFunction.mul_apply, ArithmeticFunction.one_apply] at h
  rw [Nat.sum_divisorsAntidiagonal
    (f := fun a b => (μ a : ℤ) * ((zeta : ArithmeticFunction ℤ) b))] at h
  rw [← h]
  refine Finset.sum_congr rfl fun d hd => ?_
  simp only [Nat.mem_divisors] at hd
  have hne : n / d ≠ 0 := by
    have hd0 : 0 < d := Nat.pos_of_dvd_of_pos hd.1 (Nat.pos_of_ne_zero hd.2)
    exact Nat.div_ne_zero_iff.mpr ⟨by omega, Nat.le_of_dvd (Nat.pos_of_ne_zero hd.2) hd.1⟩
  simp [ArithmeticFunction.natCoe_apply, ArithmeticFunction.zeta_apply, hne]

/-- If `n = a ^ 2 * b` with `b` squarefree, then `d ^ 2 ∣ n ↔ d ∣ a`. -/
