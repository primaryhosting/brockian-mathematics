import Mathlib

/-!
# Hyperperfect numbers

A σ-number strand coherent with the Superperfect / AlmostPerfect / HarmonicDivisor
modules.

`n` is **k-hyperperfect** when `n = 1 + k·(σ(n) − n − 1)`, equivalently
`k·σ(n) = (k+1)·n + (k−1)`, where `σ` is the sum-of-divisors function.
The case `k = 1` recovers the ordinary perfect numbers.

Hand-verified witnesses:
* σ(6)  = 1+2+3+6           = 12;  1·12 = 2·6 + 0   = 12   ⇒ 6   is 1-hyperperfect (perfect).
* σ(28) = 1+2+4+7+14+28     = 56;  1·56 = 2·28 + 0  = 56   ⇒ 28  is 1-hyperperfect (perfect).
* σ(21) = 1+3+7+21          = 32;  2·32 = 64 = 3·21 + 1    ⇒ 21  is 2-hyperperfect.
* σ(325)= (1+5+25)(1+13)    = 434; 3·434 = 1302 = 4·325+2  ⇒ 325 is 3-hyperperfect.
* σ(12) = 1+2+3+4+6+12      = 28;  2·28 = 56 ≠ 37 = 3·12+1  ⇒ 12  is NOT 2-hyperperfect.
-/

namespace Brockian.Hyperperfect

/-- Sum of divisors σ(n). -/
def sig (n : ℕ) : ℕ := ∑ d ∈ n.divisors, d

/-- `n` is `k`-hyperperfect: `k·σ(n) = (k+1)·n + (k−1)`. -/
def isHyperperfect (k n : ℕ) : Prop := k * sig n = (k + 1) * n + (k - 1)

theorem perfect_6_is_1hyper : isHyperperfect 1 6 := by
  unfold isHyperperfect sig; decide

theorem perfect_28_is_1hyper : isHyperperfect 1 28 := by
  unfold isHyperperfect sig; decide

theorem hyper_21_k2 : isHyperperfect 2 21 := by
  unfold isHyperperfect sig; decide

theorem hyper_325_k3 : isHyperperfect 3 325 := by
  unfold isHyperperfect sig; decide

theorem not_hyper_12_k2 : ¬ isHyperperfect 2 12 := by
  unfold isHyperperfect sig; decide

theorem hyperperfect_examples :
    isHyperperfect 1 6 ∧ isHyperperfect 1 28 ∧ isHyperperfect 2 21 ∧ isHyperperfect 3 325 :=
  ⟨perfect_6_is_1hyper, perfect_28_is_1hyper, hyper_21_k2, hyper_325_k3⟩

end Brockian.Hyperperfect
