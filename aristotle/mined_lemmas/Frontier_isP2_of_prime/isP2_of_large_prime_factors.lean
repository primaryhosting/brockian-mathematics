import Mathlib

/-!
# Chen Theorem
Category: Frontier — Prime Numbers
Target: Frontier.Chen_theorem
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

/-
Note on the header: Lean 4 requires the `import` commands to come first in a module, so the
prescribed header comment above is placed immediately after `import Mathlib`.

Contents:

* `Frontier.IsP2`, `Frontier.ChenRepresentable`, `Frontier.ChenStatement` : the formal statement
  of Chen's theorem ("every sufficiently large even number is `p + q` with `p` prime and `q`
  having at most two prime factors").
* `Frontier.Chen_base_case` : an unconditional, kernel-checked verification of the conclusion for
  all even `n` with `4 ≤ n ≤ 500`.
* `Frontier.Chen_theorem` : a Lean-checked reduction of the full statement to the sieve statement
  that Chen's method produces (a prime `p` with all prime factors of `n - p` exceeding `n ^ (1/3)`).
* `Frontier.goldbach_implies_chen` : the (easier) reduction of Chen's statement to Goldbach's
  conjecture.
-/

open ArithmeticFunction

namespace Frontier

/-- `q` is an *almost prime of order 2* (a `P₂` number): `q > 1` and `q` has at most two prime
factors counted with multiplicity (`Ω q ≤ 2`), i.e. `q` is a prime or a product of two primes. -/

theorem isP2_of_large_prime_factors {n q : ℕ} (hq1 : 1 < q) (hqn : q ≤ n)
    (h : ∀ r : ℕ, Nat.Prime r → r ∣ q → n < r ^ 3) : IsP2 q := by
  refine ⟨hq1, ?_⟩
  by_contra hc
  push_neg at hc
  rw [ArithmeticFunction.cardFactors_apply] at hc
  have hq0 : q ≠ 0 := by omega
  have hprod : q.primeFactorsList.prod = q := Nat.prod_primeFactorsList hq0
  have hbig : ∀ x ∈ q.primeFactorsList, n < x ^ 3 := fun x hx =>
    h x (Nat.prime_of_mem_primeFactorsList hx) (Nat.dvd_of_mem_primeFactorsList hx)
  have hpos : ∀ x ∈ q.primeFactorsList, 1 ≤ x := fun x hx =>
    (Nat.prime_of_mem_primeFactorsList hx).one_lt.le
  revert hprod hbig hpos hc
  generalize q.primeFactorsList = L
  match L with
  | [] => intro h1; simp at h1
  | [_] => intro h1; simp at h1
  | [_, _] => intro h1; simp at h1
  | (a :: b :: c :: t) =>
      intro _ hprod hbig hpos
      simp only [List.prod_cons] at hprod
      have hta : 1 ≤ t.prod := List.one_le_prod (fun x hx => hpos x (by simp [hx]))
      have h3 := lt_prod_three (n := n) (hbig a (by simp)) (hbig b (by simp)) (hbig c (by simp))
      have habc : a * b * c ≤ a * (b * (c * t.prod)) := by
        calc a * b * c = a * b * c * 1 := by ring
          _ ≤ a * b * c * t.prod := Nat.mul_le_mul_left _ hta
          _ = a * (b * (c * t.prod)) := by ring
      omega

set_option maxHeartbeats 4000000 in
set_option maxRecDepth 20000000 in
/-- Kernel-checked computation: every even `n` with `4 ≤ n ≤ 500` is a sum of two primes, the
smaller one being below `100`. -/
