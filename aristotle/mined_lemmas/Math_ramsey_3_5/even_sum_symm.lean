/-
# Ramsey 3 5
Category: Pure Mathematics
Target: Math.ramsey_3_5
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/
import Mathlib

/-!
# Ramsey 3 5
Category: Pure Mathematics
Target: Math.ramsey_3_5
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)

(Lean requires `import` to come first in a file, so the header above the import is a plain
block comment and this is the module docstring with the same content.)

Mathlib does not contain Ramsey numbers, so the whole development is built here:
the recursion `R(3,t+1) ≤ t + R(3,t)`, the parity refinement giving `R(3,4) ≤ 9`,
hence `R(3,5) ≤ 14`, and the circulant graph `C₁₃(1,5)` witnessing `R(3,5) > 13`.
-/

set_option maxHeartbeats 2000000

namespace Math

open Finset

/-! ## The Ramsey property -/

/-- `RamseyProp n s t` says that every simple graph on `n` vertices contains either a clique
of size `s` or an independent set of size `t` (equivalently, a clique of size `t` in the
complement).  `R(s,t)` is the least `n` with this property. -/

theorem even_sum_symm {W : Type} (f : W → W → ℕ) (hs : ∀ x y, f x y = f y x)
    (hd : ∀ x, f x x = 0) (A : Finset W) : Even (∑ v ∈ A, ∑ w ∈ A, f v w) := by
  induction A using Finset.cons_induction with
  | empty => simp
  | cons a B ha ih =>
      simp only [Finset.sum_cons]
      have key : f a a + ∑ w ∈ B, f a w + ∑ x ∈ B, (f x a + ∑ w ∈ B, f x w)
           = 2 * (∑ w ∈ B, f a w) + ∑ x ∈ B, ∑ w ∈ B, f x w := by
        rw [Finset.sum_add_distrib, hd]
        have hswap : ∑ x ∈ B, f x a = ∑ x ∈ B, f a x := Finset.sum_congr rfl (fun x _ => hs x a)
        rw [hswap]; ring
      rw [key]
      exact (even_two_mul _).add ih

/-- `R(3,4) ≤ 9`.  The naive recursion only gives `10`; a parity argument (there is no
`3`-regular graph on `9` vertices) improves the bound to `9`. -/
