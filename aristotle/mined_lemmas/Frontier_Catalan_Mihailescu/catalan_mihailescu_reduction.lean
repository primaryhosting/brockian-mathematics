import Mathlib
/-!
# Catalan Mihailescu
Category: Frontier — Prime Numbers
Target: Frontier.Catalan_Mihailescu
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

set_option maxHeartbeats 1000000

namespace Frontier

/-- A *Catalan solution*: a pair of consecutive perfect powers, i.e. natural numbers with
`x ^ p = y ^ q + 1`, all of `x, y, p, q` being at least `2`. -/

theorem catalan_mihailescu_reduction
    (H : ∀ X P Y Q : ℕ, P.Prime → Q.Prime → 3 ≤ X → 3 ≤ Y → X ^ P ≠ Y ^ Q + 1) :
    CatalanMihailescuStatement := by
  intro x p y q hsol
  rcases Nat.lt_or_ge x 3 with hx3 | hx3
  · -- `x = 2` is impossible
    exfalso
    have hx2 : x = 2 := by have := hsol.1; omega
    subst hx2
    exact no_catalan_solution_base_two p y q hsol
  rcases Nat.lt_or_ge y 3 with hy3 | hy3
  · -- `y = 2` gives exactly the known solution
    have hy2 : y = 2 := by have := hsol.2.2.1; omega
    subst hy2
    obtain ⟨hx, hp, hq⟩ := catalan_solution_of_rhs_base_two hsol
    subst hx; subst hp; subst hq
    rfl
  · exfalso
    obtain ⟨X, P, Y, Q, hsol', hP, hQ, hxX, hyY⟩ := catalan_reduce_to_prime_exponents hsol
    exact H X P Y Q hP hQ (by omega) (by omega) hsol'.2.2.2.2

/-! ### An exhaustive check in a finite range -/

instance decidableIsCatalanSolution (x p y q : ℕ) : Decidable (IsCatalanSolution x p y q) := by
  unfold IsCatalanSolution
  infer_instance

set_option synthInstance.maxHeartbeats 1000000 in
set_option synthInstance.maxSize 1000 in
set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000 in
/-- Exhaustive verification: in the range `x, y < 50` and `p, q < 8` the only pair of
consecutive perfect powers is `9 = 3 ^ 2` and `8 = 2 ^ 3`. -/
