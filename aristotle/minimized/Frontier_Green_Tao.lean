import Mathlib
/-!
# Green Tao
Category: Frontier — Prime Numbers
Target: Frontier.Green_Tao
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

set_option autoImplicit false

namespace Frontier

/-- `PrimeAP k` says that the primes contain an arithmetic progression of length `k`:
there are `a` and a positive common difference `d` with `a + i * d` prime for all `i < k`. -/

def PrimeAP (k : ℕ) : Prop :=
  ∃ a d : ℕ, 0 < d ∧ ∀ i < k, Nat.Prime (a + i * d)

/-- The full Green–Tao theorem: the primes contain arbitrarily long arithmetic progressions.
This statement is *not* available in Mathlib (a search for Szemerédi-type or Green–Tao
statements turns up only Dirichlet's theorem, `Nat.infinite_setOf_prime_and_modEq`), and it
is not proved here; it is recorded as a `Prop` so that the results below can refer to it. -/

def GreenTaoStatement : Prop := ∀ k : ℕ, PrimeAP k

/-- Shorter progressions are contained in longer ones. -/

theorem PrimeAP.mono {k k' : ℕ} (hk : k ≤ k') (h : PrimeAP k') : PrimeAP k := by
  obtain ⟨a, d, hd, h⟩ := h
  exact ⟨a, d, hd, fun i hi => h i (lt_of_lt_of_le hi hk)⟩

/-- Base case, verified unconditionally: `199, 409, 619, …, 2089` is an arithmetic progression
of ten primes with common difference `210`. -/

theorem primeAP_ten : PrimeAP 10 := by
  refine ⟨199, 210, by norm_num, ?_⟩
  intro i hi
  interval_cases i <;> norm_num

/-- Every progression length up to `10` is unconditionally realised inside the primes. -/

theorem primeAP_of_le_ten {k : ℕ} (hk : k ≤ 10) : PrimeAP k :=
  primeAP_ten.mono hk

/-- **Green–Tao, formalized statement together with a Lean-checked reduction.**

The primes contain arbitrarily long arithmetic progressions *if and only if* they contain
arbitrarily long arithmetic progressions arbitrarily far out (all of whose terms exceed any
prescribed bound `N`).  Thus the seemingly stronger "infinitely often" form of the Green–Tao

theorem is equivalent to the plain form, and proving the plain form for every length `k`
suffices.  The plain form itself is verified here only for lengths `k ≤ 10`
(see `Frontier.primeAP_of_le_ten`); the general case is the Green–Tao theorem, which is not
available in Mathlib. -/
