import Mathlib
namespace Brockian.KorseltCarmichael
/-- Korselt criterion (hard direction): if n is composite, squarefree, and (p-1) | (n-1) for every
    prime p | n, then n is a Fermat pseudoprime to every base coprime to n: a^n ≡ a (mod n).
    Prove; axiom-clean, no sorry. -/
theorem korselt_carmichael {n : ℕ} (h1 : 1 < n) (hcomp : ¬ n.Prime) (hsqf : Squarefree n)
    (hk : ∀ p : ℕ, p.Prime → p ∣ n → (p - 1) ∣ (n - 1)) :
    ∀ a : ℕ, Nat.Coprime a n → a ^ n ≡ a [MOD n] := by
  sorry
end Brockian.KorseltCarmichael
