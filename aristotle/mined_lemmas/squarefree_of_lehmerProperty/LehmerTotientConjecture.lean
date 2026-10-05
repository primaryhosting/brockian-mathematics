import Mathlib

/-- `n` has the Lehmer property: `φ n` divides `n - 1`. -/

def LehmerTotientConjecture : Prop :=
  ∀ n : ℕ, 1 < n → LehmerProperty n → Nat.Prime n

/-- Any Lehmer number is squarefree: if `p ^ 2 ∣ n` then `p ∣ φ n ∣ n - 1`,
while also `p ∣ n`, forcing `p ∣ 1`. -/
