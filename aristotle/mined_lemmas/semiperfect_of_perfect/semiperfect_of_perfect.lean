import Mathlib

/-- The aliquot sum of `n`: the sum of its proper divisors. -/

theorem semiperfect_of_perfect {n : ℕ} (hn : 0 < n) (h : aliquot n = n) :
    Semiperfect n :=
  ⟨n.properDivisors, Finset.mem_powerset_self _, h⟩

