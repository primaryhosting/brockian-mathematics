import Mathlib
open Matrix
namespace QuantumInfoII

/-- Pauli matrices and the unnormalized Hadamard `M = √2·H`, over ℤ. -/

theorem chsh_classical_bound (a0 a1 b0 b1 : ℤ)
    (ha0 : a0 = 1 ∨ a0 = -1) (ha1 : a1 = 1 ∨ a1 = -1)
    (hb0 : b0 = 1 ∨ b0 = -1) (hb1 : b1 = 1 ∨ b1 = -1) :
    a0*b0 + a0*b1 + a1*b0 - a1*b1 ≤ 2 ∧ -2 ≤ a0*b0 + a0*b1 + a1*b0 - a1*b1 := by
  rcases ha0 with h0 | h0 <;> rcases ha1 with h1 | h1 <;>
    rcases hb0 with h2 | h2 <;> rcases hb1 with h3 | h3 <;>
    subst h0 <;> subst h1 <;> subst h2 <;> subst h3 <;> norm_num

end QuantumInfoII

