/-
The quantum period-finding subroutine: the state produced by the algorithm,
the measurement distribution of the first register, and the lower bound on the
probability of a "good" measurement outcome.
-/
import Mathlib
import RequestProject.Analysis

open scoped BigOperators
open scoped Real
open scoped Classical

set_option maxHeartbeats 2000000

namespace QI

/-- The primitive `Q`-th root of unity `e^{2πi/Q}` used by the quantum Fourier transform. -/

theorem den_eq_of_cross (s r p q : ℕ) (hs : Nat.Coprime s r) (hp : Nat.Coprime p q)
    (h : s * q = p * r) : q = r := by
  have h1 : r ∣ q := by
    have hd : r ∣ s * q := ⟨p, by rw [h]; ring⟩
    exact Nat.Coprime.dvd_of_dvd_mul_left (Nat.Coprime.symm hs) hd
  have h2 : q ∣ r := by
    have hd : q ∣ p * r := ⟨s, by rw [← h]; ring⟩
    exact Nat.Coprime.dvd_of_dvd_mul_left (Nat.Coprime.symm hp) hd
  exact Nat.dvd_antisymm h2 h1

/-- Two numerators giving the same nearest measurement outcome coincide. -/
