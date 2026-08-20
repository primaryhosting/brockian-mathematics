/-!
# Goldbach Wheel K 2 727
Category: Brockian Corpus
Target: Brockian.GoldbachWheelK2_727
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

set_option maxHeartbeats 4000000
set_option maxRecDepth 40000
set_option autoImplicit false

namespace Brockian

/-- Primality of a natural number, spelled out. This is equivalent to `Nat.Prime`; the
equivalence and a Mathlib-phrased restatement are in `RequestProject.Main`. -/

theorem isPrimeB_isPrime {n : Nat} (hn : n ≤ 1520) (h : isPrimeB n = true) : IsPrime n := by
  rw [isPrimeB, Bool.and_eq_true] at h
  obtain ⟨h2, hnd⟩ := h
  have h2 : 2 ≤ n := of_decide_eq_true h2
  refine ⟨h2, fun d hd => ?_⟩
  by_cases hd1 : d = 1
  · exact Or.inl hd1
  by_cases hdn : d = n
  · exact Or.inr hdn
  exfalso
  obtain ⟨e, he⟩ := hd
  have hd0 : d ≠ 0 := by rintro rfl; simp at he; omega
  have he0 : e ≠ 0 := by rintro rfl; simp at he; omega
  have hdle : d ≤ n := Nat.le_of_dvd (by omega) ⟨e, he⟩
  have hcomm : n = e * d := by rw [he, Nat.mul_comm]
  have hele : e ≤ n := Nat.le_of_dvd (by omega) ⟨d, hcomm⟩
  -- the smaller of the two cofactors is at most 38, and divides `n`
  rcases Nat.le_total d e with hle | hle
  · have hdd : d * d ≤ n := by
      calc d * d ≤ d * e := Nat.mul_le_mul_left d hle
        _ = n := he.symm
    have hd38 : d ≤ 38 := by
      by_cases hc : d ≤ 38
      · exact hc
      · have : 39 * 39 ≤ d * d := Nat.mul_le_mul (by omega) (by omega)
        omega
    exact noDivLe_spec 38 n d hnd (by omega) hd38 hdd ⟨e, he⟩
  · have hee : e * e ≤ n := by
      calc e * e ≤ d * e := Nat.mul_le_mul_right e hle
        _ = n := he.symm
    have he38 : e ≤ 38 := by
      by_cases hc : e ≤ 38
      · exact hc
      · have : 39 * 39 ≤ e * e := Nat.mul_le_mul (by omega) (by omega)
        omega
    have he1 : e ≠ 1 := by rintro rfl; omega
    exact noDivLe_spec 38 n e hnd (by omega) he38 hee ⟨d, hcomm⟩

/-- The wheel: a fixed 12-element list of primes. For every even `n` with `4 ≤ n ≤ 2 * 727`,
one of the two Goldbach summands of `n` can be taken from this list. -/
