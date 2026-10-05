/-!
# Erdos Discrepancy
Category: Frontier — Prime Numbers
Target: Frontier.erdos_discrepancy
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

/-
This file is written in plain Lean 4 core (no imports), so that the header comment above
can legally be the very first thing in the file.
-/

namespace Frontier

/-- A `±1` sequence: `f n ∈ {1, -1}` for every index `n ≥ 1`. -/

theorem erdos_discrepancy_uniform (f : Nat → Int) (hf : IsPlusMinusOne f) :
    ∃ d n : Nat, 1 ≤ d ∧ 1 ≤ n ∧ n * d ≤ 12 ∧ 1 < (hapSum f d n).natAbs := by
  apply Classical.byContradiction
  intro hcon
  have h : ∀ d n : Nat, 1 ≤ d → 1 ≤ n → n * d ≤ 12 → (hapSum f d n).natAbs ≤ 1 := by
    intro d n hd hn hnd
    apply Classical.byContradiction
    intro hx
    exact hcon ⟨d, n, hd, hn, hnd, by omega⟩
  -- The doubling relation `f (2d) = - f d`, instantiated at `d = 1, 2, 3, 4, 5, 6`.
  have e2 : f 2 = - f 1 := by
    simpa using neg_of_hapSum_two f hf (d := 1) (by omega) (h 1 2 (by omega) (by omega) (by omega))
  have e4 : f 4 = - f 2 := by
    simpa using neg_of_hapSum_two f hf (d := 2) (by omega) (h 2 2 (by omega) (by omega) (by omega))
  have e6 : f 6 = - f 3 := by
    simpa using neg_of_hapSum_two f hf (d := 3) (by omega) (h 3 2 (by omega) (by omega) (by omega))
  have e8 : f 8 = - f 4 := by
    simpa using neg_of_hapSum_two f hf (d := 4) (by omega) (h 4 2 (by omega) (by omega) (by omega))
  have e10 : f 10 = - f 5 := by
    simpa using neg_of_hapSum_two f hf (d := 5) (by omega) (h 5 2 (by omega) (by omega) (by omega))
  have e12 : f 12 = - f 6 := by
    simpa using neg_of_hapSum_two f hf (d := 6) (by omega) (h 6 2 (by omega) (by omega) (by omega))
  -- Partial sums along `d = 1`.
  have s4 : (f 1 + f 2 + f 3 + f 4).natAbs ≤ 1 := by
    have := h 1 4 (by omega) (by omega) (by omega); simpa [hapSum] using this
  have s6 : (f 1 + f 2 + f 3 + f 4 + f 5 + f 6).natAbs ≤ 1 := by
    have := h 1 6 (by omega) (by omega) (by omega); simpa [hapSum] using this
  have s8 : (f 1 + f 2 + f 3 + f 4 + f 5 + f 6 + f 7 + f 8).natAbs ≤ 1 := by
    have := h 1 8 (by omega) (by omega) (by omega); simpa [hapSum] using this
  have s10 :
      (f 1 + f 2 + f 3 + f 4 + f 5 + f 6 + f 7 + f 8 + f 9 + f 10).natAbs ≤ 1 := by
    have := h 1 10 (by omega) (by omega) (by omega); simpa [hapSum] using this
  have s12 :
      (f 1 + f 2 + f 3 + f 4 + f 5 + f 6 + f 7 + f 8 + f 9 + f 10 + f 11 + f 12).natAbs
        ≤ 1 := by
    have := h 1 12 (by omega) (by omega) (by omega); simpa [hapSum] using this
  -- A partial sum along `d = 2` and one along `d = 3`.
  have u6 : (f 2 + f 4 + f 6 + f 8 + f 10 + f 12).natAbs ≤ 1 := by
    have := h 2 6 (by omega) (by omega) (by omega); simpa [hapSum] using this
  have t4 : (f 3 + f 6 + f 9 + f 12).natAbs ≤ 1 := by
    have := h 3 4 (by omega) (by omega) (by omega); simpa [hapSum] using this
  rcases hf 1 (by omega) with h1 | h1 <;> rcases hf 3 (by omega) with h3 | h3 <;>
    rcases hf 5 (by omega) with h5 | h5 <;> rcases hf 7 (by omega) with h7 | h7 <;>
    rcases hf 9 (by omega) with h9 | h9 <;> rcases hf 11 (by omega) with h11 | h11 <;>
    omega

/-- **Base case of the Erdős discrepancy problem (`C = 1`).**
For every `±1` sequence `f` there are `d, n ≥ 1` such that
`|f d + f (2d) + ⋯ + f (nd)| > 1`; equivalently, no `±1` sequence has discrepancy at
most `1` on homogeneous arithmetic progressions.  This is the `C = 1` instance of the full
statement `Frontier.ErdosDiscrepancyStatement`. -/
