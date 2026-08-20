import Mathlib
/-!
# Squarefree count via the Möbius sieve.
Uses Mathlib's `ArithmeticFunction.moebius` (μ). Bare `import Mathlib`; no non-core/Archive
namespaces or invented lemmas.
-/
namespace BrockianSieve
/-- The number of squarefree integers in `[1, x]` equals `∑_{d : d^2 ≤ x} μ(d) ⌊x / d^2⌋`.
(Sanity: `x = 10`: LHS `#{1,2,3,5,6,7,10} = 7`; RHS `= 10 − ⌊10/4⌋ − ⌊10/9⌋ = 10 − 2 − 1 = 7`.)
Proof idea: `μ(d)^2 = ∑_{e^2 ∣ d} μ(e)` (squarefree indicator) summed over `d ≤ x`, then swap
the order of summation grouping by `e`. -/
theorem squarefree_count (x : ℕ) :
    (((Finset.Icc 1 x).filter Squarefree).card : ℤ)
      = ∑ d ∈ (Finset.Icc 1 x).filter (fun d => d ^ 2 ≤ x),
          ArithmeticFunction.moebius d * ((x / d ^ 2 : ℕ) : ℤ) := by
  sorry
end BrockianSieve
