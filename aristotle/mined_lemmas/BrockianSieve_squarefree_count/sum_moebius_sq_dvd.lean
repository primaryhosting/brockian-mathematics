import Mathlib
/-!
# Squarefree count via the Möbius sieve.
Uses Mathlib's `ArithmeticFunction.moebius` (μ). Bare `import Mathlib`; no non-core/Archive
namespaces or invented lemmas.
-/
namespace BrockianSieve

open Finset ArithmeticFunction
open scoped ArithmeticFunction.Moebius

/-- `∑_{d ∣ n} μ d = 1` if `n = 1` and `0` otherwise. -/

private lemma sum_moebius_sq_dvd {x n : ℕ} (hn1 : 1 ≤ n) (hnx : n ≤ x) :
    ∑ d ∈ (Finset.Icc 1 x).filter (fun d => d ^ 2 ∣ n), (μ d : ℤ)
      = if Squarefree n then 1 else 0 := by
  have hn : n ≠ 0 := by omega
  obtain ⟨a, b, hab, ha⟩ := Nat.sq_mul_squarefree n
  -- `n = b ^ 2 * a` with `a` squarefree
  have hb0 : b ≠ 0 := by rintro rfl; simp at hab; omega
  have ha0 : a ≠ 0 := by rintro rfl; simp at hab; omega
  have hkey : ∀ d : ℕ, d ^ 2 ∣ n ↔ d ∣ b := fun d => sq_dvd_iff_dvd hn hab.symm ha
  have hset : (Finset.Icc 1 x).filter (fun d => d ^ 2 ∣ n) = b.divisors := by
    ext d
    simp only [Finset.mem_filter, Finset.mem_Icc, Nat.mem_divisors, hkey d]
    constructor
    · rintro ⟨-, hd⟩; exact ⟨hd, hb0⟩
    · rintro ⟨hd, -⟩
      refine ⟨⟨Nat.pos_of_dvd_of_pos hd (Nat.pos_of_ne_zero hb0), ?_⟩, hd⟩
      have hdb : d ≤ b := Nat.le_of_dvd (Nat.pos_of_ne_zero hb0) hd
      have hbn : b ≤ n := by
        calc b ≤ b ^ 2 := by nlinarith [Nat.one_le_iff_ne_zero.mpr hb0]
          _ ≤ b ^ 2 * a := Nat.le_mul_of_pos_right _ (Nat.pos_of_ne_zero ha0)
          _ = n := hab
      omega
  rw [hset, sum_moebius_divisors]
  congr 1
  simp only [eq_iff_iff]
  constructor
  · rintro rfl
    simpa using hab ▸ (by simpa using ha : Squarefree (1 ^ 2 * a))
  · intro hsf
    have hbb : b * b ∣ n := by rw [← hab]; exact ⟨a, by ring⟩
    exact Nat.isUnit_iff.mp (hsf b hbb)

/-- The number of squarefree integers in `[1, x]` equals `∑_{d : d^2 ≤ x} μ(d) ⌊x / d^2⌋`.
(Sanity: `x = 10`: LHS `#{1,2,3,5,6,7,10} = 7`; RHS `= 10 − ⌊10/4⌋ − ⌊10/9⌋ = 10 − 2 − 1 = 7`.)
Proof idea: `μ(d)^2 = ∑_{e^2 ∣ d} μ(e)` (squarefree indicator) summed over `d ≤ x`, then swap
the order of summation grouping by `e`. -/
