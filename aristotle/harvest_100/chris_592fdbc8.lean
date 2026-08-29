import Mathlib

/-!
# Pell's equation `x² - 6·y² = 1`: infinitely many solutions

This file complements `RequestProject/Main.lean` (which contains the target
statement `Math.pell_6`) with the Mathlib-based development of the same
equation: iterating the fundamental automorphism attached to the fundamental
solution `(5, 2)` produces infinitely many integer solutions.
-/

namespace Math

/-- Multiplication by the fundamental unit `5 + 2√6`, in coordinates:
`(x, y) ↦ (5x + 12y, 2x + 5y)`. -/
def pellStep (p : ℤ × ℤ) : ℤ × ℤ := (5 * p.1 + 12 * p.2, 2 * p.1 + 5 * p.2)

/-- The sequence of solutions obtained by iterating `pellStep` from `(1, 0)`. -/
def pellSol : ℕ → ℤ × ℤ
  | 0 => (1, 0)
  | n + 1 => pellStep (pellSol n)

@[simp] theorem pellSol_zero : pellSol 0 = (1, 0) := rfl

@[simp] theorem pellSol_succ (n : ℕ) : pellSol (n + 1) = pellStep (pellSol n) := rfl

/-- `pellStep` preserves the Pell form `x² - 6y²`. -/
theorem pellStep_form (p : ℤ × ℤ) :
    (pellStep p).1 ^ 2 - 6 * (pellStep p).2 ^ 2 = p.1 ^ 2 - 6 * p.2 ^ 2 := by
  simp only [pellStep]
  ring

/-- Every term of `pellSol` solves `x² - 6y² = 1`. -/
theorem pellSol_form (n : ℕ) : (pellSol n).1 ^ 2 - 6 * (pellSol n).2 ^ 2 = 1 := by
  induction n with
  | zero => norm_num
  | succ n ih => rw [pellSol_succ, pellStep_form, ih]

/-- The coordinates of `pellSol n` are nonnegative, with first coordinate at least `1`. -/
theorem pellSol_nonneg (n : ℕ) : 1 ≤ (pellSol n).1 ∧ 0 ≤ (pellSol n).2 := by
  induction n with
  | zero => norm_num
  | succ n ih =>
    obtain ⟨h1, h2⟩ := ih
    constructor <;> simp only [pellSol_succ, pellStep] <;> omega

/-- The second coordinates of `pellSol` are strictly increasing. -/
theorem pellSol_snd_strictMono : StrictMono fun n => (pellSol n).2 := by
  refine strictMono_nat_of_lt_succ fun n => ?_
  obtain ⟨h1, h2⟩ := pellSol_nonneg n
  simp only [pellSol_succ, pellStep]
  omega

theorem pellSol_injective : Function.Injective pellSol := by
  intro m n h
  exact pellSol_snd_strictMono.injective (congrArg Prod.snd h)

/-- There are infinitely many integer solutions of `x² - 6y² = 1`. -/
theorem pell_6_solutions_infinite :
    {p : ℤ × ℤ | p.1 ^ 2 - 6 * p.2 ^ 2 = 1}.Infinite :=
  Set.infinite_of_injective_forall_mem pellSol_injective (fun n => pellSol_form n)

/-- The `n`-th solution has second coordinate at least `n`. -/
theorem pellSol_snd_ge (n : ℕ) : (n : ℤ) ≤ (pellSol n).2 := by
  induction n with
  | zero => simp
  | succ k ih =>
    have := pellSol_nonneg k
    push_cast
    simp only [pellSol_succ, pellStep]
    omega

/-- There are solutions with arbitrarily large `y`. -/
theorem pell_6_large (N : ℤ) : ∃ x y : ℤ, x ^ 2 - 6 * y ^ 2 = 1 ∧ N < y := by
  obtain ⟨n, hn⟩ := exists_nat_gt N
  exact ⟨(pellSol n).1, (pellSol n).2, pellSol_form n, lt_of_lt_of_le hn (pellSol_snd_ge n)⟩

end Math

/-!
# Pell 6
Category: Pure Mathematics
Target: Math.pell_6
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace Math

/-- **Pell's equation for `d = 6`.**
`x² - 6·y² = 1` has a nontrivial integer solution, i.e. one with `y ≠ 0`
(so `x ≠ ±1`): take `x = 5`, `y = 2`, since `25 - 24 = 1`.

(The header comment required for this file must be the very first thing in the
file, and Lean requires `import` commands to precede all other syntax, so the
statement is phrased with core Lean's `Int` rather than the Mathlib notation
`ℤ`; the two are the same type.) -/
theorem pell_6 : ∃ x y : Int, x ^ 2 - 6 * y ^ 2 = 1 ∧ y ≠ 0 :=
  ⟨5, 2, by decide, by decide⟩

/-- A sharper form of the same fact: there is a solution with `x > 1` and `y > 0`. -/
theorem pell_6_pos : ∃ x y : Int, x ^ 2 - 6 * y ^ 2 = 1 ∧ 1 < x ∧ 0 < y :=
  ⟨5, 2, by decide, by decide, by decide⟩

end Math

