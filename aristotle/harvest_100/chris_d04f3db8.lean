import Mathlib
import RequestProject.Main

/-!
# Link with Mathlib's Ackermann function

The Ackermann function `CS.ack` defined in `RequestProject.Main` agrees with
Mathlib's `ack` from `Mathlib/Computability/Ackermann.lean`. Consequently the
totality statement `CS.ackermann_total` also characterises Mathlib's `ack`.
-/

set_option autoImplicit false

namespace CS

theorem ack_eq_mathlib_ack : ∀ m n : ℕ, CS.ack m n = _root_.ack m n := by
  intro m
  induction m with
  | zero => intro n; simp
  | succ m ihm =>
    intro n
    induction n with
    | zero => simp [ihm]
    | succ n ihn => simp [ihm, ihn]

/-- Mathlib's `ack` is the unique solution of the Ackermann recursion equations. -/
theorem ackGraph_mathlib_ack (m n : ℕ) : AckGraph m n (_root_.ack m n) := by
  rw [← ack_eq_mathlib_ack]
  exact ackGraph_ack m n

end CS

/-!
# Ackermann Total
Category: Computer Science
Target: CS.ackermann_total
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

/-
Note on file layout: Lean 4 requires every `import` command to appear at the very
beginning of a file, before any doc comment. Since the required header above is a
module doc comment, this file carries no imports and is fully self-contained
(only Lean core's `Init` is implicitly available). The companion file
`RequestProject/MathlibLink.lean` does import Mathlib and identifies the
Ackermann function defined here with Mathlib's `ack`
(`Mathlib/Computability/Ackermann.lean`).
-/

set_option relaxedAutoImplicit false
set_option autoImplicit false

namespace CS

/-- The lexicographic order on `ℕ × ℕ` is well-founded; this is what justifies the
Ackermann recursion. -/
theorem lex_wellFounded :
    WellFounded (Prod.Lex (α := Nat) (β := Nat) (· < ·) (· < ·)) :=
  (Prod.lex Nat.lt_wfRel Nat.lt_wfRel).wf

/-- The two-argument Ackermann function, defined by well-founded recursion on the
lexicographic order on `ℕ × ℕ`. -/
def ack : Nat → Nat → Nat
  | 0, n => n + 1
  | m + 1, 0 => ack m 1
  | m + 1, n + 1 => ack m (ack (m + 1) n)
termination_by m n => (m, n)

@[simp] theorem ack_zero (n : Nat) : ack 0 n = n + 1 := by rw [ack]

@[simp] theorem ack_succ_zero (m : Nat) : ack (m + 1) 0 = ack m 1 := by rw [ack]

@[simp] theorem ack_succ_succ (m n : Nat) :
    ack (m + 1) (n + 1) = ack m (ack (m + 1) n) := by rw [ack]

/-- The graph of the Ackermann recursion, given as an inductive relation.
`AckGraph m n v` means: the defining equations of the Ackermann function justify
the value `v` for the arguments `m, n`. -/
inductive AckGraph : Nat → Nat → Nat → Prop
  | zero (n : Nat) : AckGraph 0 n (n + 1)
  | succ_zero {m v : Nat} : AckGraph m 1 v → AckGraph (m + 1) 0 v
  | succ_succ {m n v w : Nat} :
      AckGraph (m + 1) n v → AckGraph m v w → AckGraph (m + 1) (n + 1) w

/-- The first recursive call of the Ackermann recursion decreases the lexicographic
measure. -/
theorem lex_decreasing_succ_zero (m : Nat) :
    Prod.Lex (α := Nat) (β := Nat) (· < ·) (· < ·) (m, 1) (m + 1, 0) :=
  Prod.Lex.left _ _ (Nat.lt_succ_self m)

/-- The inner recursive call of the Ackermann recursion decreases the lexicographic
measure. -/
theorem lex_decreasing_inner (m n : Nat) :
    Prod.Lex (α := Nat) (β := Nat) (· < ·) (· < ·) (m + 1, n) (m + 1, n + 1) :=
  Prod.Lex.right _ (Nat.lt_succ_self n)

/-- The outer recursive call of the Ackermann recursion decreases the lexicographic
measure. -/
theorem lex_decreasing_outer (m n v : Nat) :
    Prod.Lex (α := Nat) (β := Nat) (· < ·) (· < ·) (m, v) (m + 1, n + 1) :=
  Prod.Lex.left _ _ (Nat.lt_succ_self m)

/-- Existence: `ack` satisfies the Ackermann recursion equations at every point. -/
theorem ackGraph_ack : ∀ m n : Nat, AckGraph m n (ack m n) := by
  intro m
  induction m with
  | zero => intro n; simpa using AckGraph.zero n
  | succ m ihm =>
    intro n
    induction n with
    | zero => simpa using AckGraph.succ_zero (ihm 1)
    | succ n ihn =>
      rw [ack_succ_succ]
      exact AckGraph.succ_succ ihn (ihm _)

/-- Uniqueness: any value justified by the Ackermann recursion equations equals
`ack m n`. -/
theorem ackGraph_eq_ack {m n v : Nat} (h : AckGraph m n v) : v = ack m n := by
  induction h with
  | zero n => simp
  | succ_zero _ ih => simpa using ih
  | succ_succ _ _ ih₁ ih₂ => subst ih₁; simpa using ih₂

/-- **The Ackermann function is total.**
For every pair `(m, n) : ℕ × ℕ` there is exactly one value `v` justified by the
Ackermann recursion equations. Equivalently, the recursion — which terminates by
the well-founded lexicographic order on `ℕ × ℕ`, see `CS.lex_wellFounded` —
defines a total function `ℕ → ℕ → ℕ`, namely `CS.ack`. -/
theorem ackermann_total :
    ∀ m n : Nat, ∃ v : Nat, AckGraph m n v ∧ ∀ w : Nat, AckGraph m n w → w = v := by
  intro m n
  exact ⟨ack m n, ackGraph_ack m n, fun _ hw => ackGraph_eq_ack hw⟩

end CS

