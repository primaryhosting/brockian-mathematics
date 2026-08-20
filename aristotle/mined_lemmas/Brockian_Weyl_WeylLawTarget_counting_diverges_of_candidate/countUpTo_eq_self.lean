import Mathlib

open scoped BigOperators
open scoped Real
open scoped Nat
open scoped Classical
open scoped Pointwise

set_option maxHeartbeats 8000000
set_option maxRecDepth 4000
set_option synthInstance.maxHeartbeats 20000
set_option synthInstance.maxSize 128

set_option relaxedAutoImplicit false
set_option autoImplicit false

set_option pp.fullNames true
set_option pp.structureInstances true
set_option pp.coercions.types true
set_option pp.funBinderTypes true
set_option pp.letVarTypes true
set_option pp.piBinderTypes true

set_option grind.warning false

/-!
# Counting Diverges Of Candidate
Category: Brockian (Open Discharge)
Target: Brockian.Weyl.WeylLawTarget.counting_diverges_of_candidate
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

/-
This module is deliberately import-free (Lean forbids `import` after a leading module
docstring, and the header above is mandated verbatim), so the small amount of order
theory that is needed is set up by hand below.  The development is fully general: the
eigenvalue type `α` is an arbitrary type carrying `≤` and `<` satisfying the two
`ValueOrder` axioms.  The file `Brockian/Weyl/WeylLawReal.lean` instantiates everything
at `α = ℝ` (using Mathlib) and derives the usual `Filter.Tendsto` form of the statement.
-/

universe u

namespace Brockian.Weyl.WeylLawTarget

/-- The minimal order-theoretic interface used for eigenvalue thresholds:
transitivity of `≤`, and the compatibility of `<` with `≤`. -/
class ValueOrder (α : Type u) [LE α] [LT α] : Prop where
  /-- `≤` is transitive. -/
  le_trans : ∀ {a b c : α}, a ≤ b → b ≤ c → a ≤ c
  /-- `a < b` forbids `b ≤ a`. -/
  not_le_of_lt : ∀ {a b : α}, a < b → ¬ b ≤ a

variable {α : Type u} [LE α] [LT α] [ValueOrder α]

/-- A *candidate spectrum*: a nondecreasing sequence `lam : ℕ → α` of putative
eigenvalues (listed with multiplicity) which is unbounded, i.e. the spectrum
accumulates only at infinity. -/
structure Candidate (α : Type u) [LE α] [LT α] [ValueOrder α] where
  /-- The eigenvalue sequence, in nondecreasing order. -/
  lam : Nat → α
  /-- The eigenvalues are listed in nondecreasing order. -/
  lam_mono : ∀ {m n : Nat}, m ≤ n → lam m ≤ lam n
  /-- Beyond any threshold `T`, all but finitely many eigenvalues exceed `T`. -/
  lam_unbounded : ∀ T : α, ∃ N : Nat, ∀ n : Nat, N ≤ n → T < lam n

open Classical in
/-- `countUpTo c T n` is the number of indices `i < n` with `lam i ≤ T`, i.e. the
partial Weyl counting function truncated to the first `n` eigenvalues. -/

theorem countUpTo_eq_self (c : Candidate α) (T : α) (n : Nat)
    (h : ∀ i, i < n → c.lam i ≤ T) : countUpTo c T n = n := by
  induction n with
  | zero => rfl
  | succ n ih =>
      have hn : countUpTo c T n = n := ih (fun i hi => h i (Nat.lt_succ_of_lt hi))
      simp [countUpTo, hn, h n (Nat.lt_succ_self n)]

/-- `k` is *the* value of the Weyl counting function `N(T)` of the candidate `c`:
the truncated counts are eventually constant equal to `k`. -/
