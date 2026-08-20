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

theorem isCount_unique (c : Candidate α) (T : α) {k l : Nat}
    (hk : IsCount c T k) (hl : IsCount c T l) : k = l := by
  obtain ⟨K, hK⟩ := hk
  obtain ⟨L, hL⟩ := hl
  have h1 := hK (max K L) (Nat.le_max_left _ _)
  have h2 := hL (max K L) (Nat.le_max_right _ _)
  omega

/-- **The Weyl counting function of a candidate spectrum diverges.**
For every `M` there is a threshold `T₀` such that for all `T ≥ T₀` the counting
function `N(T) = #{n : λ n ≤ T}` satisfies `N(T) ≥ M`; that is, `N(T) → ∞`. -/
