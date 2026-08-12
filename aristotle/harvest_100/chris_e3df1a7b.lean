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
noncomputable def countUpTo (c : Candidate α) (T : α) : Nat → Nat
  | 0 => 0
  | n + 1 => countUpTo c T n + (if c.lam n ≤ T then 1 else 0)

theorem countUpTo_le_succ (c : Candidate α) (T : α) (n : Nat) :
    countUpTo c T n ≤ countUpTo c T (n + 1) := by
  simp only [countUpTo]
  split <;> omega

/-- The truncated counting function is nondecreasing in the truncation level. -/
theorem countUpTo_mono (c : Candidate α) (T : α) {m n : Nat} (h : m ≤ n) :
    countUpTo c T m ≤ countUpTo c T n := by
  induction h with
  | refl => exact Nat.le_refl _
  | step _ ih => exact Nat.le_trans ih (countUpTo_le_succ c T _)

/-- If the first `n` eigenvalues all lie below the threshold `T`, then the truncated
counting function at level `n` equals `n`. -/
theorem countUpTo_eq_self (c : Candidate α) (T : α) (n : Nat)
    (h : ∀ i, i < n → c.lam i ≤ T) : countUpTo c T n = n := by
  induction n with
  | zero => rfl
  | succ n ih =>
      have hn : countUpTo c T n = n := ih (fun i hi => h i (Nat.lt_succ_of_lt hi))
      simp [countUpTo, hn, h n (Nat.lt_succ_self n)]

/-- `k` is *the* value of the Weyl counting function `N(T)` of the candidate `c`:
the truncated counts are eventually constant equal to `k`. -/
def IsCount (c : Candidate α) (T : α) (k : Nat) : Prop :=
  ∃ K : Nat, ∀ n : Nat, K ≤ n → countUpTo c T n = k

/-- If all eigenvalues from index `N` on exceed `T`, the truncated count at level `N`
is the value of the counting function at `T`. -/
theorem isCount_countUpTo (c : Candidate α) (T : α) (N : Nat)
    (hN : ∀ n : Nat, N ≤ n → T < c.lam n) : IsCount c T (countUpTo c T N) := by
  refine ⟨N, ?_⟩
  intro n hn
  induction hn with
  | refl => rfl
  | @step m h ih =>
      have hm : ¬ (c.lam m ≤ T) := ValueOrder.not_le_of_lt (hN m h)
      simp [countUpTo, hm, ih]

/-- The counting function is well defined: for every threshold `T` only finitely many
eigenvalues lie below `T`, so the truncated counts stabilise. -/
theorem exists_isCount (c : Candidate α) (T : α) : ∃ k, IsCount c T k := by
  obtain ⟨N, hN⟩ := c.lam_unbounded T
  exact ⟨_, isCount_countUpTo c T N hN⟩

/-- The value of the counting function is unique. -/
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
theorem counting_diverges_of_candidate (c : Candidate α) (M : Nat) :
    ∃ T0 : α, ∀ T : α, T0 ≤ T → ∀ k : Nat, IsCount c T k → M ≤ k := by
  refine ⟨c.lam M, fun T hT k hk => ?_⟩
  obtain ⟨K, hK⟩ := hk
  have h1 : countUpTo c T M = M :=
    countUpTo_eq_self c T M fun i hi =>
      ValueOrder.le_trans (c.lam_mono (Nat.le_of_lt hi)) hT
  have h2 : countUpTo c T (max M K) = k := hK _ (Nat.le_max_right _ _)
  have h3 := countUpTo_mono c T (Nat.le_max_left M K)
  omega

end Brockian.Weyl.WeylLawTarget

import Mathlib
import Brockian.Weyl.WeylLawTarget

/-!
# The real-valued form of the Weyl counting divergence

This file instantiates the general development of `Brockian.Weyl.WeylLawTarget` at
`α = ℝ`, identifies the abstract counting function with the cardinality
`#{n | λ n ≤ T}`, and restates the divergence as a `Filter.Tendsto` statement.
-/

open Filter Topology

namespace Brockian.Weyl.WeylLawTarget

instance : ValueOrder ℝ where
  le_trans h₁ h₂ := le_trans h₁ h₂
  not_le_of_lt h hle := absurd h (not_lt_of_ge hle)

/-- A monotone real sequence tending to `+∞` is a candidate spectrum. -/
def Candidate.ofTendsto (lam : ℕ → ℝ) (hmono : Monotone lam)
    (htend : Tendsto lam atTop atTop) : Candidate ℝ where
  lam := lam
  lam_mono h := hmono h
  lam_unbounded T := (htend.eventually_gt_atTop T).exists_forall_of_atTop

/-- The Weyl counting function `N(T)` of a real candidate spectrum. -/
noncomputable def count (c : Candidate ℝ) (T : ℝ) : ℕ :=
  Classical.choose (exists_isCount c T)

theorem isCount_count (c : Candidate ℝ) (T : ℝ) : IsCount c T (count c T) :=
  Classical.choose_spec (exists_isCount c T)

theorem countUpTo_eq_card (c : Candidate ℝ) (T : ℝ) (n : ℕ) :
    countUpTo c T n = ((Finset.range n).filter fun i => c.lam i ≤ T).card := by
  classical
  induction n with
  | zero => simp [countUpTo]
  | succ n ih =>
      rw [Finset.range_add_one, Finset.filter_insert]
      by_cases h : c.lam n ≤ T
      · rw [if_pos h, Finset.card_insert_of_notMem (by simp)]
        simp [countUpTo, ih, h]
      · rw [if_neg h]
        simp [countUpTo, ih, h]

/-- The abstract counting function is the number of eigenvalues below the threshold. -/
theorem count_eq_ncard (c : Candidate ℝ) (T : ℝ) :
    count c T = {n : ℕ | c.lam n ≤ T}.ncard := by
  classical
  obtain ⟨N, hN⟩ := c.lam_unbounded T
  have hset : {n : ℕ | c.lam n ≤ T} = ((Finset.range N).filter fun i => c.lam i ≤ T : Finset ℕ) := by
    ext n
    simp only [Set.mem_setOf_eq, Finset.coe_filter, Finset.mem_range, Set.mem_setOf_eq]
    constructor
    · intro h
      refine ⟨?_, h⟩
      by_contra hlt
      exact absurd h (not_le_of_gt (hN n (le_of_not_gt hlt)))
    · exact fun h => h.2
  have h1 : count c T = countUpTo c T N :=
    isCount_unique c T (isCount_count c T) (isCount_countUpTo c T N hN)
  rw [h1, countUpTo_eq_card, hset, Set.ncard_coe_finset]

/-- **Weyl counting divergence, real form.** For a candidate spectrum of real
eigenvalues, the counting function `N(T) = #{n | λ n ≤ T}` tends to `+∞` as `T → ∞`. -/
theorem tendsto_count_atTop (c : Candidate ℝ) :
    Tendsto (fun T : ℝ => (count c T : ℝ)) atTop atTop := by
  rw [tendsto_atTop]
  intro b
  obtain ⟨M, hM⟩ := exists_nat_ge b
  obtain ⟨T0, hT0⟩ := counting_diverges_of_candidate c M
  refine Filter.eventually_atTop.2 ⟨T0, fun T hT => ?_⟩
  have : M ≤ count c T := hT0 T hT _ (isCount_count c T)
  exact hM.trans (by exact_mod_cast this)

/-- The same statement phrased directly for a monotone real sequence tending to `+∞`:
the number of terms not exceeding `T` diverges as `T → ∞`. -/
theorem tendsto_ncard_atTop (lam : ℕ → ℝ) (hmono : Monotone lam)
    (htend : Tendsto lam atTop atTop) :
    Tendsto (fun T : ℝ => (({n : ℕ | lam n ≤ T}).ncard : ℝ)) atTop atTop := by
  have h := tendsto_count_atTop (Candidate.ofTendsto lam hmono htend)
  simpa [count_eq_ncard, Candidate.ofTendsto] using h

/-- Non-vacuity: `λ n = n` is a candidate spectrum. -/
noncomputable example : Candidate ℝ :=
  Candidate.ofTendsto (fun n : ℕ => (n : ℝ)) (fun _ _ h => by simpa using h)
    tendsto_natCast_atTop_atTop

end Brockian.Weyl.WeylLawTarget

