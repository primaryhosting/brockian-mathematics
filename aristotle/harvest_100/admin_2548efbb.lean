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

namespace Frontier

section Ramsey

variable (c : ℕ → ℕ → Bool)

/-- The elements of `A` strictly above `a` receiving colour `b` (paired with `a`). -/
def branch (A : Set ℕ) (a : ℕ) (b : Bool) : Set ℕ :=
  {x ∈ A | a < x ∧ c a x = b}

/-- The colour chosen at the step starting from `A`: `true` if the `true`-branch is
infinite, `false` otherwise. -/
noncomputable def nextColor (A : Set ℕ) : Bool :=
  if (branch c A (sInf A) true).Infinite then true else false

/-- The next infinite set in the Ramsey construction. -/
noncomputable def nextSet (A : Set ℕ) : Set ℕ :=
  branch c A (sInf A) (nextColor c A)

/-- The sequence of nested infinite sets. -/
noncomputable def ramseySet : ℕ → Set ℕ
  | 0 => Set.univ
  | n + 1 => nextSet c (ramseySet n)

/-- The sequence of witnesses. -/
noncomputable def ramseyElt (n : ℕ) : ℕ := sInf (ramseySet c n)

/-- The colour attached to the `n`-th witness. -/
noncomputable def ramseyColor (n : ℕ) : Bool := nextColor c (ramseySet c n)

theorem nextSet_infinite {A : Set ℕ} (hA : A.Infinite) : (nextSet c A).Infinite := by
  by_cases h : (branch c A (sInf A) true).Infinite
  · simp [nextSet, nextColor, h]
  · have hsplit : {x ∈ A | sInf A < x} ⊆
        branch c A (sInf A) true ∪ branch c A (sInf A) false := by
      rintro x ⟨hx, hlt⟩
      rcases Bool.eq_false_or_eq_true (c (sInf A) x) with hc | hc
      · exact Or.inl ⟨hx, hlt, hc⟩
      · exact Or.inr ⟨hx, hlt, hc⟩
    have hbig : {x ∈ A | sInf A < x}.Infinite := by
      have : A \ {x | x ≤ sInf A} ⊆ {x ∈ A | sInf A < x} := by
        rintro x ⟨hx, hx2⟩
        exact ⟨hx, lt_of_not_ge (by simpa using hx2)⟩
      refine Set.Infinite.mono this ?_
      exact hA.diff (Set.finite_Iic (sInf A))
    have hunion : (branch c A (sInf A) true ∪ branch c A (sInf A) false).Infinite :=
      hbig.mono hsplit
    have := (Set.infinite_union).1 hunion
    rcases this with h' | h'
    · exact absurd h' h
    · simpa [nextSet, nextColor, h] using h'

theorem ramseySet_infinite (n : ℕ) : (ramseySet c n).Infinite := by
  induction n with
  | zero => simpa [ramseySet] using Set.infinite_univ
  | succ n ih => exact nextSet_infinite c ih

theorem ramseyElt_mem (n : ℕ) : ramseyElt c n ∈ ramseySet c n :=
  Nat.sInf_mem (ramseySet_infinite c n).nonempty

theorem ramseySet_succ_subset (n : ℕ) : ramseySet c (n + 1) ⊆ ramseySet c n := by
  intro x hx
  exact hx.1

theorem mem_succ_color {n : ℕ} {x : ℕ} (hx : x ∈ ramseySet c (n + 1)) :
    ramseyElt c n < x ∧ c (ramseyElt c n) x = ramseyColor c n :=
  ⟨hx.2.1, hx.2.2⟩

theorem ramseyElt_strictMono : StrictMono (ramseyElt c) := by
  have hstep : ∀ n, ramseyElt c n < ramseyElt c (n + 1) := by
    intro n
    exact (mem_succ_color c (ramseyElt_mem c (n + 1))).1
  exact strictMono_nat_of_lt_succ hstep

theorem ramseySet_subset_of_le {m n : ℕ} (h : m ≤ n) : ramseySet c n ⊆ ramseySet c m := by
  induction n with
  | zero =>
    have hm : m = 0 := Nat.le_zero.1 h
    subst hm
    exact subset_refl _
  | succ n ih =>
    rcases Nat.lt_or_ge m (n + 1) with hlt | hge
    · exact (ramseySet_succ_subset c n).trans (ih (Nat.lt_succ_iff.1 hlt))
    · have : m = n + 1 := le_antisymm h hge
      subst this
      exact subset_refl _

theorem ramseyElt_color {m n : ℕ} (h : m < n) :
    c (ramseyElt c m) (ramseyElt c n) = ramseyColor c m := by
  have hmem : ramseyElt c n ∈ ramseySet c (m + 1) :=
    ramseySet_subset_of_le c h (ramseyElt_mem c n)
  exact (mem_succ_color c hmem).2

/-- **Infinite Ramsey for pairs, ordered form**: any `2`-colouring `c` of ordered
pairs `i < j` of naturals admits an infinite set on which `c` is constant. -/
theorem infinite_ramsey_lt (c : ℕ → ℕ → Bool) :
    ∃ S : Set ℕ, S.Infinite ∧ ∃ b : Bool, ∀ i ∈ S, ∀ j ∈ S, i < j → c i j = b := by
  have hcol : ∃ b : Bool, {n : ℕ | ramseyColor c n = b}.Infinite := by
    by_contra hcon
    push_neg at hcon
    have h1 := hcon true
    have h0 := hcon false
    have : (Set.univ : Set ℕ).Finite := by
      have hsub : (Set.univ : Set ℕ) ⊆
          {n : ℕ | ramseyColor c n = true} ∪ {n : ℕ | ramseyColor c n = false} := by
        intro n _
        rcases Bool.eq_false_or_eq_true (ramseyColor c n) with h | h
        · exact Or.inl h
        · exact Or.inr h
      exact Set.Finite.subset (h1.union h0) hsub
    exact Set.infinite_univ this
  obtain ⟨b, hb⟩ := hcol
  refine ⟨ramseyElt c '' {n : ℕ | ramseyColor c n = b}, ?_, b, ?_⟩
  · exact hb.image ((ramseyElt_strictMono c).injective.injOn)
  · rintro i ⟨m, hm, rfl⟩ j ⟨n, hn, rfl⟩ hlt
    have hmn : m < n := (ramseyElt_strictMono c).lt_iff_lt.1 hlt
    rw [ramseyElt_color c hmn]
    exact hm

end Ramsey

/-- **Infinite Ramsey theorem for pairs**: every `2`-colouring of the unordered pairs
`[ℕ]²` admits an infinite monochromatic set, i.e. an infinite `S ⊆ ℕ` and a colour `b`
such that every pair of distinct elements of `S` has colour `b`. -/
theorem infinite_ramsey (c : Finset ℕ → Bool) :
    ∃ S : Set ℕ, S.Infinite ∧ ∃ b : Bool, ∀ i ∈ S, ∀ j ∈ S, i ≠ j → c {i, j} = b := by
  obtain ⟨S, hS, b, hb⟩ := infinite_ramsey_lt (fun i j => c {i, j})
  refine ⟨S, hS, b, ?_⟩
  intro i hi j hj hij
  rcases lt_or_gt_of_ne hij with h | h
  · exact hb i hi j hj h
  · have := hb j hj i hi h
    rwa [Finset.pair_comm] at this

end Frontier

#print axioms Frontier.infinite_ramsey
#print axioms Frontier.infinite_ramsey_lt

