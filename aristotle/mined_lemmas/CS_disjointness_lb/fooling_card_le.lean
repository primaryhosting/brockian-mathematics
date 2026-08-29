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

/-
# Disjointness Lb
Category: Frontier Cs
Target: CS.disjointness_lb
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/
import Mathlib

/-!
# Disjointness Lb
Category: Frontier Cs
Target: CS.disjointness_lb
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)

## Contents

We set up two-party communication protocols as protocol trees, and prove the
`Ω(n)` lower bound for the randomized communication complexity of set
disjointness on `n`-element ground sets: any public-coin randomized protocol
which never wrongly claims that two intersecting sets are disjoint, and which
detects disjointness with probability at least `1/2`, must communicate at least
`n - 1` bits (`CS.disjointness_lb`).

The proof combines the classical fooling set `{(S, Sᶜ) : S ⊆ Fin n}` of size
`2 ^ n` for disjointness with an averaging argument over the public random
string.  We also record the matching upper bound `n + 1`
(`CS.disjointness_ub`), which shows in particular that the hypotheses of the
lower bound are satisfiable, and the deterministic lower bound `n`
(`CS.disjointness_deterministic_lb`).

The randomized bound proved here is for protocols with one-sided error (they
never certify disjointness wrongly); the two-sided bounded-error case is
Razborov's theorem and is not covered by this argument.
-/

open Finset

namespace CS

open scoped Classical

/-- A deterministic two-party communication protocol tree.  `alice g L R` means
"Alice sends the bit `g x` and the players continue with `L` (if the bit is
`true`) or `R` (if it is `false`)"; `bob` is the same with Bob speaking. -/
inductive Prot (X Y : Type*) : Type _
  | leaf : Bool → Prot X Y
  | alice : (X → Bool) → Prot X Y → Prot X Y → Prot X Y
  | bob : (Y → Bool) → Prot X Y → Prot X Y → Prot X Y

namespace Prot

variable {X Y : Type*}

/-- The output of the protocol on the input pair `(x, y)`. -/

theorem fooling_card_le {X Y ι : Type*} (A : Finset ι) (x : ι → X) (y : ι → Y)
    (D : X → Y → Prop)
    (hfool : ∀ i ∈ A, ∀ j ∈ A, i ≠ j → ¬ D (x i) (y j) ∨ ¬ D (x j) (y i)) :
    ∀ (P : Prot X Y) (px : X → Prop) (py : Y → Prop) (B : Finset ι), B ⊆ A →
      (∀ i ∈ B, px (x i) ∧ py (y i) ∧ P.run (x i) (y i) = true) →
      (∀ a b, px a → py b → P.run a b = true → D a b) →
      B.card ≤ 2 ^ P.cost := by
  intro P
  induction P with
  | leaf b =>
    intro px py B hBA hB hsound
    cases b with
    | false =>
      have hempty : B = ∅ := by
        by_contra h
        obtain ⟨i, hi⟩ := Finset.nonempty_iff_ne_empty.2 h
        have := (hB i hi).2.2
        simp [Prot.run] at this
      simp [hempty]
    | true =>
      have hcost : (Prot.leaf (X := X) (Y := Y) true).cost = 0 := rfl
      rw [hcost, pow_zero]
      apply Finset.card_le_one.2
      intro i hi j hj
      by_contra hij
      have h1 : D (x i) (y j) := hsound _ _ (hB i hi).1 (hB j hj).2.1 rfl
      have h2 : D (x j) (y i) := hsound _ _ (hB j hj).1 (hB i hi).2.1 rfl
      rcases hfool i (hBA hi) j (hBA hj) hij with h | h
      · exact h h1
      · exact h h2
  | alice g L R ihL ihR =>
    intro px py B hBA hB hsound
    have hL : (∀ a b, (px a ∧ g a = true) → py b → L.run a b = true → D a b) := by
      intro a b ha hb hrun
      exact hsound a b ha.1 hb (by simp [Prot.run, ha.2, hrun])
    have hR : (∀ a b, (px a ∧ g a = false) → py b → R.run a b = true → D a b) := by
      intro a b ha hb hrun
      exact hsound a b ha.1 hb (by simp [Prot.run, ha.2, hrun])
    classical
    set B1 := B.filter (fun i => g (x i) = true) with hB1
    set B2 := B.filter (fun i => g (x i) = false) with hB2
    have hcard : B.card ≤ B1.card + B2.card := by
      refine le_trans (Finset.card_le_card ?_) (Finset.card_union_le B1 B2)
      intro i hi
      rw [Finset.mem_union, hB1, hB2, Finset.mem_filter, Finset.mem_filter]
      by_cases hg : g (x i) = true
      · exact Or.inl ⟨hi, hg⟩
      · exact Or.inr ⟨hi, by simpa using hg⟩
    have h1 : B1.card ≤ 2 ^ L.cost := by
      refine ihL (fun a => px a ∧ g a = true) py B1
        (Finset.Subset.trans (Finset.filter_subset _ _) hBA) ?_ hL
      intro i hi
      rw [hB1, Finset.mem_filter] at hi
      obtain ⟨hiB, hg⟩ := hi
      refine ⟨⟨(hB i hiB).1, hg⟩, (hB i hiB).2.1, ?_⟩
      have := (hB i hiB).2.2
      simpa [Prot.run, hg] using this
    have h2 : B2.card ≤ 2 ^ R.cost := by
      refine ihR (fun a => px a ∧ g a = false) py B2
        (Finset.Subset.trans (Finset.filter_subset _ _) hBA) ?_ hR
      intro i hi
      rw [hB2, Finset.mem_filter] at hi
      obtain ⟨hiB, hg⟩ := hi
      refine ⟨⟨(hB i hiB).1, hg⟩, (hB i hiB).2.1, ?_⟩
      have := (hB i hiB).2.2
      simpa [Prot.run, hg] using this
    have hle : (2:ℕ) ^ L.cost + 2 ^ R.cost ≤ 2 ^ (Prot.alice g L R).cost := by
      have e1 : (2:ℕ) ^ L.cost ≤ 2 ^ (max L.cost R.cost) :=
        Nat.pow_le_pow_right (by norm_num) (le_max_left _ _)
      have e2 : (2:ℕ) ^ R.cost ≤ 2 ^ (max L.cost R.cost) :=
        Nat.pow_le_pow_right (by norm_num) (le_max_right _ _)
      have e3 : (Prot.alice g L R).cost = 1 + max L.cost R.cost := rfl
      rw [e3, pow_add, pow_one]
      omega
    omega
  | bob g L R ihL ihR =>
    intro px py B hBA hB hsound
    have hL : (∀ a b, px a → (py b ∧ g b = true) → L.run a b = true → D a b) := by
      intro a b ha hb hrun
      exact hsound a b ha hb.1 (by simp [Prot.run, hb.2, hrun])
    have hR : (∀ a b, px a → (py b ∧ g b = false) → R.run a b = true → D a b) := by
      intro a b ha hb hrun
      exact hsound a b ha hb.1 (by simp [Prot.run, hb.2, hrun])
    classical
    set B1 := B.filter (fun i => g (y i) = true) with hB1
    set B2 := B.filter (fun i => g (y i) = false) with hB2
    have hcard : B.card ≤ B1.card + B2.card := by
      refine le_trans (Finset.card_le_card ?_) (Finset.card_union_le B1 B2)
      intro i hi
      rw [Finset.mem_union, hB1, hB2, Finset.mem_filter, Finset.mem_filter]
      by_cases hg : g (y i) = true
      · exact Or.inl ⟨hi, hg⟩
      · exact Or.inr ⟨hi, by simpa using hg⟩
    have h1 : B1.card ≤ 2 ^ L.cost := by
      refine ihL px (fun b => py b ∧ g b = true) B1
        (Finset.Subset.trans (Finset.filter_subset _ _) hBA) ?_ hL
      intro i hi
      rw [hB1, Finset.mem_filter] at hi
      obtain ⟨hiB, hg⟩ := hi
      refine ⟨(hB i hiB).1, ⟨(hB i hiB).2.1, hg⟩, ?_⟩
      have := (hB i hiB).2.2
      simpa [Prot.run, hg] using this
    have h2 : B2.card ≤ 2 ^ R.cost := by
      refine ihR px (fun b => py b ∧ g b = false) B2
        (Finset.Subset.trans (Finset.filter_subset _ _) hBA) ?_ hR
      intro i hi
      rw [hB2, Finset.mem_filter] at hi
      obtain ⟨hiB, hg⟩ := hi
      refine ⟨(hB i hiB).1, ⟨(hB i hiB).2.1, hg⟩, ?_⟩
      have := (hB i hiB).2.2
      simpa [Prot.run, hg] using this
    have hle : (2:ℕ) ^ L.cost + 2 ^ R.cost ≤ 2 ^ (Prot.bob g L R).cost := by
      have e1 : (2:ℕ) ^ L.cost ≤ 2 ^ (max L.cost R.cost) :=
        Nat.pow_le_pow_right (by norm_num) (le_max_left _ _)
      have e2 : (2:ℕ) ^ R.cost ≤ 2 ^ (max L.cost R.cost) :=
        Nat.pow_le_pow_right (by norm_num) (le_max_right _ _)
      have e3 : (Prot.bob g L R).cost = 1 + max L.cost R.cost := rfl
      rw [e3, pow_add, pow_one]
      omega
    omega

/-- Two subsets of `Fin n`, given as characteristic vectors, are disjoint. -/
