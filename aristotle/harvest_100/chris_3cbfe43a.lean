import Mathlib

/-!
# Hydra Kirby Paris
Category: Frontier — Set Theory
Target: Frontier.Hydra_Kirby_Paris
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

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

open Ordinal
open scoped NaturalOps

namespace Frontier

/-!
## Part 1: `ω ^ c` is principal for natural (Hessenberg) addition

Mathlib knows that `ω ^ c` is principal for ordinary ordinal addition, but not for the
natural sum `♯`.  We prove this here, since the ordinal assignment used for the hydra
game relies on it.
-/

/-- Every ordinal below `ω ^ d * ω` can be written as `ω ^ d * m + r` with `m` a natural
number and `r < ω ^ d`. -/
theorem exists_decomp (d x : Ordinal) (hx : x < ω ^ d * ω) :
    ∃ (m : ℕ) (r : Ordinal), r < ω ^ d ∧ x = ω ^ d * (m : Ordinal) + r := by
  have hne : (ω : Ordinal) ^ d ≠ 0 := (Ordinal.opow_pos d omega0_pos).ne'
  have hq : x / ω ^ d < ω := (Ordinal.div_lt hne).2 hx
  obtain ⟨m, hm⟩ := Ordinal.lt_omega0.1 hq
  refine ⟨m, x % ω ^ d, Ordinal.mod_lt _ hne, ?_⟩
  rw [← hm]
  exact (Ordinal.div_add_mod x (ω ^ d)).symm

theorem opow_mul_nat_add_lt (d : Ordinal) (m : ℕ) (r : Ordinal) (hr : r < ω ^ d) :
    ω ^ d * (m : Ordinal) + r < ω ^ d * ω := by
  have h1 : ω ^ d * (m : Ordinal) + r < ω ^ d * (m : Ordinal) + ω ^ d :=
    (add_lt_add_iff_left _).2 hr
  have h2 : ω ^ d * (m : Ordinal) + ω ^ d = ω ^ d * ((m : Ordinal) + 1) := by
    rw [mul_add, mul_one]
  have h3 : ω ^ d * ((m : Ordinal) + 1) < ω ^ d * ω := by
    apply mul_lt_mul_of_pos_left _ (Ordinal.opow_pos d omega0_pos)
    have := Ordinal.nat_lt_omega0 (m + 1)
    push_cast at this
    exact this
  exact h1.trans (h2 ▸ h3)

/-- Comparing two base-`ω ^ d` decompositions. -/
theorem decomp_cases (d : Ordinal) (m m' : ℕ) (r r' : Ordinal) (hr : r < ω ^ d)
    (h : ω ^ d * (m' : Ordinal) + r' < ω ^ d * (m : Ordinal) + r) :
    m' < m ∨ (m' = m ∧ r' < r) := by
  rcases lt_trichotomy m' m with hm | hm | hm
  · exact Or.inl hm
  · subst hm
    exact Or.inr ⟨rfl, (add_lt_add_iff_left _).1 h⟩
  · exfalso
    have h1 : ω ^ d * (m : Ordinal) + r < ω ^ d * ((m : Ordinal) + 1) := by
      rw [mul_add, mul_one]; exact (add_lt_add_iff_left _).2 hr
    have h2 : ω ^ d * ((m : Ordinal) + 1) ≤ ω ^ d * (m' : Ordinal) := by
      exact mul_le_mul_right (by exact_mod_cast Nat.succ_le_of_lt hm) _
    have h3 : ω ^ d * (m' : Ordinal) ≤ ω ^ d * (m' : Ordinal) + r' := le_self_add
    exact absurd h (not_lt.2 ((h1.trans_le h2).le.trans h3))

/-- The key merge estimate: natural addition of two ordinals written in base `ω ^ d`
adds the base-`ω ^ d` digits. -/
theorem nadd_decomp_le (d : Ordinal)
    (hd : ∀ x y : Ordinal, x < ω ^ d → y < ω ^ d → x ♯ y < ω ^ d) :
    ∀ a : Ordinal, ∀ b : Ordinal, ∀ (m n : ℕ) (r s : Ordinal), r < ω ^ d → s < ω ^ d →
      a = ω ^ d * (m : Ordinal) + r → b = ω ^ d * (n : Ordinal) + s →
      a ♯ b ≤ ω ^ d * ((m + n : ℕ) : Ordinal) + (r ♯ s) := by
  have step : ∀ (k l : ℕ) (x y : Ordinal), x < ω ^ d → y < ω ^ d → k + 1 ≤ l →
      ω ^ d * ((k : ℕ) : Ordinal) + (x ♯ y) < ω ^ d * ((l : ℕ) : Ordinal) := by
    intro k l x y hx hy hkl
    have h1 : ω ^ d * ((k : ℕ) : Ordinal) + (x ♯ y)
        < ω ^ d * ((k : ℕ) : Ordinal) + ω ^ d := (add_lt_add_iff_left _).2 (hd _ _ hx hy)
    have h2 : ω ^ d * ((k : ℕ) : Ordinal) + ω ^ d = ω ^ d * (((k + 1 : ℕ)) : Ordinal) := by
      push_cast; rw [mul_add, mul_one]
    have h3 : ω ^ d * (((k + 1 : ℕ)) : Ordinal) ≤ ω ^ d * ((l : ℕ) : Ordinal) := by
      exact mul_le_mul_right (by exact_mod_cast hkl) _
    exact h1.trans_le (h2 ▸ h3)
  intro a
  induction a using Ordinal.induction with
  | _ a IHa =>
  intro b
  induction b using Ordinal.induction with
  | _ b IHb =>
  intro m n r s hr hs ha hb
  rw [Ordinal.nadd_le_iff]
  constructor
  · intro a' ha'
    have ha'lt : a' < ω ^ d * ω := ha'.trans_le (le_of_lt (ha ▸ opow_mul_nat_add_lt d m r hr))
    obtain ⟨m', r', hr', rfl⟩ := exists_decomp d a' ha'lt
    have key := IHa _ ha' b m' n r' s hr' hs rfl hb
    rcases decomp_cases d m m' r r' hr (ha ▸ ha') with hlt | ⟨rfl, hrr⟩
    · exact key.trans_lt ((step (m' + n) (m + n) r' s hr' hs (by omega)).trans_le le_self_add)
    · exact key.trans_lt ((add_lt_add_iff_left _).2 (Ordinal.nadd_lt_nadd_right hrr s))
  · intro b' hb'
    have hb'lt : b' < ω ^ d * ω := hb'.trans_le (le_of_lt (hb ▸ opow_mul_nat_add_lt d n s hs))
    obtain ⟨n', s', hs', rfl⟩ := exists_decomp d b' hb'lt
    have key := IHb _ hb' m n' r s' hr hs' ha rfl
    rcases decomp_cases d n n' s s' hs (hb ▸ hb') with hlt | ⟨rfl, hss⟩
    · exact key.trans_lt ((step (m + n') (m + n) r s' hr hs' (by omega)).trans_le le_self_add)
    · exact key.trans_lt ((add_lt_add_iff_left _).2 (Ordinal.nadd_lt_nadd_left hss r))

/-- **The ordinals `ω ^ c` are principal for natural addition.** -/
theorem nadd_lt_opow_omega0 (c : Ordinal) :
    ∀ a b : Ordinal, a < ω ^ c → b < ω ^ c → a ♯ b < ω ^ c := by
  induction c using Ordinal.induction with
  | _ c IH =>
  rcases Ordinal.zero_or_succ_or_isSuccLimit c with rfl | ⟨d, rfl⟩ | hlim
  · intro a b ha hb
    rw [Ordinal.opow_zero, Ordinal.lt_one_iff_zero] at ha hb
    subst ha; subst hb
    simp
  · intro a b ha hb
    rw [Ordinal.opow_succ] at *
    obtain ⟨m, r, hr, rfl⟩ := exists_decomp d a ha
    obtain ⟨n, s, hs, rfl⟩ := exists_decomp d b hb
    have hd : ∀ x y : Ordinal, x < ω ^ d → y < ω ^ d → x ♯ y < ω ^ d :=
      IH d (Order.lt_succ_of_le le_rfl)
    exact (nadd_decomp_le d hd _ _ m n r s hr hs rfl rfl).trans_lt
      (opow_mul_nat_add_lt d (m + n) _ (hd _ _ hr hs))
  · intro a b ha hb
    obtain ⟨d, hd, had⟩ := (Ordinal.lt_opow_of_isSuccLimit (omega0_pos).ne' hlim).1 ha
    obtain ⟨e, he, hbe⟩ := (Ordinal.lt_opow_of_isSuccLimit (omega0_pos).ne' hlim).1 hb
    have h1 : a < ω ^ (max d e) :=
      had.trans_le (Ordinal.opow_le_opow_right omega0_pos (le_max_left d e))
    have h2 : b < ω ^ (max d e) :=
      hbe.trans_le (Ordinal.opow_le_opow_right omega0_pos (le_max_right d e))
    have hlt : max d e < c := max_lt hd he
    exact (IH _ hlt a b h1 h2).trans ((Ordinal.opow_lt_opow_iff_right one_lt_omega0).2 hlt)

/-!
## Part 2: Hydras and the Kirby–Paris game
-/

/-- A hydra is a finite rooted tree: a node carries the (ordered) list of its subtrees.
A *head* of the hydra is a leaf, i.e. a subtree of the form `Hydra.node []`. -/
inductive Hydra : Type
  | node : List Hydra → Hydra

namespace Hydra

-- The ordinal value of a hydra: the natural sum of `ω ^ (value of child)` over its
-- children, defined simultaneously with its list version.
mutual
/-- The ordinal value of a hydra: `Σ♯ ω ^ (value of child)`, a natural (Hessenberg) sum. -/
noncomputable def value : Hydra → Ordinal
  | .node l => listValue l
/-- The natural sum of `ω ^ (value of h)` over the hydras `h` of a list. -/
noncomputable def listValue : List Hydra → Ordinal
  | [] => 0
  | h :: t => (ω ^ value h) ♯ listValue t
end

@[simp] theorem value_node (l : List Hydra) : value (.node l) = listValue l := rfl

@[simp] theorem listValue_nil : listValue [] = 0 := rfl

@[simp] theorem listValue_cons (h : Hydra) (t : List Hydra) :
    listValue (h :: t) = (ω ^ value h) ♯ listValue t := rfl

/-- The single move relation of the Kirby–Paris hydra game: `Step h h'` means that `h'`
arises from `h` by Hercules cutting off one head, followed by the hydra's regrowth.

* `root`: a head attached to the root is removed and nothing grows back;
* `copy`: a head attached to a child `u` of the root is removed, and `n` copies of the
  mutilated `u` are attached to the root (`n` arbitrary — the hydra plays as it likes);
* `deep`: the cut happens strictly inside one of the children, in which case the
  regrowth happens inside that child. -/
inductive Step : Hydra → Hydra → Prop
  | root (a b : List Hydra) :
      Step (.node (a ++ .node [] :: b)) (.node (a ++ b))
  | copy (a b c d : List Hydra) (n : ℕ) :
      Step (.node (a ++ .node (c ++ .node [] :: d) :: b))
        (.node (a ++ (List.replicate n (.node (c ++ d)) ++ b)))
  | deep (a b : List Hydra) (u u' : Hydra) (h : Step u u') :
      Step (.node (a ++ u :: b)) (.node (a ++ u' :: b))

theorem listValue_append (l₁ l₂ : List Hydra) :
    listValue (l₁ ++ l₂) = listValue l₁ ♯ listValue l₂ := by
  induction l₁ with
  | nil => simp [Ordinal.zero_nadd]
  | cons h t ih => simp [ih, Ordinal.nadd_assoc]

theorem listValue_replicate_lt (u : Hydra) (c : Ordinal) (n : ℕ) (h : ω ^ value u < ω ^ c) :
    listValue (List.replicate n u) < ω ^ c := by
  induction n with
  | zero => simpa using Ordinal.opow_pos c omega0_pos
  | succ n ih =>
    rw [List.replicate_succ, listValue_cons]
    exact nadd_lt_opow_omega0 c _ _ h ih

/-- The value of the head `Hydra.node []` is `0`, so a head contributes `ω ^ 0 = 1`. -/
@[simp] theorem value_head : value (.node []) = 0 := rfl

theorem value_lt_of_step {h h' : Hydra} (hs : Step h h') : value h' < value h := by
  induction hs with
  | root a b =>
    simp only [value_node, listValue_append, listValue_cons, listValue_nil, Ordinal.opow_zero,
      Ordinal.one_nadd]
    exact Ordinal.nadd_lt_nadd_left (Order.lt_succ _) _
  | copy a b c d n =>
    have hu : value (.node (c ++ d)) < value (.node (c ++ .node [] :: d)) := by
      simp only [value_node, listValue_append, listValue_cons, listValue_nil, Ordinal.opow_zero,
        Ordinal.one_nadd]
      exact Ordinal.nadd_lt_nadd_left (Order.lt_succ _) _
    have hpow : ω ^ value (Hydra.node (c ++ d))
        < ω ^ value (Hydra.node (c ++ Hydra.node [] :: d)) :=
      (Ordinal.opow_lt_opow_iff_right one_lt_omega0).2 hu
    have hrep : listValue (List.replicate n (Hydra.node (c ++ d)))
        < ω ^ value (Hydra.node (c ++ Hydra.node [] :: d)) :=
      listValue_replicate_lt _ _ n hpow
    simp only [value_node, listValue_append, listValue_cons] at hrep ⊢
    exact Ordinal.nadd_lt_nadd_left (Ordinal.nadd_lt_nadd_right hrep _) _
  | deep a b u u' _ ih =>
    simp only [value_node, listValue_append, listValue_cons]
    exact Ordinal.nadd_lt_nadd_left
      (Ordinal.nadd_lt_nadd_right ((Ordinal.opow_lt_opow_iff_right one_lt_omega0).2 ih) _) _

/-- A living hydra always has a legal move: Hercules can cut off some head.  (This shows
that the termination statement below is not vacuous.) -/
theorem exists_step (h : Hydra) : h = .node [] ∨ ∃ h', Step h h' := by
  refine Hydra.rec (motive_1 := fun u => u = .node [] ∨ ∃ u', Step u u')
    (motive_2 := fun l => l = [] ∨ ∃ l', Step (Hydra.node l) (Hydra.node l')) ?_ ?_ ?_ h
  · rintro l (rfl | ⟨l', hl'⟩)
    · exact Or.inl rfl
    · exact Or.inr ⟨_, hl'⟩
  · exact Or.inl rfl
  · rintro u t (rfl | ⟨u', hu'⟩) _
    · exact Or.inr ⟨t, Step.root [] t⟩
    · exact Or.inr ⟨u' :: t, Step.deep [] t u u' hu'⟩

/-- Example of a move: cutting the single head of the hydra `•—•—•` makes the hydra grow
five new heads at the root. -/
example : Step (.node [.node [.node []]]) (.node (List.replicate 5 (.node []))) :=
  Step.copy [] [] [] [] 5

/-- The move relation of the hydra game is well-founded. -/
theorem step_wf : WellFounded (fun h' h : Hydra => Step h h') :=
  Subrelation.wf (fun {_ _} hs => value_lt_of_step.{0} hs)
    (InvImage.wf value.{0} Ordinal.lt_wf)

end Hydra

/-- **Kirby–Paris hydra theorem.** No matter how Hercules plays and no matter how the
hydra regrows its heads, the game terminates: any play in which Hercules keeps cutting
heads as long as the hydra is alive reaches the dead hydra `Hydra.node []` after
finitely many steps. -/
theorem Hydra_Kirby_Paris (play : ℕ → Hydra)
    (hplay : ∀ t : ℕ, play t ≠ Hydra.node [] → Hydra.Step (play t) (play (t + 1))) :
    ∃ t : ℕ, play t = Hydra.node [] := by
  by_contra hcon
  push_neg at hcon
  have hstep : ∀ t : ℕ, Hydra.Step (play t) (play (t + 1)) := fun t => hplay t (hcon t)
  have key : ∀ o : Ordinal.{0}, ∀ t : ℕ, Hydra.value.{0} (play t) ≠ o := by
    intro o
    induction o using Ordinal.induction with
    | _ o IH =>
      intro t ht
      exact IH (Hydra.value.{0} (play (t + 1)))
        (ht ▸ Hydra.value_lt_of_step.{0} (hstep t)) (t + 1) rfl
  exact key (Hydra.value.{0} (play 0)) 0 rfl

end Frontier

