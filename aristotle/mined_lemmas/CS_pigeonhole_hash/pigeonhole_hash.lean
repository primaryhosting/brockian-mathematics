import Mathlib
import RequestProject.Main

/-!
# Pigeonhole Hash — generalisation to arbitrary finite types

A Mathlib-based restatement of `CS.pigeonhole_hash` for arbitrary finite key and value
types, derived from the core-library version proved in `RequestProject/Main.lean`.
-/

namespace CS

/-- Any hash function from a set of `n + 1` keys to a set of `n` hash values has a
collision. -/

theorem pigeonhole_hash : ∀ (n : Nat) (f : Fin (n + 1) → Fin n),
    ∃ a b : Fin (n + 1), a ≠ b ∧ f a = f b := by
  intro n
  induction n with
  | zero => intro f; exact absurd (f ⟨0, Nat.zero_lt_succ 0⟩).isLt (Nat.not_lt_zero _)
  | succ n ih =>
    intro f
    let l : Fin (n + 2) := ⟨n + 1, Nat.lt_succ_self _⟩
    by_cases hc : ∃ i : Fin (n + 2), i ≠ l ∧ f i = f l
    · obtain ⟨i, hi, hfi⟩ := hc
      exact ⟨i, l, hi, hfi⟩
    · have hc' : ∀ i : Fin (n + 2), i ≠ l → f i ≠ f l := fun i hi h => hc ⟨i, hi, h⟩
      have hne : ∀ i : Fin (n + 1), (f ⟨i.val, Nat.lt_succ_of_lt i.isLt⟩).val ≠ (f l).val := by
        intro i h
        have hil : (⟨i.val, Nat.lt_succ_of_lt i.isLt⟩ : Fin (n + 2)) ≠ l := by
          intro he
          simp only [l, Fin.mk.injEq] at he
          have := i.isLt
          omega
        exact absurd (Fin.val_inj.mp h) (hc' _ hil)
      let g : Fin (n + 1) → Fin n := fun i =>
        ⟨shrink (f l).val (f ⟨i.val, Nat.lt_succ_of_lt i.isLt⟩).val,
          shrink_lt (f l).isLt (f _).isLt (hne i)⟩
      obtain ⟨a, b, hab, hg⟩ := ih g
      refine ⟨⟨a.val, Nat.lt_succ_of_lt a.isLt⟩, ⟨b.val, Nat.lt_succ_of_lt b.isLt⟩, ?_, ?_⟩
      · intro h
        simp only [Fin.mk.injEq] at h
        exact hab (Fin.val_inj.mp h)
      · have h3 : (g a).val = (g b).val := congrArg Fin.val hg
        simp only [g] at h3
        exact Fin.val_inj.mp (shrink_inj (hne a) (hne b) h3)

/-- Equivalent contrapositive form: no hash function from `Fin (n + 1)` to `Fin n` is
injective. -/
