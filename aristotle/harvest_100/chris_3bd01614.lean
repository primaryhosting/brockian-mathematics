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
theorem pigeonhole_hash_card {K V : Type*} [Fintype K] [Fintype V] {n : ℕ}
    (hK : Fintype.card K = n + 1) (hV : Fintype.card V = n) (f : K → V) :
    ∃ a b : K, a ≠ b ∧ f a = f b := by
  -- transport along equivalences `K ≃ Fin (n+1)` and `V ≃ Fin n`
  classical
  obtain ⟨eK⟩ := (Fintype.truncEquivFinOfCardEq (α := K) hK).nonempty
  obtain ⟨eV⟩ := (Fintype.truncEquivFinOfCardEq (α := V) hV).nonempty
  obtain ⟨a, b, hab, hfab⟩ := pigeonhole_hash n (fun i => eV (f (eK.symm i)))
  refine ⟨eK.symm a, eK.symm b, ?_, ?_⟩
  · exact fun h => hab (eK.symm.injective h)
  · exact eV.injective hfab

end CS

/-!
# Pigeonhole Hash
Category: Computer Science
Target: CS.pigeonhole_hash
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

/-
Note on file layout: Lean 4 requires `import` commands to be the very first commands of a
file, and a module docstring `/-! ... -/` counts as a command. Since the mandated header
above must literally begin the file, this module carries no imports and the proof is
developed from the Lean 4 core library only. A Mathlib-based generalisation to arbitrary
finite types is given in `RequestProject/Card.lean`.
-/

namespace CS

/-- `shrink v x` deletes the value `v` from the range of possible values:
values below `v` are kept, values above `v` are shifted down by one. -/
private def shrink (v x : Nat) : Nat := if x < v then x else x - 1

/-- If `x, v < n + 1` and `x ≠ v` then `shrink v x < n`. -/
private theorem shrink_lt {n v x : Nat} (hv : v < n + 1) (hx : x < n + 1) (hne : x ≠ v) :
    shrink v x < n := by
  unfold shrink; split <;> omega

/-- `shrink v` is injective away from `v`. -/
private theorem shrink_inj {v x y : Nat} (hxv : x ≠ v) (hyv : y ≠ v)
    (h : shrink v x = shrink v y) : x = y := by
  unfold shrink at h; split at h <;> split at h <;> omega

/-- **Pigeonhole principle for hash functions.**

Any hash function `f` from an `(n+1)`-element set of keys, `Fin (n + 1)`, to an
`n`-element set of hash values, `Fin n`, has a collision: there are two distinct keys
`a ≠ b` with `f a = f b`.

The proof is by induction on `n`. For `n = 0` the codomain is empty, so no such `f` can be
applied to a key. For the step, if some key other than the last one already collides with
the last key we are done; otherwise no key is mapped to `f last`, so deleting that value
from the codomain turns `f` (restricted to the first `n + 1` keys) into a hash function
`Fin (n + 1) → Fin n`, and the induction hypothesis supplies a collision. -/
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
theorem no_injective_hash (n : Nat) (f : Fin (n + 1) → Fin n) :
    ¬ (∀ a b : Fin (n + 1), f a = f b → a = b) := by
  intro hinj
  obtain ⟨a, b, hab, hfab⟩ := pigeonhole_hash n f
  exact hab (hinj a b hfab)

end CS

