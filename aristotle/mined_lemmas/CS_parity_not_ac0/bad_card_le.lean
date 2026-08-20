import RequestProject.Basic

/-!
# Unbounded fan-in Boolean circuits, the class `AC⁰`, and `PARITY`

A `Circuit n` is a Boolean circuit on `n` inputs built from constants, input
variables, negations, and *unbounded fan-in* `AND`/`OR` gates.

* `Circuit.depth` counts the maximal number of `AND`/`OR` gates on a root-to-leaf
  path (negations are free, as is standard for `AC⁰`).
* `Circuit.size` counts the number of `AND`/`OR` gates.

`InAC0 f` says that the family `f` is computed by circuits of some fixed depth and
polynomial size.  Making negations free and not counting them in the size only
makes the class larger, hence the lower bound proved later stronger.
-/

namespace CS

/-- Boolean circuits with unbounded fan-in `AND`/`OR` gates. -/
inductive Circuit (n : ℕ) where
  | const : Bool → Circuit n
  | var : Fin n → Circuit n
  | neg : Circuit n → Circuit n
  | or : (m : ℕ) → (Fin m → Circuit n) → Circuit n
  | and : (m : ℕ) → (Fin m → Circuit n) → Circuit n

namespace Circuit

/-- The Boolean function computed by a circuit. -/

lemma bad_card_le {n m : ℕ} (F : Fn n) (bfun : Bits n → Bool) (q : Fin m → Fn n)
    (bs : Fin m → Bits n → Bool)
    (hcorr : ∀ x, (∀ i, q i x = bit (bs i x)) → F x = bit (decide (∃ i, q i x = 1)) →
      F x = bit (bfun x)) :
    ((Finset.univ : Finset (Bits n)).filter (fun x => F x ≠ bit (bfun x))).card ≤
      ((Finset.univ : Finset (Bits n)).filter
        (fun x => F x ≠ bit (decide (∃ i, q i x = 1)))).card +
      ∑ i, ((Finset.univ : Finset (Bits n)).filter (fun x => q i x ≠ bit (bs i x))).card := by
  classical
  have hsub : ((Finset.univ : Finset (Bits n)).filter (fun x => F x ≠ bit (bfun x)))
      ⊆ ((Finset.univ : Finset (Bits n)).filter
          (fun x => F x ≠ bit (decide (∃ i, q i x = 1)))) ∪
        (Finset.univ.biUnion (fun i => (Finset.univ : Finset (Bits n)).filter
          (fun x => q i x ≠ bit (bs i x)))) := by
    intro x hx
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hx
    by_contra hcon
    rw [Finset.mem_union] at hcon
    push_neg at hcon
    obtain ⟨h1', h2'⟩ := hcon
    have h1 : F x = bit (decide (∃ i, q i x = 1)) := by
      by_contra hh
      exact h1' (Finset.mem_filter.2 ⟨Finset.mem_univ x, hh⟩)
    have h2 : ∀ i, q i x = bit (bs i x) := by
      intro i
      by_contra hh
      exact h2' (Finset.mem_biUnion.2
        ⟨i, Finset.mem_univ i, Finset.mem_filter.2 ⟨Finset.mem_univ x, hh⟩⟩)
    exact hx (hcorr x h2 h1)
  calc ((Finset.univ : Finset (Bits n)).filter (fun x => F x ≠ bit (bfun x))).card
      ≤ (((Finset.univ : Finset (Bits n)).filter
          (fun x => F x ≠ bit (decide (∃ i, q i x = 1)))) ∪
        (Finset.univ.biUnion (fun i => (Finset.univ : Finset (Bits n)).filter
          (fun x => q i x ≠ bit (bs i x))))).card := Finset.card_le_card hsub
    _ ≤ ((Finset.univ : Finset (Bits n)).filter
          (fun x => F x ≠ bit (decide (∃ i, q i x = 1)))).card +
        (Finset.univ.biUnion (fun i => (Finset.univ : Finset (Bits n)).filter
          (fun x => q i x ≠ bit (bs i x)))).card := Finset.card_union_le _ _
    _ ≤ _ := Nat.add_le_add_left (Finset.card_biUnion_le) _

/-- **Razborov's approximation lemma**. -/
