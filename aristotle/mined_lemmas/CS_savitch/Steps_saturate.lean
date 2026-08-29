/-
# Savitch
Category: Frontier Cs
Target: CS.savitch
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/
import Mathlib

/-!
# Savitch
Category: Frontier Cs
Target: CS.savitch
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)

(The header above is repeated as a module docstring: Lean 4 requires `import` lines to come
first, so the very first comment of the file cannot be a module docstring.)

This file develops space bounded machines, proves Savitch's theorem
`NSPACE f ⊆ DSPACE (f ^ 2)` and deduces `PSPACE = NPSPACE`.
-/

set_option autoImplicit false

namespace CS

/-! ## Languages -/

/-- A language is a predicate on binary strings. -/
abbrev Language := List Bool → Prop

/-- The bit of `x` at position `i` (`false` beyond the end of `x`). -/

theorem Steps_saturate {N : ℕ} (hE : ∀ a b, E a b → b ≤ N) {m u v : ℕ} (hu : u ≤ N)
    (h : Steps E m u v) : Steps E (N + 1) u v := by
  classical
  set S : ℕ → Finset ℕ := fun i => (Finset.range (N + 1)).filter (fun w => Steps E i u w)
    with hS
  have hmem : ∀ i w, w ∈ S i ↔ Steps E i u w := by
    intro i w
    simp only [hS, Finset.mem_filter, Finset.mem_range, and_iff_right_iff_imp]
    intro hw
    exact Nat.lt_succ_of_le (Steps_le_of_edge hE hu hw)
  have hmono : ∀ i j, i ≤ j → S i ⊆ S j := by
    intro i j hij w hw
    exact (hmem j w).2 (Steps_mono hij ((hmem i w).1 hw))
  have hstab : ∀ i, S (i + 1) = S i → ∀ j, i ≤ j → S j = S i := by
    intro i hi j hij
    induction j with
    | zero =>
      have : i = 0 := by omega
      rw [this]
    | succ j ih =>
      rcases Nat.lt_or_ge i (j + 1) with h' | h'
      · have hji : S j = S i := ih (by omega)
        apply Finset.ext
        intro w
        rw [hmem, ← hi, hmem]
        constructor
        · rintro (h1 | ⟨z, hz1, hz2⟩)
          · exact Or.inl (((hmem i w).1 (hji ▸ (hmem j w).2 h1)))
          · exact Or.inr ⟨z, ((hmem i z).1 (hji ▸ (hmem j z).2 hz1)), hz2⟩
        · rintro (h1 | ⟨z, hz1, hz2⟩)
          · exact Or.inl ((hmem j w).1 (hji ▸ (hmem i w).2 h1))
          · exact Or.inr ⟨z, (hmem j z).1 (hji ▸ (hmem i z).2 hz1), hz2⟩
      · have : i = j + 1 := by omega
        rw [this]
  have hcard : ∀ i, (S i).card ≤ N + 1 := by
    intro i
    calc (S i).card ≤ (Finset.range (N + 1)).card := Finset.card_le_card (Finset.filter_subset _ _)
      _ = N + 1 := Finset.card_range _
  have hgrow : ∀ j, (∀ i, i < j → S (i + 1) ≠ S i) → j + 1 ≤ (S j).card := by
    intro j
    induction j with
    | zero =>
      intro _
      have : u ∈ S 0 := (hmem 0 u).2 rfl
      exact Finset.card_pos.2 ⟨u, this⟩
    | succ j ih =>
      intro hne
      have h1 : j + 1 ≤ (S j).card := ih (fun i hi => hne i (by omega))
      have h2 : S j ⊂ S (j + 1) :=
        ssubset_iff_subset_ne.2 ⟨hmono j (j + 1) (by omega), fun hh => hne j (by omega) hh.symm⟩
      have := Finset.card_lt_card h2
      omega
  have hex : ∃ i, i ≤ N ∧ S (i + 1) = S i := by
    by_contra hcon
    push_neg at hcon
    have := hgrow (N + 1) (fun i hi => hcon i (by omega))
    have := hcard (N + 1)
    omega
  obtain ⟨i, hiN, hi⟩ := hex
  have hvm : v ∈ S (max m i) := hmono m (max m i) (le_max_left _ _) ((hmem m v).2 h)
  rw [hstab i hi (max m i) (le_max_right _ _)] at hvm
  exact Steps_mono (by omega) ((hmem i v).1 hvm)

/-! ## Machine models

Both models are *random access input* space bounded machines: a configuration determines a
position of the input that is read, and the transition depends on the configuration together
with the bit read there.  This is what makes the classes non-trivial: a machine has no other
access to its input (see `CS.firstBit_mem_dspace` for a concrete language in `DSPACE 0`).

The transition data is allowed to depend arbitrarily on the input length `n`, so the model is
non-uniform; Savitch's simulation below is proved in this generality, and in particular applies
to uniform machines. -/

/-- A nondeterministic space bounded machine.  Configurations for inputs of length `n` are the
naturals `< size n`. -/
structure NMachine where
  /-- number of configurations on inputs of length `n` -/
  size : ℕ → ℕ
  /-- initial configuration -/
  init : ℕ → ℕ
  /-- input position read by a configuration -/
  ipos : ℕ → ℕ → ℕ
  /-- transition relation, depending on the bit read -/
  step : ℕ → Bool → ℕ → ℕ → Prop
  /-- accepting configurations -/
  acc : ℕ → ℕ → Prop
  init_lt : ∀ n, init n < size n
  step_lt : ∀ n b u v, step n b u v → u < size n ∧ v < size n

/-- The configuration graph of `M` on input `x`. -/
