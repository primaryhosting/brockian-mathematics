import Mathlib

/-!
# Sorting Lb 5
Category: Computer Science
Target: CS.sorting_lb_5
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

namespace CS

/-- A *comparison sorting algorithm* on `n` real-valued keys, modelled as a decision tree.
Each internal node `node i j l r` compares the keys at positions `i` and `j` of the input and
branches to `l` if `a i ≤ a j`, to `r` otherwise; each leaf outputs a permutation of the
positions (the claimed sorting order).  Only comparisons of input keys are allowed. -/
inductive CompTree (n : ℕ) : Type
  | leaf : Equiv.Perm (Fin n) → CompTree n
  | node : Fin n → Fin n → CompTree n → CompTree n → CompTree n

namespace CompTree

variable {n : ℕ}

/-- The permutation output by the algorithm on the input `a`. -/
noncomputable def run : CompTree n → (Fin n → ℝ) → Equiv.Perm (Fin n)
  | leaf σ, _ => σ
  | node i j l r, a => if a i ≤ a j then l.run a else r.run a

/-- The worst-case number of comparisons performed, i.e. the depth of the decision tree. -/
def depth : CompTree n → ℕ
  | leaf _ => 0
  | node _ _ l r => max l.depth r.depth + 1

/-- The (finite) set of permutations appearing at the leaves of the tree. -/
def leaves : CompTree n → Finset (Equiv.Perm (Fin n))
  | leaf σ => {σ}
  | node _ _ l r => l.leaves ∪ r.leaves

/-- A tree of depth `d` has at most `2 ^ d` leaves. -/
theorem card_leaves_le (t : CompTree n) : t.leaves.card ≤ 2 ^ t.depth := by
  induction t with
  | leaf σ => simp [leaves, depth]
  | node i j l r ihl ihr =>
      refine le_trans (Finset.card_union_le _ _) ?_
      have hl : l.leaves.card ≤ 2 ^ (max l.depth r.depth) :=
        ihl.trans (Nat.pow_le_pow_right (by norm_num) (le_max_left _ _))
      have hr : r.leaves.card ≤ 2 ^ (max l.depth r.depth) :=
        ihr.trans (Nat.pow_le_pow_right (by norm_num) (le_max_right _ _))
      have : l.leaves.card + r.leaves.card ≤
          2 ^ (max l.depth r.depth) + 2 ^ (max l.depth r.depth) := by omega
      simpa [depth, pow_succ, two_mul, Nat.mul_comm] using this

/-- Every output of the algorithm occurs as a leaf. -/
theorem run_mem_leaves (t : CompTree n) (a : Fin n → ℝ) : t.run a ∈ t.leaves := by
  induction t with
  | leaf σ => simp [run, leaves]
  | node i j l r ihl ihr =>
      by_cases h : a i ≤ a j <;> simp [run, leaves, h, ihl, ihr]

end CompTree

/-- The permutation that sorts a given input is unique (strict monotonicity of `a ∘ σ` already
forces `a` to be injective). -/
theorem sorting_perm_unique {n : ℕ} {a : Fin n → ℝ}
    {σ p : Equiv.Perm (Fin n)} (hσ : StrictMono (a ∘ σ)) (hp : StrictMono (a ∘ p)) :
    σ = p := by
  have hρ : StrictMono ⇑(p⁻¹ * σ) := by
    intro x y hxy
    have h1 : a (σ x) < a (σ y) := hσ hxy
    by_contra hcon
    have h2 : (p⁻¹ * σ) y ≤ (p⁻¹ * σ) x := not_lt.mp hcon
    rcases eq_or_lt_of_le h2 with h3 | h3
    · have : σ y = σ x := by
        have := congrArg (fun k => p k) h3
        simpa [Equiv.Perm.mul_apply] using this
      have hxy' : x = y := σ.injective this.symm
      exact absurd (hxy' ▸ h1) (lt_irrefl _)
    · have := hp h3
      simp only [Function.comp_apply, Equiv.Perm.mul_apply, Equiv.apply_symm_apply,
        Equiv.Perm.inv_def] at this
      exact absurd h1 (not_lt.mpr this.le)
  have h4 : p⁻¹ * σ = 1 := (Equiv.Perm.monotone_iff _).mp hρ.monotone
  have h5 := congrArg (fun x => p * x) h4
  simpa [mul_assoc] using h5

/-- Every permutation of `Fin n` is realised as the sorting permutation of some injective input. -/
theorem exists_input_with_sorting_perm {n : ℕ} (p : Equiv.Perm (Fin n)) :
    ∃ a : Fin n → ℝ, Function.Injective a ∧ StrictMono (a ∘ p) := by
  refine ⟨fun k => ((p.symm k : ℕ) : ℝ), ?_, ?_⟩
  · intro x y hxy
    simp only at hxy
    have h1 : (p.symm x : ℕ) = (p.symm y : ℕ) := by exact_mod_cast hxy
    have h2 : p.symm x = p.symm y := Fin.ext h1
    simpa using congrArg p h2
  · intro x y hxy
    simp only [Function.comp_apply, Equiv.symm_apply_apply]
    exact_mod_cast (Fin.val_strictMono hxy)

/-- A correct comparison sorting tree must have all `n!` permutations among its leaves. -/
theorem leaves_eq_univ {n : ℕ} (t : CompTree n)
    (hcorrect : ∀ a : Fin n → ℝ, Function.Injective a → StrictMono (a ∘ t.run a)) :
    t.leaves = Finset.univ := by
  refine Finset.eq_univ_of_forall (fun p => ?_)
  obtain ⟨a, ha, hp⟩ := exists_input_with_sorting_perm p
  have : t.run a = p := sorting_perm_unique (hcorrect a ha) hp
  exact this ▸ t.run_mem_leaves a

/-- **Comparison-sorting lower bound.**  Any comparison sort of `5` elements, i.e. any decision
tree that only compares input keys and outputs a permutation sorting the input, must perform at
least `⌈log₂ (5!)⌉ = 7` comparisons in the worst case. -/
theorem sorting_lb_5 (t : CompTree 5)
    (hcorrect : ∀ a : Fin 5 → ℝ, Function.Injective a → StrictMono (a ∘ t.run a)) :
    Nat.clog 2 (Nat.factorial 5) ≤ t.depth := by
  have hleaves : t.leaves = Finset.univ := leaves_eq_univ t hcorrect
  have hcard : (Nat.factorial 5) ≤ 2 ^ t.depth := by
    have h1 : t.leaves.card = Nat.factorial 5 := by
      rw [hleaves, Finset.card_univ, Fintype.card_perm, Fintype.card_fin]
    exact h1 ▸ t.card_leaves_le
  exact (Nat.clog_le_iff_le_pow (by norm_num)).mpr hcard

/-- `⌈log₂ (5!)⌉ = 7`. -/
theorem clog_factorial_five : Nat.clog 2 (Nat.factorial 5) = 7 := by
  norm_num [Nat.factorial]

/-- Sanity check that the correctness hypothesis is satisfiable: the obvious one-comparison
algorithm correctly sorts two elements. -/
theorem exists_correct_comparison_sort_two :
    ∃ t : CompTree 2, (∀ a : Fin 2 → ℝ, Function.Injective a → StrictMono (a ∘ t.run a)) ∧
      t.depth = 1 := by
  refine ⟨CompTree.node 0 1 (CompTree.leaf 1) (CompTree.leaf (Equiv.swap 0 1)), ?_, rfl⟩
  intro a ha
  have hne : a 0 ≠ a 1 := fun h => by simpa using ha h
  rw [Fin.strictMono_iff_lt_succ]
  intro i
  fin_cases i
  by_cases h : a 0 ≤ a 1
  · simp only [CompTree.run, h, if_true, Function.comp_apply]
    simp only [Equiv.Perm.coe_one, id_eq]
    exact lt_of_le_of_ne h hne
  · simp only [CompTree.run, h, if_false, Function.comp_apply]
    push_neg at h
    simpa [Equiv.swap_apply_def] using h

/-- Restatement of the lower bound with the explicit constant `7`. -/
theorem sorting_lb_5_seven (t : CompTree 5)
    (hcorrect : ∀ a : Fin 5 → ℝ, Function.Injective a → StrictMono (a ∘ t.run a)) :
    7 ≤ t.depth := by
  have := sorting_lb_5 t hcorrect
  rwa [clog_factorial_five] at this

end CS

