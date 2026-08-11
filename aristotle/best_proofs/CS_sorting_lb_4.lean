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

namespace CS

/-- A comparison-based sorting algorithm on `n` elements, modelled as a binary decision
tree: an internal node compares two positions `i` and `j` of the input and branches on
the outcome of the test `f i ≤ f j`; a leaf outputs a permutation of the positions,
intended to be the permutation that sorts the input. -/
inductive DTree (n : ℕ) where
  | leaf : Equiv.Perm (Fin n) → DTree n
  | node : Fin n → Fin n → DTree n → DTree n → DTree n
  deriving Inhabited

namespace DTree

variable {n : ℕ}

/-- The worst-case number of comparisons performed by the algorithm, i.e. the height of
the decision tree. -/
def depth : DTree n → ℕ
  | leaf _ => 0
  | node _ _ l r => 1 + max l.depth r.depth

/-- Running the algorithm on an input `f : Fin n → ℕ`. -/
def run : DTree n → (Fin n → ℕ) → Equiv.Perm (Fin n)
  | leaf p, _ => p
  | node i j l r, f => if f i ≤ f j then l.run f else r.run f

/-- The list of outputs sitting at the leaves of the tree. -/
def leaves : DTree n → List (Equiv.Perm (Fin n))
  | leaf p => [p]
  | node _ _ l r => l.leaves ++ r.leaves

/-- A decision tree of depth `d` has at most `2 ^ d` leaves. -/
lemma length_leaves_le (t : DTree n) : t.leaves.length ≤ 2 ^ t.depth := by
  induction t with
  | leaf p => simp [leaves, depth]
  | node i j l r ihl ihr =>
      have h : (2 : ℕ) ^ l.depth + 2 ^ r.depth ≤ 2 ^ (1 + max l.depth r.depth) := by
        have hl : (2 : ℕ) ^ l.depth ≤ 2 ^ (max l.depth r.depth) :=
          Nat.pow_le_pow_right (by norm_num) (le_max_left _ _)
        have hr : (2 : ℕ) ^ r.depth ≤ 2 ^ (max l.depth r.depth) :=
          Nat.pow_le_pow_right (by norm_num) (le_max_right _ _)
        have : (2 : ℕ) ^ (1 + max l.depth r.depth)
            = 2 ^ (max l.depth r.depth) + 2 ^ (max l.depth r.depth) := by
          rw [pow_add]; ring
        omega
      simp only [leaves, depth, List.length_append]
      omega

/-- Every run of the algorithm ends at one of its leaves. -/
lemma run_mem_leaves (t : DTree n) (f : Fin n → ℕ) : t.run f ∈ t.leaves := by
  induction t with
  | leaf p => simp [run, leaves]
  | node i j l r ihl ihr =>
      by_cases h : f i ≤ f j <;> simp [run, leaves, h, ihl, ihr]

end DTree

/-- Correctness of a comparison sort: on every input with pairwise distinct entries, the
permutation it outputs sorts the input. -/
def Sorts {n : ℕ} (t : DTree n) : Prop :=
  ∀ f : Fin n → ℕ, Function.Injective f → StrictMono (f ∘ (t.run f))

/-- A sanity check that the correctness predicate `Sorts` is satisfiable: the one-comparison
tree that compares the two entries and swaps them if needed is a correct sort of `2`
elements. -/
example : Sorts (DTree.node (0 : Fin 2) 1 (DTree.leaf 1) (DTree.leaf (Equiv.swap 0 1))) := by
  intro f hf a b hab
  have hab' : a = 0 ∧ b = 1 := by
    have hlt : (a : ℕ) < (b : ℕ) := hab
    have ha := a.isLt
    have hb := b.isLt
    refine ⟨Fin.ext ?_, Fin.ext ?_⟩ <;> simp <;> omega
  obtain ⟨rfl, rfl⟩ := hab'
  by_cases h : f 0 ≤ f 1
  · have hlt : f 0 < f 1 := lt_of_le_of_ne h (fun he => by simpa using hf he)
    simpa [DTree.run, h, Function.comp] using hlt
  · have hlt : f 1 < f 0 := lt_of_not_ge h
    simpa [DTree.run, h, Function.comp, Equiv.swap_apply_left, Equiv.swap_apply_right] using hlt

/-- A strictly monotone permutation of `Fin n`, composed with the coercion to `ℕ`,
must be the identity. -/
lemma perm_eq_one_of_strictMono {n : ℕ} (g : Equiv.Perm (Fin n))
    (h : StrictMono (fun i => ((g i : Fin n) : ℕ))) : g = 1 := by
  refine (Equiv.Perm.monotone_iff g).mp ?_
  intro a b hab
  rcases eq_or_lt_of_le hab with rfl | hlt
  · exact le_rfl
  · exact le_of_lt (Fin.lt_def.mpr (h hlt))

/-- On the input `fun i => (τ i : ℕ)`, a correct comparison sort must output `τ⁻¹`. -/
lemma run_eq_inv {n : ℕ} (t : DTree n) (ht : Sorts t) (τ : Equiv.Perm (Fin n)) :
    t.run (fun i => ((τ i : Fin n) : ℕ)) = τ⁻¹ := by
  set f : Fin n → ℕ := fun i => ((τ i : Fin n) : ℕ) with hf
  have hinj : Function.Injective f := by
    intro a b hab
    have : τ a = τ b := Fin.val_injective hab
    exact τ.injective this
  have hsm := ht f hinj
  set σ := t.run f with hσ
  have : StrictMono (fun i => (((τ * σ) i : Fin n) : ℕ)) := by
    simpa [Function.comp, hf, Equiv.Perm.mul_apply] using hsm
  have h1 : τ * σ = 1 := perm_eq_one_of_strictMono _ this
  have := congrArg (fun p => τ⁻¹ * p) h1
  simpa [← mul_assoc] using this

/-- **Comparison-sort lower bound for 4 elements.**
Any correct comparison sort of `4` elements uses at least `⌈log₂ (4!)⌉ = 5` comparisons
in the worst case. -/
theorem sorting_lb_4 (t : DTree 4) (ht : Sorts t) : Nat.clog 2 (Nat.factorial 4) ≤ t.depth := by
  have hcard : (Finset.univ : Finset (Equiv.Perm (Fin 4))).card ≤ t.leaves.toFinset.card := by
    refine Finset.card_le_card_of_injOn (fun τ => τ⁻¹) ?_ ?_
    · intro τ _
      refine Finset.mem_coe.mpr (List.mem_toFinset.mpr ?_)
      show τ⁻¹ ∈ t.leaves
      rw [← run_eq_inv t ht τ]
      exact t.run_mem_leaves _
    · intro a _ b _ hab
      simpa using congrArg (fun p : Equiv.Perm (Fin 4) => p⁻¹) hab
  have h24 : (Finset.univ : Finset (Equiv.Perm (Fin 4))).card = 24 := by
    simp [Finset.card_univ, Fintype.card_perm, Nat.factorial]
  have hlen : t.leaves.toFinset.card ≤ t.leaves.length := t.leaves.toFinset_card_le
  have hpow : (24 : ℕ) ≤ 2 ^ t.depth := by
    have := t.length_leaves_le
    omega
  have : Nat.factorial 4 = 24 := by decide
  rw [this]
  exact (Nat.clog_le_iff_le_pow (by norm_num)).mpr hpow

end CS

