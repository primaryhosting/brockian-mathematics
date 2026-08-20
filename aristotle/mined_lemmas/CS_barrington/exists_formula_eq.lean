import Mathlib

/-!
# Basic definitions for Barrington's theorem

* Boolean formulas over the basis `{¬, ∧, ∨}` (with constants), together with their
  depth and semantics.  Non-uniform `NC¹` is the class of families of boolean functions
  computed by formulas of logarithmic depth.
* Width-5 permutation branching programs: a program is a list of instructions, each of
  which reads one input bit and outputs one of two permutations of `Fin 5` (or is a
  constant instruction).  The value of the program is the product of the permutations
  produced by its instructions, and the program accepts iff this product lies in a
  designated set of accepting permutations.
-/

namespace CS

open Equiv Equiv.Perm

/-- Permutations of a five element set. -/
abbrev Perm5 := Equiv.Perm (Fin 5)

/-- A permutation of `Fin 5` is a five-cycle if it is a cycle whose support is everything. -/

theorem exists_formula_eq (n : ℕ) : ∀ (ℓ : ℕ) (P : List (Instr n)), P.length = ℓ →
    ∀ π : Perm5, ∃ φ : Formula n, (∀ x, (φ.eval x = true ↔ BPeval P x = π)) ∧
      φ.depth ≤ (K5 + 1) * Nat.clog 2 ℓ + 1 := by
  intro ℓ
  induction ℓ using Nat.strong_induction_on with
  | _ ℓ IH =>
    intro P hP π
    match hℓ : ℓ with
    | 0 =>
        subst hℓ
        have hPnil : P = [] := List.length_eq_zero_iff.1 hP
        subst hPnil
        refine ⟨.const (decide ((1 : Perm5) = π)), ?_, by simp [Formula.depth]⟩
        intro x; simp [Formula.eval]
    | 1 =>
        subst hℓ
        obtain ⟨I, rfl⟩ := List.length_eq_one_iff.1 hP
        have hval : ∀ x : Fin n → Bool, BPeval [I] x = I.run x := by
          intro x; simp [BPeval]
        match I with
        | .const p =>
            refine ⟨.const (decide (p = π)), ?_, by simp [Formula.depth]⟩
            intro x; simp [Formula.eval, hval, Instr.run]
        | .test i p q =>
            by_cases hp : p = π <;> by_cases hq : q = π
            · refine ⟨.const true, ?_, by simp [Formula.depth]⟩
              intro x
              by_cases hx : x i <;> simp [Formula.eval, Instr.run, hx, hp, hq]
            · refine ⟨.var i, ?_, by simp [Formula.depth, Nat.clog]⟩
              intro x
              by_cases hx : x i <;> simp [Formula.eval, Instr.run, hx, hp, hq]
            · refine ⟨.not (.var i), ?_, by simp [Formula.depth, Nat.clog]⟩
              intro x
              by_cases hx : x i <;> simp [Formula.eval, Instr.run, hx, hp, hq]
            · refine ⟨.const false, ?_, by simp [Formula.depth]⟩
              intro x
              by_cases hx : x i <;> simp [Formula.eval, hval, Instr.run, hx, hp, hq]
    | (k + 2) =>
        subst hℓ
        set ℓ := k + 2 with hℓdef
        set m := (ℓ + 1) / 2 with hm
        have hm1 : 1 ≤ m := by omega
        have hmℓ : m < ℓ := by omega
        have hsub : ℓ - m ≤ m := by omega
        have hsubℓ : ℓ - m < ℓ := by omega
        set A := P.take m with hA
        set B := P.drop m with hB
        have hlenA : A.length = m := by rw [hA, List.length_take, hP]; omega
        have hlenB : B.length = ℓ - m := by rw [hB, List.length_drop, hP]
        have hsplit : ∀ x : Fin n → Bool, BPeval P x = BPeval A x * BPeval B x := by
          intro x
          conv_lhs => rw [← List.take_append_drop m P]
          rw [BPeval_append]
        choose φA hφA hdA using fun ρ => IH m hmℓ A hlenA ρ
        choose φB hφB hdB using fun ρ => IH (ℓ - m) hsubℓ B hlenB ρ
        refine ⟨Formula.orList ((Finset.univ : Finset Perm5).toList.map
          (fun ρ => .and (φA ρ) (φB (ρ⁻¹ * π)))), ?_, ?_⟩
        · intro x
          rw [Formula.eval_orList]
          simp only [List.any_map, List.any_eq_true, Function.comp_def, Finset.mem_toList,
            Finset.mem_univ, true_and, Formula.eval, Bool.and_eq_true]
          constructor
          · rintro ⟨ρ, h1, h2⟩
            rw [hsplit x, (hφA ρ x).1 h1, (hφB (ρ⁻¹ * π) x).1 h2]
            group
          · intro h
            refine ⟨BPeval A x, (hφA _ x).2 rfl, (hφB _ x).2 ?_⟩
            rw [hsplit x] at h
            rw [← h]
            group
        · have hdepth : ∀ p ∈ ((Finset.univ : Finset Perm5).toList.map
              (fun ρ => (Formula.and (φA ρ) (φB (ρ⁻¹ * π)) : Formula n))),
              p.depth ≤ (K5 + 1) * Nat.clog 2 m + 2 := by
            intro p hp
            simp only [List.mem_map, Finset.mem_toList] at hp
            obtain ⟨ρ, -, rfl⟩ := hp
            have h1 := hdA ρ
            have h2 : (φB (ρ⁻¹ * π)).depth ≤ (K5 + 1) * Nat.clog 2 m + 1 := by
              refine le_trans (hdB (ρ⁻¹ * π)) ?_
              have := Nat.clog_mono_right 2 hsub
              have := Nat.mul_le_mul_left (K5 + 1) this
              omega
            simp only [Formula.depth]
            omega
          have hor := Formula.depth_orList _ _ hdepth
          rw [List.length_map, length_univ_toList] at hor
          have hclog : Nat.clog 2 ℓ = Nat.clog 2 m + 1 := by
            rw [Nat.clog_of_two_le (by norm_num) (by omega)]
            congr 1
          rw [hclog]
          have : (K5 + 1) * (Nat.clog 2 m + 1) = (K5 + 1) * Nat.clog 2 m + K5 + 1 := by ring
          omega

/-- A width-5 permutation branching program with an arbitrary set of accepting
permutations is simulated by a formula of depth `O(log ℓ)`. -/
