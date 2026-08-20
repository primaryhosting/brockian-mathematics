/-
# Nisan Wigderson Prg
Category: Frontier Cs
Target: CS.nisan_wigderson_prg
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/
import Mathlib

/-!
# Nisan Wigderson Prg
Category: Frontier Cs
Target: CS.nisan_wigderson_prg
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open scoped BigOperators

namespace CS

/-! ## Boolean circuits

We use a term representation of Boolean circuits, but we measure their size in the
*DAG* sense: the size of a circuit is the number of distinct subcircuits occurring in
it (equivalently, the number of gates when identical subcircuits are shared). -/

/-- Boolean circuits on `n` input variables. -/
inductive Circ (n : ℕ) where
  | var : Fin n → Circ n
  | const : Bool → Circ n
  | not : Circ n → Circ n
  | and : Circ n → Circ n → Circ n
  | or : Circ n → Circ n → Circ n
  deriving DecidableEq

namespace Circ

/-- The Boolean function computed by a circuit. -/

lemma nw_predictor_circuit {ℓ d m α : ℕ}
    (e : Fin m → (Fin ℓ ↪ Fin d))
    (hdesign : ∀ i j : Fin m, i ≠ j →
      ((Finset.univ.image (e i)) ∩ (Finset.univ.image (e j))).card ≤ α)
    (f : (Fin ℓ → Bool) → Bool) (D : Circ m) (i : Fin m)
    (z₀ : Fin d → Bool) (y₀ : Fin m → Bool) (neg : Bool) :
    ∃ C : Circ ℓ, C.size ≤ D.size + m * (7 * 2 ^ α) + 1 ∧
      ∀ x : Fin ℓ → Bool,
        C.eval x =
          xor neg ((D.eval (nwStr e f i (setBlock (e i) z₀ x) y₀ (y₀ i))) == y₀ i) := by
  classical
  set T : Fin m → Finset (Fin ℓ) :=
    fun j => Finset.univ.filter (fun t : Fin ℓ => ∃ u, e j u = e i t) with hT
  -- the blocks of a design overlap in few positions
  have hTcard : ∀ j : Fin m, j ≠ i → (T j).card ≤ α := by
    intro j hji
    have himg : (T j).image (e i) = (Finset.univ.image (e i)) ∩ (Finset.univ.image (e j)) := by
      ext k
      simp only [hT, Finset.mem_image, Finset.mem_filter, Finset.mem_univ, true_and,
        Finset.mem_inter]
      constructor
      · rintro ⟨t, ⟨u, hu⟩, rfl⟩
        exact ⟨⟨t, rfl⟩, ⟨u, by rw [hu]⟩⟩
      · rintro ⟨⟨t, rfl⟩, ⟨u, hu⟩⟩
        exact ⟨t, ⟨u, hu⟩, rfl⟩
    have hcard : (T j).card = ((T j).image (e i)).card :=
      (Finset.card_image_of_injective _ (e i).injective).symm
    rw [hcard, himg]
    exact hdesign i j (Ne.symm hji)
  -- the `j`-th output bit depends only on the positions of block `i` met by block `j`
  have hdep : ∀ (j : Fin m) (x₁ x₂ : Fin ℓ → Bool), (∀ t ∈ T j, x₁ t = x₂ t) →
      f (setBlock (e i) z₀ x₁ ∘ e j) = f (setBlock (e i) z₀ x₂ ∘ e j) := by
    intro j x₁ x₂ hx
    congr 1
    funext u
    simp only [Function.comp_apply]
    by_cases h : ∃ t, e i t = e j u
    · obtain ⟨t, ht⟩ := h
      rw [← ht, setBlock_apply_mem, setBlock_apply_mem]
      exact hx t (by simp [hT, ht])
    · rw [setBlock_apply_not_mem _ _ _ h, setBlock_apply_not_mem _ _ _ h]
  set σ : Fin m → Circ ℓ := fun j =>
    if (j : ℕ) < (i : ℕ) then
      Circ.juntaCirc (fun x => f (setBlock (e i) z₀ x ∘ e j)) (T j).toList (fun _ => false)
    else Circ.const (y₀ j) with hσ
  have hevalσ : ∀ (j : Fin m) (x : Fin ℓ → Bool),
      Circ.eval (σ j) x = nwStr e f i (setBlock (e i) z₀ x) y₀ (y₀ i) j := by
    intro j x
    by_cases hj : (j : ℕ) < (i : ℕ)
    · simp only [hσ, nwStr, if_pos hj]
      rw [Circ.eval_juntaCirc]
      exact hdep j _ x (by intro t ht; simp [Finset.mem_toList, ht])
    · have hσj : σ j = Circ.const (y₀ j) := by
        simp only [hσ]; rw [if_neg hj]
      rw [hσj]
      by_cases hji : j = i
      · subst hji
        simp [nwStr, Circ.eval]
      · simp only [nwStr, Circ.eval, if_neg hj, if_neg hji]
  have hsizeσ : ∀ j : Fin m, Circ.size (σ j) ≤ 7 * 2 ^ α := by
    intro j
    have hp : (1 : ℕ) ≤ 2 ^ α := Nat.one_le_two_pow
    by_cases hj : (j : ℕ) < (i : ℕ)
    · have hji : j ≠ i := by
        intro h; rw [h] at hj; omega
      have hlen : (T j).toList.length ≤ α := by
        rw [Finset.length_toList]; exact hTcard j hji
      have hb := Circ.size_juntaCirc (fun x => f (setBlock (e i) z₀ x ∘ e j))
        (T j).toList (fun _ => false)
      have hmono : (7 : ℕ) * 2 ^ (T j).toList.length ≤ 7 * 2 ^ α :=
        Nat.mul_le_mul_left _ (Nat.pow_le_pow_right (by norm_num) hlen)
      simp only [hσ, if_pos hj]
      omega
    · simp only [hσ, if_neg hj, Circ.size_const]
      omega
  set Acirc : Circ ℓ := Circ.subst D σ with hAc
  have hevalA : ∀ x : Fin ℓ → Bool,
      Circ.eval Acirc x = D.eval (nwStr e f i (setBlock (e i) z₀ x) y₀ (y₀ i)) := by
    intro x
    rw [hAc, Circ.eval_subst]
    congr 1
    funext j
    exact hevalσ j x
  have hsizeA : Circ.size Acirc ≤ D.size + m * (7 * 2 ^ α) := by
    have h1 := Circ.size_subst D σ
    rw [← hAc] at h1
    have h2 : ∑ j : Fin m, Circ.size (σ j) ≤ m * (7 * 2 ^ α) := by
      calc ∑ j : Fin m, Circ.size (σ j)
          ≤ ∑ _j : Fin m, 7 * 2 ^ α := Finset.sum_le_sum (fun j _ => hsizeσ j)
        _ = m * (7 * 2 ^ α) := by simp [Finset.sum_const, Finset.card_univ, mul_comm]
    omega
  have hxor : ∀ a r ng : Bool, xor (xor ng (!r)) a = xor ng (a == r) := by decide
  by_cases hc : xor neg (!(y₀ i)) = true
  · refine ⟨Circ.not Acirc, ?_, ?_⟩
    · have hn := Circ.size_not Acirc
      omega
    · intro x
      have h := hxor (D.eval (nwStr e f i (setBlock (e i) z₀ x) y₀ (y₀ i))) (y₀ i) neg
      rw [hc] at h
      simp only [Circ.eval]
      rw [hevalA]
      simpa using h
  · simp only [Bool.not_eq_true] at hc
    refine ⟨Acirc, by omega, ?_⟩
    intro x
    have h := hxor (D.eval (nwStr e f i (setBlock (e i) z₀ x) y₀ (y₀ i))) (y₀ i) neg
    rw [hc] at h
    rw [hevalA]
    simpa using h

/-- If two functions have the same sums over each orbit of an involution, their total sums
agree. -/
