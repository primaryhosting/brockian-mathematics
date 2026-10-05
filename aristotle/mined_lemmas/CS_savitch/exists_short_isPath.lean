/-
# Savitch
Category: Frontier Cs
Target: CS.savitch
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import RequestProject.Savitch.Model
import RequestProject.Savitch.Reach
import RequestProject.Savitch.Interp
import RequestProject.Savitch.BigStep
import RequestProject.Savitch.Invariant
import RequestProject.Savitch.Encode

/-!
# Savitch
Category: Frontier Cs
Target: CS.savitch
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

/-!
## Statement

`NSPACE(f) ⊆ DSPACE(f²)`, and consequently `PSPACE = NPSPACE` (Savitch's theorem).

The model of computation is the standard configuration-graph model, set up in
`RequestProject.Savitch.Model`: configurations are natural numbers (binary strings), a machine
runs in space `f` on input `x` if all configurations reachable on `x` are `< 2 ^ f |x|`, and
one step may depend on the current configuration together with the single input symbol scanned
by the input head, whose position is determined by the configuration.  The initial
configuration may depend on the input length (the usual assumption that the space bound is
constructible).  No computability assumption is imposed on the transition functions.

The deterministic simulator is built explicitly: it performs the depth-first evaluation of
Savitch's divide-and-conquer recursion, its states are recursion stacks of depth at most `s`,
each frame holding boundedly many numbers `< 2 ^ s`, and the whole state is encoded as a
natural number `< 2 ^ (42 * (s + 1) ^ 2)`.  Hence a nondeterministic machine running in space
`f` is simulated deterministically in space `42 * (f + 1) ^ 2`.
-/

namespace CS

open Classical

variable {Γ : Type}

/-! ### Deterministic machines are nondeterministic machines -/

/-- A deterministic machine, viewed as a nondeterministic one. -/

theorem exists_short_isPath :
    ∀ (t : ℕ) (p : ℕ → ℕ) (a b : ℕ), IsPath edge p t a b → (∀ i, i ≤ t → p i < 2 ^ s) →
      ∃ (t' : ℕ) (p' : ℕ → ℕ), t' ≤ 2 ^ s ∧ IsPath edge p' t' a b ∧
        (∀ i, i ≤ t' → p' i < 2 ^ s) := by
  intro t
  induction t using Nat.strong_induction_on with
  | _ t ih =>
    intro p a b hp hbnd
    by_cases ht : t ≤ 2 ^ s
    · exact ⟨t, p, ht, hp, hbnd⟩
    · push_neg at ht
      -- pigeonhole: two vertices of the walk coincide
      have hmaps : ∀ i ∈ Finset.range (t + 1), p i ∈ Finset.range (2 ^ s) := by
        intro i hi
        simp only [Finset.mem_range] at hi ⊢
        exact hbnd i (by omega)
      have hcard : (Finset.range (2 ^ s)).card < (Finset.range (t + 1)).card := by
        simp only [Finset.card_range]; omega
      obtain ⟨i, hi, j, hj, hij, hpij⟩ :=
        Finset.exists_ne_map_eq_of_card_lt_of_maps_to hcard hmaps
      simp only [Finset.mem_range] at hi hj
      -- WLOG `i < j`
      obtain ⟨i, j, hi, hj, hij, hpij⟩ :
          ∃ i j : ℕ, i < t + 1 ∧ j < t + 1 ∧ i < j ∧ p i = p j := by
        rcases lt_or_gt_of_ne hij with h | h
        · exact ⟨i, j, hi, hj, h, hpij⟩
        · exact ⟨j, i, hj, hi, h, hpij.symm⟩
      obtain ⟨h0, htb, hstep⟩ := hp
      set d := j - i with hd
      have hd0 : 0 < d := by omega
      set q : ℕ → ℕ := fun n => if n ≤ i then p n else p (n + d) with hq
      have hqle : ∀ n, n ≤ i → q n = p n := by intro n hn; simp [hq, hn]
      have hqgt : ∀ n, i < n → q n = p (n + d) := by
        intro n hn; simp [hq, Nat.not_le.mpr hn]
      have hlen : t - d < t := by omega
      have hpath : IsPath edge q (t - d) a b := by
        refine ⟨?_, ?_, ?_⟩
        · rw [hqle 0 (by omega)]; exact h0
        · rcases Nat.lt_or_ge i (t - d) with h2 | h2
          · rw [hqgt _ h2, show t - d + d = t from by omega]; exact htb
          · have : t - d = i := by omega
            rw [this, hqle i le_rfl, hpij, show j = t from by omega]
            exact htb
        · intro n hn
          rcases lt_or_ge n i with h | h
          · rw [hqle n (by omega), hqle (n + 1) (by omega)]
            exact hstep n (by omega)
          rcases eq_or_lt_of_le h with h' | h'
          · rw [hqle n (by omega), hqgt (n + 1) (by omega), ← h', hpij,
              show i + 1 + d = j + 1 from by omega]
            exact hstep j (by omega)
          · rw [hqgt n h', hqgt (n + 1) (by omega), show n + 1 + d = (n + d) + 1 from by omega]
            exact hstep (n + d) (by omega)
      have hqbnd : ∀ n, n ≤ t - d → q n < 2 ^ s := by
        intro n hn
        rcases Nat.lt_or_ge i n with h | h
        · rw [hqgt n h]; exact hbnd (n + d) (by omega)
        · rw [hqle n h]; exact hbnd n (by omega)
      exact ih (t - d) hlen q a b hpath hqbnd

/-- Completeness: if all configurations reachable from `a` fit in `s` bits, then
reachability is captured by the Savitch predicate at level `s`. -/
