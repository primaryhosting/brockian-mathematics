/-
  Brockian/SieveHamiltonian.lean — THE SIEVE HAMILTONIAN CAMPAIGN
  (July 30, after the "invent the dynamics" program note).

  The object: on the arithmetic wheel Z/M (M odd squarefree), the twin
  sieve deletes residues a with a ≡ 0 or a ≡ −2 mod some ℓ ∣ M. Once
  3 ∣ M the admissible set is pinned to the coset a ≡ 2 (mod 3); the
  residual translation flow is +3 on that coset. The compressed
  Hamiltonian (Dirichlet deletion of forbidden sites from the residual
  cycle) decomposes into path Laplacians over the admissible RUNS, so
  its spectrum is exact and finite. Everything below is finite; no
  Hilbert–Pólya claim is made anywhere in this file — the operator
  limit M → ∞ is an OPEN PROGRAM subject to the G0–G6 gate ladder.

  Charter as Core.lean. The declarations below are the formal campaign targets.
-/
import Mathlib

set_option autoImplicit false

namespace Brockian.SieveHamiltonian

open Matrix

/-! ## 1. The no-go theorem: why the naive adjacency dies at 3 -/

/-- Twin admissibility pins the mod-3 residue. -/

theorem tripleAdmissibleCount_prime (p : ℕ) (hp : p.Prime) (hodd : Odd p) :
    tripleAdmissibleCount p =
      if p = 3 ∨ p = 5 then 1 else p - 6 := by
  by_cases hp3 : p = 3
  · subst hp3; simp [tripleAdmissibleCount]
    rw [Nat.card_eq_one_iff_unique]
    constructor
    · -- Subsingleton: any admissible a = 2
      suffices h : ∀ a : ZMod 3, TripleAdmissible 3 a → a = 2 from
        ⟨fun x y => Subtype.ext (h x.1 x.2 ▸ h y.1 y.2 ▸ rfl)⟩
      intro a ha
      fin_cases a <;> simp [TripleAdmissible] at ha <;> trivial
    · -- Nonempty: TripleAdmissible 3 2
      refine ⟨2, ?_⟩
      simp [TripleAdmissible]
      decide
  · by_cases hp5 : p = 5
    · subst hp5; simp [tripleAdmissibleCount]
      rw [Nat.card_eq_one_iff_unique]
      constructor
      · -- Subsingleton: any admissible a = 1
        suffices h : ∀ a : ZMod 5, TripleAdmissible 5 a → a = 1 from
          ⟨fun x y => Subtype.ext (h x.1 x.2 ▸ h y.1 y.2 ▸ rfl)⟩
        intro a ha
        fin_cases a <;> simp [TripleAdmissible] at ha <;> trivial
      · -- Nonempty: TripleAdmissible 5 1
        refine ⟨1, ?_⟩
        simp [TripleAdmissible]
        decide
    · -- p ≥ 7 case: count = p - 6
      simp [tripleAdmissibleCount]
      -- First establish p ≥ 7
      have hp7 : 7 ≤ p := by
        by_contra h
        push_neg at h
        interval_cases p <;> simp_all (config := {decide := true})
      -- In ZMod p (a field), IsUnit x ↔ x ≠ 0
      -- TripleAdmissible means a ∉ {0, -2, -3, -5, -6, -8}
      -- Use that ZMod p is a field, so IsUnit x ↔ x ≠ 0
      -- Note: Nat.card for finite types works without explicit Fintype
      -- Define the forbidden set
      let F : Finset (ZMod p) := {0, (-2 : ZMod p), (-3 : ZMod p), (-5 : ZMod p), (-6 : ZMod p), (-8 : ZMod p)}
      -- Show F has 6 elements
      have hFcard : F.card = 6 := by
        by_cases hp7' : p = 7
        · subst hp7'; decide
        · -- p ≥ 11 (can't be 8, 9, 10 since p is prime)
          have hp11 : 11 ≤ p := by
            by_contra h
            push_neg at h
            interval_cases p <;> norm_num [hp] at *
          haveI : NeZero p := ⟨by omega⟩
          -- For p ≥ 11, all elements are distinct since differences are < p
          have h2_ne_zero : (2 : ZMod p) ≠ 0 := by
            have hlt : (2 : ℕ) < p := by omega
            have h1 : ZMod.val ((2 : ℕ) : ZMod p) = 2 := ZMod.val_cast_of_lt hlt
            exact fun h => by simp [h] at h1
          have h0 : (0 : ZMod p) ≠ -2 := by simp [h2_ne_zero]
          have h1 : (0 : ZMod p) ≠ -3 := by
            intro h; have h3 : (3 : ZMod p) = 0 := by linear_combination h
            have hlt : (3 : ℕ) < p := by omega
            have h2 : ZMod.val ((3 : ℕ) : ZMod p) = 3 := ZMod.val_cast_of_lt hlt
            simp [h3] at h2
          have h2 : (0 : ZMod p) ≠ -5 := by
            intro h; have h5 : (5 : ZMod p) = 0 := by linear_combination h
            have hlt : (5 : ℕ) < p := by omega
            have h2 : ZMod.val ((5 : ℕ) : ZMod p) = 5 := ZMod.val_cast_of_lt hlt
            simp [h5] at h2
          have h3 : (0 : ZMod p) ≠ -6 := by
            intro h; have h6 : (6 : ZMod p) = 0 := by linear_combination h
            have hlt : (6 : ℕ) < p := by omega
            have h2 : ZMod.val ((6 : ℕ) : ZMod p) = 6 := ZMod.val_cast_of_lt hlt
            simp [h6] at h2
          have h4 : (0 : ZMod p) ≠ -8 := by
            intro h; have h8 : (8 : ZMod p) = 0 := by linear_combination h
            have hlt : (8 : ℕ) < p := by omega
            have h2 : ZMod.val ((8 : ℕ) : ZMod p) = 8 := ZMod.val_cast_of_lt hlt
            simp [h8] at h2
          have h1_ne_zero : (1 : ZMod p) ≠ 0 := by
            have hlt : (1 : ℕ) < p := by omega
            have h1 : ZMod.val ((1 : ℕ) : ZMod p) = 1 := ZMod.val_cast_of_lt hlt
            intro heq; simp [heq] at h1
          have h5 : (-2 : ZMod p) ≠ -3 := by
            intro h; have h1 : (1 : ZMod p) = 0 := by linear_combination h
            exact h1_ne_zero h1
          have h3_ne_zero : (3 : ZMod p) ≠ 0 := by
            have hlt : (3 : ℕ) < p := by omega
            have h1 : ZMod.val ((3 : ℕ) : ZMod p) = 3 := ZMod.val_cast_of_lt hlt
            intro heq; simp [heq] at h1
          have h6 : (-2 : ZMod p) ≠ -5 := by
            intro h; have h3 : (3 : ZMod p) = 0 := by linear_combination h
            exact h3_ne_zero h3
          have h7 : (-2 : ZMod p) ≠ -6 := by
            intro h; have h4 : (4 : ZMod p) = 0 := by linear_combination h
            have hlt : (4 : ℕ) < p := by omega
            have h2 : ZMod.val ((4 : ℕ) : ZMod p) = 4 := ZMod.val_cast_of_lt hlt
            simp [h4] at h2
          have h8 : (-2 : ZMod p) ≠ -8 := by
            intro h; have h6 : (6 : ZMod p) = 0 := by linear_combination h
            have hlt : (6 : ℕ) < p := by omega
            have h2 : ZMod.val ((6 : ℕ) : ZMod p) = 6 := ZMod.val_cast_of_lt hlt
            simp [h6] at h2
          -- Compute F.card = 6
          have hFcard' : F.card = 6 := by
            have h9 : (-3 : ZMod p) ≠ -5 := by
              intro h; have h2 : (2 : ZMod p) = 0 := by linear_combination h
              exact h2_ne_zero h2
            have h10 : (-3 : ZMod p) ≠ -6 := by
              intro h; have h3 : (3 : ZMod p) = 0 := by linear_combination h
              exact h3_ne_zero h3
            have h11 : (-3 : ZMod p) ≠ -8 := by
              intro h; have h5 : (5 : ZMod p) = 0 := by linear_combination h
              have hlt : (5 : ℕ) < p := by omega
              have h2 : ZMod.val ((5 : ℕ) : ZMod p) = 5 := ZMod.val_cast_of_lt hlt
              simp [h5] at h2
            have h12 : (-5 : ZMod p) ≠ -6 := by
              intro h; have h1 : (1 : ZMod p) = 0 := by linear_combination h
              exact h1_ne_zero h1
            have h13 : (-5 : ZMod p) ≠ -8 := by
              intro h; have h3 : (3 : ZMod p) = 0 := by linear_combination h
              exact h3_ne_zero h3
            have h14 : (-6 : ZMod p) ≠ -8 := by
              intro h; have h2 : (2 : ZMod p) = 0 := by linear_combination h
              exact h2_ne_zero h2
            have nodup : List.Nodup [0, (-2 : ZMod p), (-3 : ZMod p), (-5 : ZMod p), (-6 : ZMod p), (-8 : ZMod p)] := by
              simp [List.Nodup, List.mem_cons, h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14]
            have : F = [0, (-2 : ZMod p), (-3 : ZMod p), (-5 : ZMod p), (-6 : ZMod p), (-8 : ZMod p)].toFinset := by simp [F]
            rw [this, List.toFinset_card_of_nodup nodup]; rfl
          exact hFcard'
      simp only [hp3, hp5, or_self, ↓reduceIte]
      -- TripleAdmissible p a ↔ a ∉ F
      have h_equiv : ∀ a : ZMod p, TripleAdmissible p a ↔ a ∉ F := by
        haveI : Fact (Nat.Prime p) := ⟨hp⟩
        intro a
        simp [TripleAdmissible, F]
        simp (config := {decide := true}) [add_eq_zero_iff_eq_neg]; tauto
      -- Use equivalence to rewrite cardinality
      have hcard : Nat.card { a : ZMod p // TripleAdmissible p a } = Nat.card { a : ZMod p // a ∉ F } := by
        exact Nat.card_congr (Equiv.subtypeEquivRight h_equiv)
      rw [hcard]
      -- Nat.card of complement = p - F.card = p - 6
      haveI : NeZero p := ⟨by omega⟩
      haveI : Fintype (ZMod p) := ZMod.fintype p
      rw [Nat.card_eq_fintype_card]
      have hsub : F ⊆ Finset.univ := Finset.subset_univ F
      calc Fintype.card { a : ZMod p // a ∉ F }
          = (Finset.univ \ F).card := by
              rw [Fintype.card_subtype]
              congr 1; ext x; simp [Finset.mem_sdiff, Finset.mem_univ]
        _ = Finset.card (Finset.univ : Finset (ZMod p)) - F.card := by
              rw [Finset.card_sdiff]; simp
        _ = p - 6 := by simp [ZMod.card, hFcard]

/-- Product formula for an arbitrary odd squarefree wheel. -/
