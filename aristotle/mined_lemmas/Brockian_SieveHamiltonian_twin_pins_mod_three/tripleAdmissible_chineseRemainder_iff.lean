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

theorem tripleAdmissible_chineseRemainder_iff (m n : ℕ) (h : m.Coprime n)
    (a : ZMod (m * n)) :
    TripleAdmissible (m * n) a ↔
      TripleAdmissible m ((ZMod.chineseRemainder h a).1) ∧
      TripleAdmissible n ((ZMod.chineseRemainder h a).2) := by
  set cred := ZMod.chineseRemainder h with hcred
  -- cred is a ring isomorphism, so IsUnit is preserved
  have hunit : ∀ x : ZMod (m * n), IsUnit x ↔ IsUnit (cred x) := by
    intro x
    constructor
    · exact IsUnit.map (f := cred.toRingHom)
    · intro hx
      have heq : x = cred.symm (cred x) := by simp
      rw [heq]
      exact IsUnit.map (f := cred.symm.toRingHom) hx
  have hprod : ∀ p : ZMod m × ZMod n, IsUnit p ↔ IsUnit p.1 ∧ IsUnit p.2 := by
    intro p
    constructor
    · rintro ⟨u, rfl⟩
      exact ⟨IsUnit.map (RingHom.fst (ZMod m) (ZMod n)) ⟨u, rfl⟩,
             IsUnit.map (RingHom.snd (ZMod m) (ZMod n)) ⟨u, rfl⟩⟩
    · rintro ⟨⟨u₁, hu₁⟩, ⟨u₂, hu₂⟩⟩
      use ⟨(u₁, u₂), (u₁⁻¹, u₂⁻¹), by simp, by simp⟩
      simp [hu₁, hu₂]
  -- cred is a ring hom, so it preserves addition
  have hadd : ∀ (x : ZMod (m * n)) (k : ZMod (m * n)), cred (x + k) = cred x + cred k :=
    fun x k => RingEquiv.map_add cred x k
  -- cred maps natural numbers to the same number in both components
  have hconst : ∀ k : ℕ, (cred (k : ZMod (m * n))).1 = (k : ZMod m) ∧ (cred (k : ZMod (m * n))).2 = (k : ZMod n) := by
    intro k
    simp [cred]
  -- Now show the key lemma for addition with small constants
  have ha2 : cred (a + 2) = (⟨(cred a).1 + 2, (cred a).2 + 2⟩ : ZMod m × ZMod n) := by
    rw [hadd]
    have hc2 : cred 2 = ((2 : ZMod m), (2 : ZMod n)) := by
      have := hconst 2
      simp only [Nat.cast_ofNat] at this
      ext <;> simp [this]
    rw [hc2]
    rfl
  -- Helper for other constants
  have ha3 : cred (a + 3) = ((cred a).1 + 3, (cred a).2 + 3) := by
    rw [hadd]
    have hc3 : cred (3 : ZMod (m * n)) = ((3 : ZMod m), (3 : ZMod n)) := by
      have := hconst 3
      simp only [Nat.cast_ofNat] at this
      ext <;> simp [this]
    rw [hc3]; rfl
  have ha5 : cred (a + 5) = ((cred a).1 + 5, (cred a).2 + 5) := by
    rw [hadd]
    have hc5 : cred (5 : ZMod (m * n)) = ((5 : ZMod m), (5 : ZMod n)) := by
      have := hconst 5
      simp only [Nat.cast_ofNat] at this
      ext <;> simp [this]
    rw [hc5]; rfl
  have ha6 : cred (a + 6) = ((cred a).1 + 6, (cred a).2 + 6) := by
    rw [hadd]
    have hc6 : cred (6 : ZMod (m * n)) = ((6 : ZMod m), (6 : ZMod n)) := by
      have := hconst 6
      simp only [Nat.cast_ofNat] at this
      ext <;> simp [this]
    rw [hc6]; rfl
  have ha8 : cred (a + 8) = ((cred a).1 + 8, (cred a).2 + 8) := by
    rw [hadd]
    have hc8 : cred (8 : ZMod (m * n)) = ((8 : ZMod m), (8 : ZMod n)) := by
      have := hconst 8
      simp only [Nat.cast_ofNat] at this
      ext <;> simp [this]
    rw [hc8]; rfl
  -- Now prove the main statement
  unfold TripleAdmissible
  -- Prove for a * (a + 2)
  have hua : IsUnit (a * (a + 2)) ↔
    IsUnit ((cred a).1 * ((cred a).1 + 2)) ∧ IsUnit ((cred a).2 * ((cred a).2 + 2)) := by
    have heq : cred (a * (a + 2)) = ((cred a).1 * ((cred a).1 + 2), (cred a).2 * ((cred a).2 + 2)) := by
      calc cred (a * (a + 2))
          = cred a * cred (a + 2) := RingEquiv.map_mul cred _ _
        _ = cred a * ((cred a).1 + 2, (cred a).2 + 2) := by rw [ha2]
        _ = ((cred a).1 * ((cred a).1 + 2), (cred a).2 * ((cred a).2 + 2)) := by rfl
    rw [hunit, heq, hprod]
  -- Prove for (a + 3) * (a + 5)
  have hub : IsUnit ((a + 3) * (a + 5)) ↔
    IsUnit (((cred a).1 + 3) * ((cred a).1 + 5)) ∧ IsUnit (((cred a).2 + 3) * ((cred a).2 + 5)) := by
    have heq : cred ((a + 3) * (a + 5)) = (((cred a).1 + 3) * ((cred a).1 + 5), ((cred a).2 + 3) * ((cred a).2 + 5)) := by
      calc cred ((a + 3) * (a + 5))
          = cred (a + 3) * cred (a + 5) := RingEquiv.map_mul cred _ _
        _ = ((cred a).1 + 3, (cred a).2 + 3) * ((cred a).1 + 5, (cred a).2 + 5) := by rw [ha3, ha5]
        _ = (((cred a).1 + 3) * ((cred a).1 + 5), ((cred a).2 + 3) * ((cred a).2 + 5)) := by simp
    rw [hunit, heq, hprod]
  -- Prove for (a + 6) * (a + 8)
  have huc : IsUnit ((a + 6) * (a + 8)) ↔
    IsUnit (((cred a).1 + 6) * ((cred a).1 + 8)) ∧ IsUnit (((cred a).2 + 6) * ((cred a).2 + 8)) := by
    have heq : cred ((a + 6) * (a + 8)) = (((cred a).1 + 6) * ((cred a).1 + 8), ((cred a).2 + 6) * ((cred a).2 + 8)) := by
      calc cred ((a + 6) * (a + 8))
          = cred (a + 6) * cred (a + 8) := RingEquiv.map_mul cred _ _
        _ = ((cred a).1 + 6, (cred a).2 + 6) * ((cred a).1 + 8, (cred a).2 + 8) := by rw [ha6, ha8]
        _ = (((cred a).1 + 6) * ((cred a).1 + 8), ((cred a).2 + 6) * ((cred a).2 + 8)) := by rfl
    rw [hunit, heq, hprod]
  rw [hua, hub, huc]
  -- LHS: (A ∧ B) ∧ (C ∧ D) ∧ (E ∧ F)
  -- RHS: (A ∧ C ∧ E) ∧ B ∧ D ∧ F
  tauto

/-- Chinese remaindering makes the triple count multiplicative. -/
