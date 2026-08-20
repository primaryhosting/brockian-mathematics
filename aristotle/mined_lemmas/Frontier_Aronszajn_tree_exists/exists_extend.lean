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

/-
The limit step of the transfinite construction: at a countable limit ordinal `a`
we build a nice partial injection with domain `a` coherent with all previous ones,
by an `ω`-recursion along a cofinal sequence, reserving one new value at each stage
so that the resulting function still omits infinitely many naturals.
-/
import RequestProject.Aronszajn.Step

open Ordinal Cardinal Set

namespace Aronszajn


theorem exists_extend {b c : Ordinal.{0}} (hbc : b ≤ c) {h k : Ordinal.{0} → ℕ}
    (hh : Nice b h) (hk : Nice c k) (hcoh : Coh h k b) {S : Set ℕ} (hSfin : S.Finite)
    (hS : ∀ d < b, h d ∉ S) :
    ∃ h' : Ordinal.{0} → ℕ, Nice c h' ∧ (∀ d < b, h' d = h d) ∧ Coh h' k c ∧
      (∀ d < c, h' d ∉ S) := by
  classical
  obtain ⟨hinj, hnorm, hcoinf⟩ := hh
  obtain ⟨kinj, knorm, kcoinf⟩ := hk
  set F : Set Ordinal.{0} := {d | d < b ∧ h d ≠ k d} with hFdef
  have hFfin : F.Finite := hcoh
  set V : Set ℕ := (h '' F) ∪ S with hVdef
  have hVfin : V.Finite := (hFfin.image h).union hSfin
  set C : Set ℕ := {n | ∀ d < c, k d ≠ n} \ V with hCdef
  have hCinf : C.Infinite := kcoinf.diff hVfin
  obtain ⟨nu, hnuinj, hnuC⟩ := exists_inj_into hCinf
  set P : Set ℕ := (h '' Set.Iio b) ∪ S with hPdef
  -- the new function
  set h' : Ordinal.{0} → ℕ :=
    fun d => if d < b then h d else if d < c then (if k d ∈ P then nu (k d) else k d) else 0
    with hh'def
  -- `C` is disjoint from `P`
  have hCP : ∀ n ∈ C, n ∉ P := by
    rintro n ⟨hnk, hnV⟩ hnP
    rcases hnP with ⟨e, he, rfl⟩ | hnS
    · by_cases hef : h e = k e
      · exact hnk e (lt_of_lt_of_le he hbc) hef.symm
      · exact hnV (Or.inl ⟨e, ⟨he, hef⟩, rfl⟩)
    · exact hnV (Or.inr hnS)
  have hCkval : ∀ n ∈ C, ∀ d < c, k d ≠ n := fun n hn => hn.1
  -- values of `h'`
  have hlow : ∀ d < b, h' d = h d := by
    intro d hd; simp [hh'def, hd]
  have hlowP : ∀ d < b, h' d ∈ P := by
    intro d hd; rw [hlow d hd]; exact Or.inl ⟨d, hd, rfl⟩
  have hhigh : ∀ d, b ≤ d → d < c → (h' d = nu (k d) ∧ k d ∈ P) ∨ (h' d = k d ∧ k d ∉ P) := by
    intro d hbd hdc
    by_cases hkP : k d ∈ P
    · exact Or.inl ⟨by simp [hh'def, not_lt.2 hbd, hdc, hkP], hkP⟩
    · exact Or.inr ⟨by simp [hh'def, not_lt.2 hbd, hdc, hkP], hkP⟩
  have hhighnotP : ∀ d, b ≤ d → d < c → h' d ∉ P := by
    intro d hbd hdc
    rcases hhigh d hbd hdc with ⟨he, -⟩ | ⟨he, hkP⟩
    · rw [he]; exact hCP _ (hnuC _)
    · rw [he]; exact hkP
  -- `D`, the finite set of repaired positions
  set D : Set Ordinal.{0} := {d | d < c ∧ k d ∈ (h '' F) ∪ S} with hDdef
  have hDfin : D.Finite := finite_preimage_of_injBelow kinj hVfin
  have hDsub : ∀ d, b ≤ d → d < c → k d ∈ P → d ∈ D := by
    intro d hbd hdc hkP
    refine ⟨hdc, ?_⟩
    rcases hkP with ⟨e, he, hek⟩ | hnS
    · by_cases hef : h e = k e
      · exact absurd (kinj e (lt_of_lt_of_le he hbc) d hdc (by rw [hef] at hek; exact hek))
          (by intro hh2; exact absurd (hh2 ▸ he) (not_lt.2 hbd))
      · exact Or.inl ⟨e, ⟨he, hef⟩, hek⟩
    · exact Or.inr hnS
  refine ⟨h', ⟨?_, ?_, ?_⟩, hlow, ?_, ?_⟩
  · -- injectivity
    intro d hd e he hde
    rcases lt_or_ge d b with hdb | hdb
    · rcases lt_or_ge e b with heb | heb
      · exact hinj d hdb e heb (by rw [← hlow d hdb, ← hlow e heb]; exact hde)
      · exact absurd (hde ▸ hlowP d hdb) (hhighnotP e heb he)
    · rcases lt_or_ge e b with heb | heb
      · exact absurd (hde ▸ hlowP e heb) (by rw [← hde] at *; exact hhighnotP d hdb hd)
      · rcases hhigh d hdb hd with ⟨hd1, hd2⟩ | ⟨hd1, hd2⟩ <;>
          rcases hhigh e heb he with ⟨he1, he2⟩ | ⟨he1, he2⟩
        · exact kinj d hd e he (hnuinj (by rw [← hd1, ← he1]; exact hde))
        · exact absurd (by rw [← he1, ← hde, hd1] : k e = nu (k d))
            (hCkval _ (hnuC (k d)) e he)
        · exact absurd (by rw [← hd1, hde, he1] : k d = nu (k e))
            (hCkval _ (hnuC (k e)) d hd)
        · exact kinj d hd e he (by rw [← hd1, ← he1]; exact hde)
  · -- normalization
    intro d hcd
    have : ¬ d < b := not_lt.2 (le_trans hbc hcd)
    simp [hh'def, this, not_lt.2 hcd]
  · -- coinfinite
    have hsub : ({n | ∀ d < c, k d ≠ n} \ (V ∪ nu '' (k '' D))) ⊆ {n | ∀ d < c, h' d ≠ n} := by
      rintro n ⟨hnk, hnV⟩ d hd hdn
      rcases lt_or_ge d b with hdb | hdb
      · rw [hlow d hdb] at hdn
        by_cases hef : h d = k d
        · exact hnk d hd (by rw [← hef]; exact hdn)
        · exact hnV (Or.inl (Or.inl ⟨d, ⟨hdb, hef⟩, hdn⟩))
      · rcases hhigh d hdb hd with ⟨hd1, hd2⟩ | ⟨hd1, -⟩
        · exact hnV (Or.inr ⟨k d, ⟨d, hDsub d hdb hd hd2, rfl⟩, by rw [← hd1]; exact hdn⟩)
        · exact hnk d hd (by rw [← hd1]; exact hdn)
    exact Set.Infinite.mono hsub
      (kcoinf.diff (hVfin.union ((hDfin.image k).image nu)))
  · -- coherence with `k`
    apply Set.Finite.subset (hFfin.union hDfin)
    rintro d ⟨hd, hne⟩
    rcases lt_or_ge d b with hdb | hdb
    · refine Or.inl ⟨hdb, ?_⟩
      rw [hlow d hdb] at hne; exact hne
    · rcases hhigh d hdb hd with ⟨-, hd2⟩ | ⟨hd1, -⟩
      · exact Or.inr (hDsub d hdb hd hd2)
      · exact absurd hd1 hne
  · -- still avoids `S`
    intro d hd
    rcases lt_or_ge d b with hdb | hdb
    · rw [hlow d hdb]; exact hS d hdb
    · exact fun hmem => hhighnotP d hdb hd (Or.inr hmem)

end Aronszajn

/-
# Aronszajn Tree Exists
Category: Frontier — Set Theory
Target: Frontier.Aronszajn_tree_exists
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/
import RequestProject.Aronszajn.Tree

open Ordinal Cardinal Set

namespace Frontier

/-- **An Aronszajn tree exists.**

There is a partial order `(T, le)` together with a level function `lvl : T → Ordinal`
such that:

* the predecessors of any node are linearly ordered by `le`, and `lvl` restricts to an
  order isomorphism from them onto the ordinals `< lvl x` (so `T` is a tree and `lvl x`
  is the order type of the set of predecessors of `x`);
* every node has level `< ω₁` and every ordinal `< ω₁` occurs as a level, i.e. the tree
  has height `ω₁`;
* every level of the tree is countable;
* every chain of `T` — in particular every branch — is countable.

The tree is constructed as the tree of finite modifications of a coherent sequence
`Aronszajn.E` of injections `a → ℕ` (`a < ω₁`), ordered by end-extension. -/
