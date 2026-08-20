/-
# The infinite Ramsey theorem

Mathlib (as of this project's pinned version) contains no form of Ramsey's theorem, so we develop
the infinite version here, for colourings of `n`-element subsets of `ℕ` with `k` colours.

An infinite homogeneous set is presented as the range of a strictly monotone function `f : ℕ → ℕ`.
-/
import Mathlib

set_option autoImplicit false

namespace Frontier

open Finset

/-- `Homogeneous n c f a` says that every `n`-element subset of the range of `f` has colour `a`. -/

theorem infinite_ramsey (n k : ℕ) (c : Finset ℕ → Fin k) :
    ∃ f : ℕ → ℕ, StrictMono f ∧ ∃ a : Fin k, Homogeneous n c f a := by
  classical
  induction n generalizing c with
  | zero =>
      refine ⟨id, strictMono_id, c ∅, ?_⟩
      intro s hs
      rw [Finset.card_eq_zero] at hs
      subst hs
      simp
  | succ n IH =>
      rcases isEmpty_or_nonempty (Fin k) with hk | hk
      · exact (hk.false (c ∅)).elim
      -- one step of thinning, packaged for the recursion
      have key : ∀ g : {g : ℕ → ℕ // StrictMono g},
          ∃ p : {g : ℕ → ℕ // StrictMono g} × Fin k,
            (∀ i, g.1 0 < p.1.1 i) ∧ (∀ i, ∃ j, p.1.1 i = g.1 j) ∧
            ∀ s : Finset ℕ, s.card = n → c (insert (g.1 0) (s.image p.1.1)) = p.2 := by
        intro g
        obtain ⟨g', b, hg'mono, h1, h2, h3⟩ := ramsey_step IH c g.1 g.2
        exact ⟨(⟨g', hg'mono⟩, b), h1, h2, h3⟩
      choose F hF1 hF2 hF3 using key
      -- the nested sequence of reservoirs
      set G : ℕ → {g : ℕ → ℕ // StrictMono g} :=
        fun i => Nat.rec ⟨id, strictMono_id⟩ (fun _ g => (F g).1) i with hGdef
      set a : ℕ → ℕ := fun i => (G i).1 0 with hadef
      set α : ℕ → Fin k := fun i => (F (G i)).2 with hαdef
      have hrange : ∀ j i, i ≤ j → ∀ x, ∃ y, (G j).1 x = (G i).1 y := by
        intro j
        induction j with
        | zero =>
            intro i hi x
            obtain rfl : i = 0 := Nat.le_zero.mp hi
            exact ⟨x, rfl⟩
        | succ j ihj =>
            intro i hi x
            rcases eq_or_lt_of_le hi with rfl | h
            · exact ⟨x, rfl⟩
            · have hij : i ≤ j := Nat.lt_succ_iff.mp h
              obtain ⟨y, hy⟩ := hF2 (G j) x
              obtain ⟨z, hz⟩ := ihj i hij y
              exact ⟨z, by rw [show (G (j + 1)).1 x = (F (G j)).1.1 x from rfl, hy, hz]⟩
      have hamono : StrictMono a := strictMono_nat_of_lt_succ fun i => hF1 (G i) 0
      have hkey : ∀ i (t : Finset ℕ), t.card = n → (∀ x ∈ t, x ∈ Set.range (G (i + 1)).1) →
          c (insert (a i) t) = α i := by
        intro i t htc hmem
        obtain ⟨s, hs, hst⟩ := exists_preimage_finset t hmem
        rw [← hst]
        exact hF3 (G i) s (by rw [hs, htc])
      -- pigeonhole on the colours attached to the successive first elements
      obtain ⟨y, hy⟩ := Finite.exists_infinite_fiber α
      have hinf : {i | α i = y}.Infinite := Set.infinite_coe_iff.mp hy
      set φ := Nat.nth (fun i => α i = y) with hφdef
      have hφ : StrictMono φ := Nat.nth_strictMono hinf
      have hφmem : ∀ i, α (φ i) = y := Nat.nth_mem_of_infinite hinf
      have hinj : Function.Injective fun i => a (φ i) := fun x z h => (hamono.comp hφ).injective h
      refine ⟨fun i => a (φ i), hamono.comp hφ, y, ?_⟩
      intro s hs
      have hne : s.Nonempty := Finset.card_pos.mp (by omega)
      have hi0 : s.min' hne ∈ s := s.min'_mem hne
      have himg : s.image (fun i => a (φ i))
          = insert (a (φ (s.min' hne))) ((s.erase (s.min' hne)).image fun i => a (φ i)) := by
        conv_lhs => rw [← Finset.insert_erase hi0]
        rw [Finset.image_insert]
      rw [himg, hkey (φ (s.min' hne))]
      · exact hφmem _
      · rw [Finset.card_image_of_injective _ hinj, Finset.card_erase_of_mem hi0, hs]
        omega
      · intro x hx
        simp only [Finset.mem_image, Finset.mem_erase] at hx
        obtain ⟨z, ⟨hzne, hzs⟩, rfl⟩ := hx
        have hlt : s.min' hne < z := lt_of_le_of_ne (s.min'_le z hzs) (Ne.symm hzne)
        have hle : φ (s.min' hne) + 1 ≤ φ z := hφ hlt
        obtain ⟨w, hw⟩ := hrange (φ z) (φ (s.min' hne) + 1) hle 0
        exact ⟨w, hw.symm⟩

end Frontier

/-
# Paris Harrington
Category: Frontier — Set Theory
Target: Frontier.Paris_Harrington
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)

(The header above is the requested header comment; Lean 4 does not allow a module docstring
`/-! ... -/` to precede `import`, so it is written as an ordinary block comment.)

The Paris–Harrington theorem consists of two halves:

* the *strengthened finite Ramsey theorem* is **true**;
* it is **not provable in Peano arithmetic**.

The second half is a metamathematical statement about the theory `PA`; formalising it would require
a full development of first-order arithmetic together with the Paris–Harrington indicator argument,
and it is not attempted here.  What is formalised and proved here is the mathematical content: the
strengthened finite Ramsey theorem itself, `Frontier.Paris_Harrington`, proved (as in the original
argument) from the infinite Ramsey theorem by a compactness argument.  Mathlib contains no Ramsey
theorem, so the infinite Ramsey theorem is developed from scratch in
`RequestProject.InfiniteRamsey`; the compactness step is carried out with a non-principal
ultrafilter (`Filter.hyperfilter ℕ`) instead of König's lemma.
-/
import RequestProject.InfiniteRamsey

set_option autoImplicit false

namespace Frontier

open Finset Filter

/-- A finite set of natural numbers is *relatively large* if it is nonempty and has at least as
many elements as its least element. -/
