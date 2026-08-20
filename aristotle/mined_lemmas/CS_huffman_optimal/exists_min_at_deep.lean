/-
# Huffman Optimal
Category: Computer Science
Target: CS.huffman_optimal
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/
import Mathlib

/-!
# Huffman Optimal
Category: Computer Science
Target: CS.huffman_optimal
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)

(Lean 4 requires `import` to be the first command in a file, so the header above the
import is a plain block comment and this is its module-docstring copy.)
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

/-!
## Binary code trees

A binary prefix code for a finite set of weighted symbols is (up to the irrelevant
choice of which child is `0` and which is `1`) the same thing as a binary tree whose
leaves carry the weights of the symbols.  The expected codeword length of the code is
the *weighted external path length* of the tree, i.e. `∑ᵢ wᵢ * depthᵢ`.
-/

/-- A binary code tree: leaves carry a (nonnegative) weight. -/
inductive HTree : Type
  | leaf : ℝ → HTree
  | node : HTree → HTree → HTree
  deriving Inhabited

namespace HTree

/-- Total weight of a tree, i.e. the sum of the weights of its leaves. -/

lemma exists_min_at_deep (M₁ : Multiset (ℝ × ℕ)) (x a : ℝ) (d : ℕ)
    (hd : ∀ p ∈ ((x, d) ::ₘ M₁), p.2 ≤ d)
    (ha : ∀ w ∈ (((x, d) ::ₘ M₁).map Prod.fst), a ≤ w)
    (hmem : a ∈ (((x, d) ::ₘ M₁).map Prod.fst)) :
    ∃ M₁' : Multiset (ℝ × ℕ),
      ((a, d) ::ₘ M₁').map Prod.fst = ((x, d) ::ₘ M₁).map Prod.fst ∧
      ((a, d) ::ₘ M₁').map Prod.snd = ((x, d) ::ₘ M₁).map Prod.snd ∧
      wcost ((a, d) ::ₘ M₁') ≤ wcost ((x, d) ::ₘ M₁) := by
  by_cases hx : a = x
  · exact ⟨M₁, by rw [hx], by rw [hx], by rw [hx]⟩
  · have hmem' : a ∈ M₁.map Prod.fst := by
      rw [Multiset.map_cons, Multiset.mem_cons] at hmem
      exact hmem.resolve_left hx
    obtain ⟨p, hp, hpa⟩ := Multiset.mem_map.mp hmem'
    obtain ⟨E, hE⟩ := Multiset.exists_cons_of_mem hp
    have hax : a ≤ x := ha x (by simp)
    have hpd : p.2 ≤ d := hd p (by rw [Multiset.mem_cons]; exact Or.inr hp)
    refine ⟨(x, p.2) ::ₘ E, ?_, ?_, ?_⟩
    · rw [hE]
      simp only [Multiset.map_cons]
      rw [← hpa]
      exact Multiset.cons_swap _ _ _
    · rw [hE]
      simp only [Multiset.map_cons]
    · rw [hE]
      simp only [wcost_cons]
      have hp1 : p.1 = a := hpa
      rw [hp1]
      have hcast : (p.2 : ℝ) ≤ (d : ℝ) := Nat.cast_le.mpr hpd
      nlinarith [sub_nonneg.mpr hax, sub_nonneg.mpr hcast]

/-!
## Optimality
-/

/-- Rescaling the Kraft sum from one bound `D` to a larger bound `D'`. -/
