/-
# Polya Isomer Count
Category: Chemistry
Target: Chem.polya_isomer_count
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/
-- (The header above uses `/-` rather than `/-!` only because Lean requires all module
-- docstrings to appear *after* the `import` lines; the text is otherwise verbatim.)
import Mathlib

/-!
# Polya Isomer Count
Category: Chemistry
Target: Chem.polya_isomer_count
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open scoped BigOperators
open scoped Nat

set_option maxHeartbeats 1000000
set_option relaxedAutoImplicit false
set_option autoImplicit false

namespace Chem

open MulAction

attribute [local instance] arrowAction

/-- If a colouring `f` of the skeleton positions is invariant under the symmetry `g`,
then it is invariant under every integer power of `g`. -/
private lemma colouring_zpow_invariant {G : Type*} {α : Type*} {β : Type*} [Group G]
    [MulAction G α] (g : G) (f : α → β) (hf : ∀ a, f (g • a) = f a) (n : ℤ) (a : α) :
    f (g ^ n • a) = f a := by
  have hinv : ∀ a : α, f (g⁻¹ • a) = f a := by
    intro a
    have h := hf (g⁻¹ • a)
    rw [smul_inv_smul] at h
    exact h.symm
  induction n using Int.induction_on generalizing a with
  | zero => simp
  | succ k ih =>
      have h1 : g ^ ((k : ℤ) + 1) • a = g ^ (k : ℤ) • (g • a) := by
        rw [zpow_add_one, mul_smul]
      rw [h1, ih, hf]
  | pred k ih =>
      have h1 : g ^ (-(k : ℤ) - 1) • a = g ^ (-(k : ℤ)) • (g⁻¹ • a) := by
        rw [zpow_sub_one, mul_smul]
      rw [h1, ih, hinv]

/-- Colourings fixed by a symmetry `g` are exactly the colourings that are constant on the
cycles (orbits of `⟨g⟩`) of `g`. -/
private def fixedColouringEquiv {G : Type*} {α : Type*} {β : Type*} [Group G]
    [MulAction G α] (g : G) :
    (fixedBy (α → β) g) ≃ (orbitRel.Quotient (Subgroup.zpowers g) α → β) where
  toFun f := by
    refine Quotient.lift (fun a => (f : α → β) a) ?_
    rintro a b hab
    have hfix : g • (f : α → β) = (f : α → β) := f.2
    have hf : ∀ a : α, (f : α → β) (g • a) = (f : α → β) a := by
      intro a
      have h2 : (g • (f : α → β)) (g • a) = (f : α → β) (g • a) := congrFun hfix (g • a)
      have h3 : (g • (f : α → β)) (g • a) = (f : α → β) a := by
        show (f : α → β) (g⁻¹ • (g • a)) = (f : α → β) a
        rw [inv_smul_smul]
      rw [← h2]
      exact h3
    obtain ⟨⟨x, hx⟩, hxb⟩ := hab
    obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.mp hx
    have hba : g ^ n • b = a := by simpa using hxb
    show (f : α → β) a = (f : α → β) b
    rw [← hba, colouring_zpow_invariant g _ hf]
  invFun F := by
    refine ⟨fun a => F (Quotient.mk _ a), ?_⟩
    rw [mem_fixedBy]
    funext a
    show F (Quotient.mk _ (g⁻¹ • a)) = F (Quotient.mk _ a)
    congr 1
    exact Quotient.sound ⟨⟨g⁻¹, Subgroup.mem_zpowers_iff.mpr ⟨-1, by simp⟩⟩, rfl⟩
  left_inv f := by ext a; rfl
  right_inv F := by
    funext q
    induction q using Quotient.inductionOn with
    | _ a => rfl

/-- **Pólya / Burnside isomer count.**
For a finite symmetry group `G` acting on the substitution positions `α` of a molecular
skeleton, with `β` the (finite) set of substituents, the number of distinct substitution
isomers (orbits of colourings `α → β` under `G`), multiplied by `|G|`, equals the sum over
group elements `g` of `|β| ^ (number of cycles of `g` on the positions)`; i.e. the number of
isomers is the Pólya cycle-index average `(1/|G|) ∑_g |β|^{c(g)}`. -/
theorem polya_isomer_count (G : Type*) [Group G] [Fintype G] (α : Type*) [Fintype α]
    (β : Type*) [Finite β] [MulAction G α] :
    Nat.card (orbitRel.Quotient G (α → β)) * Nat.card G
      = ∑ g : G, Nat.card β ^ Nat.card (orbitRel.Quotient (Subgroup.zpowers g) α) := by
  classical
  have key : ∀ g : G, Nat.card (fixedBy (α → β) g)
      = Nat.card β ^ Nat.card (orbitRel.Quotient (Subgroup.zpowers g) α) := by
    intro g
    rw [Nat.card_congr (fixedColouringEquiv g), Nat.card_fun]
  haveI : ∀ a : G, Fintype (fixedBy (α → β) a) := fun _ => Fintype.ofFinite _
  haveI : Fintype (Quotient (orbitRel G (α → β))) := Fintype.ofFinite _
  have burnside := MulAction.sum_card_fixedBy_eq_card_orbits_mul_card_group G (α → β)
  simp only [← Nat.card_eq_fintype_card] at burnside
  rw [← burnside]
  exact Finset.sum_congr rfl (fun g _ => key g)

/-- The Pólya cycle-index average form of the isomer count: the number of substitution
isomers equals `(1/|G|) ∑_{g ∈ G} |β| ^ c(g)`, where `c(g)` is the number of cycles of `g`
acting on the substitution positions. -/
theorem polya_isomer_count_eq_average (G : Type*) [Group G] [Fintype G] (α : Type*) [Fintype α]
    (β : Type*) [Finite β] [MulAction G α] :
    Nat.card (orbitRel.Quotient G (α → β))
      = (∑ g : G, Nat.card β ^ Nat.card (orbitRel.Quotient (Subgroup.zpowers g) α))
          / Nat.card G := by
  have hG : 0 < Nat.card G := Nat.card_pos
  rw [← polya_isomer_count G α β, Nat.mul_div_cancel _ hG]

end Chem

