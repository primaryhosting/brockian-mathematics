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

theorem hc_le_wcost : ∀ (n : ℕ) (M : Multiset (ℝ × ℕ)), (M.map Prod.snd).sum = n →
    M ≠ 0 → (∀ p ∈ M, 0 ≤ p.1) → KraftLe (M.map Prod.snd) →
    hc (M.map Prod.fst) ≤ wcost M := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n IH =>
  intro M hn hM0 hnn hK
  have hnnw : ∀ w ∈ M.map Prod.fst, 0 ≤ w := by
    intro w hw
    obtain ⟨p, hp, rfl⟩ := Multiset.mem_map.mp hw
    exact hnn p hp
  by_cases hcard : Multiset.card M = 1
  · obtain ⟨p, rfl⟩ := Multiset.card_eq_one.mp hcard
    have h1 : 0 ≤ p.1 := hnn p (Multiset.mem_singleton_self p)
    rw [Multiset.map_singleton, hc_singleton, wcost, Multiset.map_singleton,
      Multiset.sum_singleton]
    positivity
  · have hcard2 : 2 ≤ Multiset.card M := by
      have h0 : Multiset.card M ≠ 0 := fun h => hM0 (Multiset.card_eq_zero.mp h)
      omega
    obtain ⟨q, hq, hqmax⟩ := Multiset.exists_max_image (f := Prod.snd) hM0
    obtain ⟨M₀, hM₀⟩ := Multiset.exists_cons_of_mem hq
    have hM₀0 : M₀ ≠ 0 := by
      intro h
      rw [hM₀, h] at hcard2
      simp at hcard2
    by_cases hex : ∃ r ∈ M₀, r.2 = q.2
    · -- The generic case: two leaves of maximal depth `d`.
      obtain ⟨r, hrmem, hrd⟩ := hex
      obtain ⟨M₁, hM₁⟩ := Multiset.exists_cons_of_mem hrmem
      have hr_eta : ((r.1, q.2) : ℝ × ℕ) = r := by rw [← hrd]
      have hMeq : M = (q.1, q.2) ::ₘ ((r.1, q.2) ::ₘ M₁) := by rw [hr_eta, hM₀, hM₁]
      set d : ℕ := q.2 with hd_def
      have hdall : ∀ p ∈ M, p.2 ≤ d := hqmax
      have hallsnd : ∀ e ∈ M.map Prod.snd, e ≤ d := by
        intro e he
        obtain ⟨p, hp, rfl⟩ := Multiset.mem_map.mp he
        exact hdall p hp
      have hh := hK d hallsnd
      rw [hMeq] at hh
      simp only [Multiset.map_cons, Multiset.sum_cons, Nat.sub_self, pow_zero] at hh
      have hd1 : 1 ≤ d := by
        by_contra hcon
        have hd0 : d = 0 := by omega
        rw [hd0] at hh
        simp only [pow_zero] at hh
        omega
      -- the two lightest weights are moved to the two deepest slots
      obtain ⟨pa, hpa, hpamin⟩ := Multiset.exists_min_image (f := Prod.fst) hM0
      set a : ℝ := pa.1 with ha_def
      have hamem : a ∈ M.map Prod.fst := Multiset.mem_map_of_mem _ hpa
      have hamin : ∀ w ∈ M.map Prod.fst, a ≤ w := by
        intro w hw
        obtain ⟨p, hp, rfl⟩ := Multiset.mem_map.mp hw
        exact hpamin p hp
      obtain ⟨N₁, hN₁f, hN₁s, hN₁c⟩ :=
        exists_min_at_deep ((r.1, d) ::ₘ M₁) q.1 a d
          (by rw [← hMeq]; exact hdall) (by rw [← hMeq]; exact hamin)
          (by rw [← hMeq]; exact hamem)
      rw [← hMeq] at hN₁f hN₁s hN₁c
      have hN₁snd : N₁.map Prod.snd = d ::ₘ M₁.map Prod.snd := by
        have h1 : d ::ₘ N₁.map Prod.snd = d ::ₘ (d ::ₘ M₁.map Prod.snd) := by
          have := hN₁s
          rw [hMeq] at this
          simpa using this
        exact (Multiset.cons_inj_right d).mp h1
      have hdmem : d ∈ N₁.map Prod.snd := by
        rw [hN₁snd]; exact Multiset.mem_cons_self _ _
      obtain ⟨s0, hs0, hs0d⟩ := Multiset.mem_map.mp hdmem
      obtain ⟨N₂, hN₂⟩ := Multiset.exists_cons_of_mem hs0
      have hN₁eq : N₁ = (s0.1, d) ::ₘ N₂ := by rw [hN₂, ← hs0d]
      have hN₁0 : N₁ ≠ 0 := by
        rw [hN₁eq]; exact Multiset.cons_ne_zero
      have hN₁depth : ∀ p ∈ N₁, p.2 ≤ d := by
        intro p hp
        have : p.2 ∈ N₁.map Prod.snd := Multiset.mem_map_of_mem _ hp
        rw [hN₁snd] at this
        rcases Multiset.mem_cons.mp this with h | h
        · omega
        · obtain ⟨p', hp', hp'2⟩ := Multiset.mem_map.mp h
          have hp'M : p' ∈ M := by
            rw [hM₀, hM₁]
            exact Multiset.mem_cons_of_mem (Multiset.mem_cons_of_mem hp')
          have := hdall p' hp'M
          omega
      obtain ⟨pb, hpb, hpbmin⟩ := Multiset.exists_min_image (f := Prod.fst) hN₁0
      set b : ℝ := pb.1 with hb_def
      have hbmem : b ∈ N₁.map Prod.fst := Multiset.mem_map_of_mem _ hpb
      have hbmin : ∀ w ∈ N₁.map Prod.fst, b ≤ w := by
        intro w hw
        obtain ⟨p, hp, rfl⟩ := Multiset.mem_map.mp hw
        exact hpbmin p hp
      obtain ⟨N₂', hN₂'f, hN₂'s, hN₂'c⟩ :=
        exists_min_at_deep N₂ s0.1 b d
          (by rw [← hN₁eq]; exact hN₁depth) (by rw [← hN₁eq]; exact hbmin)
          (by rw [← hN₁eq]; exact hbmem)
      rw [← hN₁eq] at hN₂'f hN₂'s hN₂'c
      -- the rearranged configuration
      have hfst : a ::ₘ b ::ₘ N₂'.map Prod.fst = M.map Prod.fst := by
        have h1 : b ::ₘ N₂'.map Prod.fst = N₁.map Prod.fst := by simpa using hN₂'f
        have h2 : a ::ₘ N₁.map Prod.fst = M.map Prod.fst := by simpa using hN₁f
        rw [h1, h2]
      have hsnd : d ::ₘ d ::ₘ N₂'.map Prod.snd = M.map Prod.snd := by
        have h1 : d ::ₘ N₂'.map Prod.snd = N₁.map Prod.snd := by simpa using hN₂'s
        have h2 : d ::ₘ N₁.map Prod.snd = M.map Prod.snd := by simpa using hN₁s
        rw [h1, h2]
      have hcostle : wcost ((a, d) ::ₘ (b, d) ::ₘ N₂') ≤ wcost M := by
        have h1 : wcost ((b, d) ::ₘ N₂') ≤ wcost N₁ := hN₂'c
        have h2 : wcost ((a, d) ::ₘ N₁) ≤ wcost M := hN₁c
        rw [wcost_cons] at h2 ⊢
        simp only at h2 ⊢
        linarith
      -- apply the induction hypothesis to the merged configuration
      have hbmem' : b ∈ M.map Prod.fst := by rw [← hfst]; simp
      have hab : a ≤ b := hamin b hbmem'
      have hbmin' : ∀ w ∈ N₂'.map Prod.fst, b ≤ w := by
        intro w hw
        refine hbmin w ?_
        have h1 : b ::ₘ N₂'.map Prod.fst = N₁.map Prod.fst := by simpa using hN₂'f
        rw [← h1]
        exact Multiset.mem_cons_of_mem hw
      have ha0 : 0 ≤ a := hnnw a hamem
      have hb0 : 0 ≤ b := hnnw b hbmem'
      have hN₂'nn : ∀ p ∈ N₂', 0 ≤ p.1 := by
        intro p hp
        refine hnnw p.1 ?_
        rw [← hfst]
        exact Multiset.mem_cons_of_mem (Multiset.mem_cons_of_mem (Multiset.mem_map_of_mem _ hp))
      have hsumT : ((((a + b, d - 1) : ℝ × ℕ) ::ₘ N₂').map Prod.snd).sum < n := by
        have h1 : (M.map Prod.snd).sum = d + (d + (N₂'.map Prod.snd).sum) := by
          rw [← hsnd]; simp
        simp only [Multiset.map_cons, Multiset.sum_cons]
        omega
      have hIH := IH _ hsumT ((a + b, d - 1) ::ₘ N₂') rfl Multiset.cons_ne_zero
        (by
          intro p hp
          rcases Multiset.mem_cons.mp hp with rfl | hp
          · simpa using add_nonneg ha0 hb0
          · exact hN₂'nn p hp)
        (by
          simp only [Multiset.map_cons]
          refine kraft_merge d hd1 (N₂'.map Prod.snd) ?_ (by rw [hsnd]; exact hK)
          intro e he
          refine hallsnd e ?_
          rw [← hsnd]
          exact Multiset.mem_cons_of_mem (Multiset.mem_cons_of_mem he))
      simp only [Multiset.map_cons] at hIH
      have hcast : ((d - 1 : ℕ) : ℝ) = (d : ℝ) - 1 := by
        have : ((d : ℝ) - 1) = ((d - 1 : ℕ) : ℝ) := by
          rw [Nat.cast_sub hd1]; norm_num
        linarith
      calc hc (M.map Prod.fst) = hc (a ::ₘ b ::ₘ N₂'.map Prod.fst) := by rw [hfst]
        _ = (a + b) + hc ((a + b) ::ₘ N₂'.map Prod.fst) := hc_cons2 a b _ hab hbmin'
        _ ≤ (a + b) + wcost ((a + b, d - 1) ::ₘ N₂') := by linarith
        _ = wcost ((a, d) ::ₘ (b, d) ::ₘ N₂') := by
              rw [wcost_cons, wcost_cons, wcost_cons]
              simp only [hcast]
              ring
        _ ≤ wcost M := hcostle
    · -- Only one leaf of maximal depth: lower it by one level.
      have hlt : ∀ p ∈ M₀, p.2 < q.2 := by
        intro p hp
        exact lt_of_le_of_ne (hqmax p (by rw [hM₀]; exact Multiset.mem_cons_of_mem hp))
          (fun h => hex ⟨p, hp, h⟩)
      obtain ⟨r, hr⟩ := Multiset.exists_mem_of_ne_zero hM₀0
      have hd1 : 1 ≤ q.2 := by have := hlt r hr; omega
      have hMsnd : M.map Prod.snd = q.2 ::ₘ M₀.map Prod.snd := by rw [hM₀]; simp
      have hltm : ∀ e ∈ M₀.map Prod.snd, e < q.2 := by
        intro e he
        obtain ⟨p, hp, rfl⟩ := Multiset.mem_map.mp he
        exact hlt p hp
      have hq0 : 0 ≤ q.1 := hnn q hq
      have hfst : (((q.1, q.2 - 1) : ℝ × ℕ) ::ₘ M₀).map Prod.fst = M.map Prod.fst := by
        rw [hM₀]; simp
      have hsum : ((((q.1, q.2 - 1) : ℝ × ℕ) ::ₘ M₀).map Prod.snd).sum < n := by
        have h1 : (M.map Prod.snd).sum = q.2 + (M₀.map Prod.snd).sum := by rw [hMsnd]; simp
        simp only [Multiset.map_cons, Multiset.sum_cons]
        omega
      have hIH := IH _ hsum (((q.1, q.2 - 1) : ℝ × ℕ) ::ₘ M₀) rfl Multiset.cons_ne_zero
        (by
          intro p hp
          rcases Multiset.mem_cons.mp hp with rfl | hp
          · simpa using hq0
          · exact hnn p (by rw [hM₀]; exact Multiset.mem_cons_of_mem hp))
        (by
          simp only [Multiset.map_cons]
          exact kraft_lower_one q.2 hd1 (M₀.map Prod.snd) hltm (by rw [← hMsnd]; exact hK))
      rw [hfst] at hIH
      refine hIH.trans ?_
      have hcast : ((q.2 - 1 : ℕ) : ℝ) = (q.2 : ℝ) - 1 := by
        have : ((q.2 : ℝ) - 1) = ((q.2 - 1 : ℕ) : ℝ) := by
          rw [Nat.cast_sub hd1]; norm_num
        linarith
      rw [hM₀, wcost_cons, wcost_cons]
      simp only [hcast]
      have : q.1 * ((q.2 : ℝ) - 1) ≤ q.1 * (q.2 : ℝ) := by nlinarith
      linarith

/-- **Huffman coding is optimal.**  For any list of nonnegative weights `ws` (e.g. the
probabilities of the symbols of a source), the Huffman tree `huffman ws` has the right
leaf weights (`huffman_leaves`) and its expected codeword length `cost` is minimal
among all binary prefix codes (binary trees) with the same multiset of leaf weights. -/
