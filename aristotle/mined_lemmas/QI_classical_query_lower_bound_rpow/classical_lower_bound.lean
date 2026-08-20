import Mathlib
import RequestProject.Simon.Basic
import RequestProject.Simon.Classical
import RequestProject.Simon.Quantum
import RequestProject.Simon.Solve

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

set_option grind.warning false

/-!
# Simon's problem: `O(n)` quantum queries, `Ω(2 ^ (n / 2))` classical queries

`QI.simon_algorithm` collects the two halves of the classical/quantum
separation for Simon's problem.  An instance is a function
`f : BV n → BV n` on `n`-bit strings satisfying Simon's promise
`IsSimon f s`: `s ≠ 0` and `f x = f y ↔ y = x ∨ y = x + s`.  The task is to
output the hidden shift `s`.

*Quantum upper bound.*  Each round of Simon's algorithm uses exactly **one**
query: it prepares `2 ^ (-n/2) ∑ₓ |x⟩|f x⟩`, applies the Hadamard transform to
the first register and measures.  The resulting distribution `prob f` is
uniform on the hyperplane `{y | ⟪y, s⟫ = 0}` orthogonal to `s`.  After
`2 * n` such rounds — i.e. `2 * n = O(n)` queries — the outcomes fail to pin
down `s` (as the unique nonzero solution of the linear system `⟪yᵢ, t⟫ = 0`)
only with probability at most `2 ^ (-n)`.

*Classical lower bound.*  A deterministic classical query algorithm that always
outputs the hidden shift after `q` queries must satisfy `2 ^ n ≤ (q + 2) ^ 2`,
i.e. `q ≥ 2 ^ (n / 2) - 2 = Ω(2 ^ (n / 2))`.
-/

namespace QI

/-- The classical lower bound in the form `2 ^ (n / 2) ≤ q + 2`. -/

theorem classical_lower_bound {n q : ℕ} (A : QueryAlg n) (hq : q * q + 3 ≤ 2 ^ n) :
    ∃ (f : BV n → BV n) (s : BV n), IsSimon f s ∧ result A f q ≠ s := by
  classical
  -- the (at most `q`) points queried when the oracle is the identity
  set X : Finset (BV n) := (Finset.range q).image (fun k => query A id k) with hXdef
  have hXcard : X.card ≤ q := le_trans (Finset.card_image_le) (by simp)
  -- the forbidden shifts
  set D : Finset (BV n) := ((X ×ˢ X).image (fun p => p.1 + p.2)) ∪ {0} with hDdef
  have hDcard : D.card ≤ q * q + 1 := by
    refine le_trans (Finset.card_union_le _ _) ?_
    have h1 : ((X ×ˢ X).image (fun p => p.1 + p.2)).card ≤ q * q := by
      refine le_trans Finset.card_image_le ?_
      rw [Finset.card_product]
      exact Nat.mul_le_mul hXcard hXcard
    simpa using Nat.add_le_add h1 (le_of_eq (Finset.card_singleton 0))
  -- there are at least two admissible shifts
  have hcompl : 1 < (Finset.univ \ D).card := by
    have hcard : (Finset.univ \ D).card = 2 ^ n - D.card := by
      rw [Finset.card_sdiff, Finset.inter_univ, Finset.card_univ, card_bv]
    have hD : D.card ≤ 2 ^ n := le_trans hDcard (by omega)
    omega
  obtain ⟨s, hsD, t, htD, hst⟩ := Finset.one_lt_card.1 hcompl
  have hmem : ∀ u ∈ Finset.univ \ D, u ≠ 0 ∧ ∀ x ∈ X, ∀ y ∈ X, x + y ≠ u := by
    intro u hu
    have hu' : u ∉ D := (Finset.mem_sdiff.1 hu).2
    constructor
    · intro h0
      exact hu' (by rw [h0, hDdef]; exact Finset.mem_union_right _ (Finset.mem_singleton_self 0))
    · intro x hx y hy hxy
      refine hu' ?_
      rw [hDdef]
      refine Finset.mem_union_left _ ?_
      exact Finset.mem_image.2 ⟨(x, y), Finset.mem_product.2 ⟨hx, hy⟩, hxy⟩
  obtain ⟨hs0, hsX⟩ := hmem s hsD
  obtain ⟨ht0, htX⟩ := hmem t htD
  obtain ⟨f, hf, hfid⟩ := exists_isSimon_id_on hs0 X hsX
  obtain ⟨g, hg, hgid⟩ := exists_isSimon_id_on ht0 X htX
  -- both oracles agree with the identity on all queried points
  have key : ∀ (h : BV n → BV n), (∀ x ∈ X, h x = x) → result A h q = result A id q := by
    intro h hid
    have : trace A h q = trace A id q := by
      refine trace_congr A id h q ?_
      intro j hj
      have hmemj : query A id j ∈ X := by
        rw [hXdef]
        exact Finset.mem_image.2 ⟨j, Finset.mem_range.2 hj, rfl⟩
      simpa using hid _ hmemj
    simp [result, this]
  have hfr : result A f q = result A id q := key f hfid
  have hgr : result A g q = result A id q := key g hgid
  by_cases hres : result A id q = s
  · exact ⟨g, t, hg, by rw [hgr, hres]; exact hst⟩
  · exact ⟨f, s, hf, by rw [hfr]; exact hres⟩

/-- **`Ω(2 ^ (n / 2))` classical queries are necessary.**  A deterministic
algorithm that always outputs the hidden shift after `q` queries must satisfy
`2 ^ n ≤ (q + 2) ^ 2`. -/
