import Mathlib
open Matrix Finset
namespace MS.Brockian
/-- Universal q−2 admissibility law (heart of the Brockian sieve). -/

theorem universal_admissibility_count (q : ℕ) [NeZero q] (g : ZMod q) (hg : g ≠ 0) :
    (admissibleResidues q g).card = q - 2 := by
  classical
  have hne : (0 : ZMod q) ≠ -g := by
    simpa [eq_comm, neg_eq_zero] using hg
  have hset : admissibleResidues q g = (Finset.univ : Finset (ZMod q)) \ {0, -g} := by
    ext r
    simp [admissibleResidues, Finset.mem_sdiff, not_or]
  have hcard : ({0, -g} : Finset (ZMod q)).card = 2 := by
    rw [Finset.card_insert_of_notMem (by simpa using hne), Finset.card_singleton]
  rw [hset, Finset.card_sdiff, Finset.inter_univ, hcard, Finset.card_univ, ZMod.card]
set_option maxHeartbeats 2000000 in
set_option maxRecDepth 4000 in
/-- Pentagon golden eigenvalue: 2cos(2π/5) = (√5−1)/2 solves the C₅ adjacency spectrum. -/
