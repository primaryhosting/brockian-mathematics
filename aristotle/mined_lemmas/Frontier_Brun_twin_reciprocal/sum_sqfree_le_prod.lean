import RequestProject.Mertens

/-!
# The main term: `∏_{3 ≤ p ≤ z} (1 - 2/p) ≤ 16 / (log z)^2`

This is proved by the elementary Euler-type argument: expanding `∏ (1 + 1/(p-1))` over
subsets dominates `∑_{a ≤ z squarefree} 1/a`, which in turn is at least half the harmonic
sum, hence at least `(log z)/2`.
-/

namespace Brun

open Finset


lemma sum_sqfree_le_prod (z : ℕ) :
    ∑ a ∈ sqfreeLE z, (1 / (a : ℝ)) ≤ ∏ p ∈ primesLE z, (1 + 1 / ((p : ℝ) - 1)) := by
  classical
  have hexp : ∏ p ∈ primesLE z, (1 / ((p : ℝ) - 1) + 1)
      = ∑ s ∈ (primesLE z).powerset, ∏ p ∈ s, (1 / ((p : ℝ) - 1)) := by
    rw [Finset.prod_add]
    exact Finset.sum_congr rfl (fun s _ => by simp)
  have hstep : ∑ s ∈ (primesLE z).powerset, (1 / ((∏ p ∈ s, p : ℕ) : ℝ))
      ≤ ∑ s ∈ (primesLE z).powerset, ∏ p ∈ s, (1 / ((p : ℝ) - 1)) := by
    refine Finset.sum_le_sum (fun s hs => ?_)
    rw [Finset.mem_powerset] at hs
    have hprod : ((∏ p ∈ s, p : ℕ) : ℝ) = ∏ p ∈ s, (p : ℝ) := by push_cast; ring
    rw [hprod, ← Finset.prod_inv_distrib]
    refine Finset.prod_le_prod (fun p _ => by positivity) (fun p hp => ?_)
    have hp2 : 2 ≤ p := (mem_primesLE.mp (hs hp)).2.two_le
    have hp2' : (2:ℝ) ≤ p := by exact_mod_cast hp2
    rw [one_div]
    apply inv_le_inv_of_le <;> linarith
  have hinj : Set.InjOn (fun s => ∏ p ∈ s, p) ((primesLE z).powerset : Set (Finset ℕ)) := by
    intro s hs t ht hst
    have hs' : ∀ p ∈ s, p.Prime := by
      intro p hp
      exact (mem_primesLE.mp ((Finset.mem_powerset.mp hs) hp)).2
    have ht' : ∀ p ∈ t, p.Prime := by
      intro p hp
      exact (mem_primesLE.mp ((Finset.mem_powerset.mp ht) hp)).2
    have := congrArg Nat.primeFactors hst
    rwa [Nat.primeFactors_prod hs', Nat.primeFactors_prod ht'] at this
  have himg : sqfreeLE z ⊆ ((primesLE z).powerset).image (fun s => ∏ p ∈ s, p) := by
    intro a ha
    simp only [sqfreeLE, Finset.mem_filter, Finset.mem_Icc] at ha
    obtain ⟨⟨ha1, haz⟩, hsq⟩ := ha
    refine Finset.mem_image.mpr ⟨a.primeFactors, ?_, Nat.prod_primeFactors_of_squarefree hsq⟩
    rw [Finset.mem_powerset]
    intro p hp
    rw [Nat.mem_primeFactors] at hp
    exact mem_primesLE.mpr ⟨le_trans (Nat.le_of_dvd (by omega) hp.2.1) haz, hp.1⟩
  calc ∑ a ∈ sqfreeLE z, (1 / (a : ℝ))
      ≤ ∑ a ∈ ((primesLE z).powerset).image (fun s => ∏ p ∈ s, p), (1 / (a : ℝ)) := by
        refine Finset.sum_le_sum_of_subset_of_nonneg himg ?_
        intro i _ _; positivity
  _ = ∑ s ∈ (primesLE z).powerset, (1 / ((∏ p ∈ s, p : ℕ) : ℝ)) := Finset.sum_image hinj
  _ ≤ ∏ p ∈ primesLE z, (1 / ((p : ℝ) - 1) + 1) := by rw [hexp]; exact hstep
  _ = ∏ p ∈ primesLE z, (1 + 1 / ((p : ℝ) - 1)) := by
        exact Finset.prod_congr rfl (fun p _ => by ring)

