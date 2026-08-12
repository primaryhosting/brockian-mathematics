/-
`m` independent runs of Simon's algorithm, and the analysis showing that `n + 2` quantum
queries determine the hidden shift with probability at least `3/4`.
-/
import RequestProject.SimonQuantum

open scoped BigOperators
open scoped Classical
open Finset

set_option maxHeartbeats 1000000
set_option autoImplicit false

namespace QI

/-- The state of `m` independent copies of the Simon circuit (a product state, using
`m` quantum queries in total). -/
noncomputable def tupleState {n : ℕ} (m : ℕ) (f : Bits n → Bits n) :
    (Fin m → Bits n × Bits n) → ℂ := fun v => ∏ i, simonState f (v i)

/-- Probability of observing the tuple `y` of outcomes when measuring the first register of
each of the `m` copies. -/
noncomputable def measureTuple {n : ℕ} (m : ℕ) (f : Bits n → Bits n) (y : Fin m → Bits n) : ℝ :=
  ∑ z : Fin m → Bits n, Complex.normSq (tupleState m f (fun i => (y i, z i)))

lemma measureTuple_eq_prod {n : ℕ} (m : ℕ) (f : Bits n → Bits n) (y : Fin m → Bits n) :
    measureTuple m f y = ∏ i, measureFst (simonState f) (y i) := by
  classical
  have h : ∀ z : Fin m → Bits n,
      Complex.normSq (tupleState m f (fun i => (y i, z i)))
        = ∏ i, Complex.normSq (simonState f (y i, z i)) := by
    intro z
    rw [tupleState]
    exact map_prod Complex.normSq _ _
  rw [measureTuple, Finset.sum_congr rfl (fun z _ => h z)]
  simp only [measureFst]
  rw [Finset.prod_univ_sum]
  rw [Fintype.piFinset_univ]

/-- The measurement outcome distribution of one run is a genuine probability distribution:
the probabilities sum to `1`. -/
theorem measureFst_total {n : ℕ} (f : Bits n → Bits n) (s : Bits n) (hf : SimonPromise f s) :
    ∑ y : Bits n, measureFst (simonState f) y = 1 := by
  classical
  have hs : s ≠ 0 := hf.1
  rw [Finset.sum_congr rfl (fun y _ => measureFst_simonState f s hf y)]
  rw [Finset.sum_ite, Finset.sum_const, Finset.sum_const_zero, add_zero, nsmul_eq_mul]
  have hfil : (Finset.univ.filter (fun y : Bits n => bdot y s = 0)) = orth s := rfl
  rw [hfil]
  have hK2 : 2 * (orth s).card = 2 ^ n := card_orth s hs
  have hKR : ((orth s).card : ℝ) * 2 = 2 ^ n := by exact_mod_cast (by omega : (orth s).card * 2 = 2 ^ n)
  have h2n : (0:ℝ) < 2 ^ n := by positivity
  field_simp
  linarith [hKR]

/-- The outcome tuple `y` pins down the hidden shift `s`: every `y i` is orthogonal to `s`,
and `s` is the only nonzero string with this property. -/
def determines {n m : ℕ} (y : Fin m → Bits n) (s : Bits n) : Prop :=
  (∀ i, bdot (y i) s = 0) ∧ ∀ t : Bits n, t ≠ 0 → (∀ i, bdot (y i) t = 0) → t = s

/-- The set of successful outcome tuples. -/
noncomputable def goodSet (n m : ℕ) (s : Bits n) : Finset (Fin m → Bits n) :=
  Finset.univ.filter (fun y => determines y s)

/-- The probability that `m` runs of Simon's algorithm determine the hidden shift. -/
noncomputable def successProb {n : ℕ} (m : ℕ) (f : Bits n → Bits n) (s : Bits n) : ℝ :=
  ∑ y ∈ goodSet n m s, measureTuple m f y

/-- Counting bound: at least three quarters of the tuples of vectors orthogonal to `s`
determine `s`, once `m = n + 2`. -/
lemma card_goodSet_lower {n : ℕ} (s : Bits n) (hs : s ≠ 0) (m : ℕ) (hm : m = n + 2) :
    3 * (orth s).card ^ m ≤ 4 * (goodSet n m s).card := by
  classical
  set S : Finset (Bits n) := orth s with hS
  set P : Finset (Fin m → Bits n) := Fintype.piFinset (fun _ : Fin m => S) with hP
  have hPcard : P.card = S.card ^ m := by
    rw [hP, Fintype.card_piFinset]
    simp
  have hsub : goodSet n m s ⊆ P := by
    intro y hy
    rw [goodSet, Finset.mem_filter] at hy
    rw [hP, Fintype.mem_piFinset]
    intro i
    rw [hS, mem_orth]
    exact hy.2.1 i
  set T : Finset (Bits n) := Finset.univ.filter (fun t => t ≠ 0 ∧ t ≠ s) with hT
  set Bad : Finset (Fin m → Bits n) := P \ goodSet n m s with hBad
  have hBadsub : Bad ⊆ T.biUnion
      (fun t => Fintype.piFinset (fun _ : Fin m => S.filter (fun y => bdot y t = 0))) := by
    intro y hy
    rw [hBad, Finset.mem_sdiff] at hy
    obtain ⟨hyP, hyG⟩ := hy
    rw [hP, Fintype.mem_piFinset] at hyP
    have hys : ∀ i, bdot (y i) s = 0 := by
      intro i
      have := hyP i
      rwa [hS, mem_orth] at this
    have : ¬ determines y s := by
      intro hd
      exact hyG (by rw [goodSet, Finset.mem_filter]; exact ⟨Finset.mem_univ _, hd⟩)
    rw [determines] at this
    push_neg at this
    obtain ⟨t, ht0, htorth, hts⟩ := this hys
    refine Finset.mem_biUnion.2 ⟨t, ?_, ?_⟩
    · rw [hT, Finset.mem_filter]
      exact ⟨Finset.mem_univ _, ht0, hts⟩
    · rw [Fintype.mem_piFinset]
      intro i
      rw [Finset.mem_filter, hS, mem_orth]
      exact ⟨hys i, htorth i⟩
  have hkey : ∀ t ∈ T, 2 ^ m * (S.filter (fun y => bdot y t = 0)).card ^ m = S.card ^ m := by
    intro t ht
    rw [hT, Finset.mem_filter] at ht
    have h2 := card_orth_inter s t hs ht.2.1 ht.2.2
    rw [← hS] at h2
    calc 2 ^ m * (S.filter (fun y => bdot y t = 0)).card ^ m
        = (2 * (S.filter (fun y => bdot y t = 0)).card) ^ m := by rw [mul_pow]
      _ = S.card ^ m := by rw [h2]
  have hTcard : T.card ≤ 2 ^ n := by
    calc T.card ≤ (Finset.univ : Finset (Bits n)).card := Finset.card_le_card (Finset.subset_univ _)
      _ = 2 ^ n := by simp
  have hBadbound : 2 ^ m * Bad.card ≤ 2 ^ n * S.card ^ m := by
    have h1 : Bad.card ≤ ∑ t ∈ T,
        (Fintype.piFinset (fun _ : Fin m => S.filter (fun y => bdot y t = 0))).card :=
      le_trans (Finset.card_le_card hBadsub) Finset.card_biUnion_le
    have h2 : 2 ^ m * Bad.card ≤ ∑ t ∈ T, 2 ^ m *
        (Fintype.piFinset (fun _ : Fin m => S.filter (fun y => bdot y t = 0))).card := by
      rw [← Finset.mul_sum]
      exact Nat.mul_le_mul_left _ h1
    have h3 : ∑ t ∈ T, 2 ^ m *
        (Fintype.piFinset (fun _ : Fin m => S.filter (fun y => bdot y t = 0))).card
        = ∑ t ∈ T, S.card ^ m := by
      refine Finset.sum_congr rfl ?_
      intro t ht
      rw [Fintype.card_piFinset]
      simp only [Finset.prod_const, Finset.card_univ, Fintype.card_fin]
      exact hkey t ht
    rw [h3, Finset.sum_const, smul_eq_mul] at h2
    exact le_trans h2 (Nat.mul_le_mul_right _ hTcard)
  have hpow : (2:ℕ) ^ m = 4 * 2 ^ n := by
    rw [hm]; ring
  have h4 : 4 * Bad.card ≤ S.card ^ m := by
    have := hBadbound
    rw [hpow] at this
    have hpos : 0 < (2:ℕ) ^ n := Nat.pow_pos (by norm_num)
    nlinarith [this, hpos]
  have hsplit : (goodSet n m s).card + Bad.card = S.card ^ m := by
    rw [hBad, Finset.card_sdiff_of_subset hsub, ← hPcard]
    have := Finset.card_le_card hsub
    omega
  omega

/-- **`n + 2` quantum queries suffice.**  With `n + 2` runs of the one-query Simon circuit,
the measurement outcomes determine the hidden shift with probability at least `3/4`. -/
theorem successProb_lower {n : ℕ} (f : Bits n → Bits n) (s : Bits n) (hf : SimonPromise f s) :
    (3 : ℝ) / 4 ≤ successProb (n + 2) f s := by
  classical
  have hs : s ≠ 0 := hf.1
  set m := n + 2 with hm
  set K : ℕ := (orth s).card with hK
  have hK2 : 2 * K = 2 ^ n := card_orth s hs
  have hKpos : 0 < K := by
    have : 0 < 2 ^ n := Nat.pow_pos (by norm_num)
    omega
  have hval : ∀ y ∈ goodSet n m s, measureTuple m f y = ((K : ℝ))⁻¹ ^ m := by
    intro y hy
    rw [goodSet, Finset.mem_filter] at hy
    rw [measureTuple_eq_prod]
    have : ∀ i : Fin m, measureFst (simonState f) (y i) = ((K : ℝ))⁻¹ := by
      intro i
      rw [measureFst_simonState f s hf, if_pos (hy.2.1 i)]
      have hKne : ((K : ℝ)) ≠ 0 := by
        have : (0:ℝ) < (K:ℝ) := by exact_mod_cast hKpos
        exact this.ne'
      have h2n : ((2:ℝ)) ^ n = 2 * (K : ℝ) := by exact_mod_cast hK2.symm
      rw [h2n]
      field_simp
    rw [Finset.prod_congr rfl (fun i _ => this i)]
    simp
  rw [successProb, Finset.sum_congr rfl hval, Finset.sum_const, nsmul_eq_mul]
  have hcount := card_goodSet_lower s hs m rfl
  rw [← hK] at hcount
  have hKR : (0:ℝ) < (K : ℝ) := by exact_mod_cast hKpos
  have hcountR : 3 * (K : ℝ) ^ m ≤ 4 * ((goodSet n m s).card : ℝ) := by
    exact_mod_cast hcount
  have hKm : (0:ℝ) < (K:ℝ) ^ m := by positivity
  rw [inv_pow, ← div_eq_mul_inv, le_div_iff₀ hKm]
  linarith [hcountR]

end QI

/-
The classical query lower bound for Simon's problem: any deterministic classical algorithm
solving Simon's problem needs `Ω(2^(n/2))` queries.
-/
import RequestProject.SimonQuantum

open scoped BigOperators
open scoped Classical
open Finset

set_option maxHeartbeats 1000000
set_option autoImplicit false

namespace QI

/-- A deterministic adaptive classical query algorithm: `query` chooses the next query point
from the list of answers received so far, and `out` produces the answer. -/
structure ClassicalAlg (n : ℕ) where
  /-- Choice of the next query, given the answers so far. -/
  query : List (Bits n) → Bits n
  /-- Final output, given the list of answers. -/
  out : List (Bits n) → Bits n

/-- The list of answers received after `k` queries to `f`. -/
def transcript {n : ℕ} (A : ClassicalAlg n) (f : Bits n → Bits n) : ℕ → List (Bits n)
  | 0 => []
  | (k + 1) => transcript A f k ++ [f (A.query (transcript A f k))]

/-- The output of the algorithm after `q` queries to `f`. -/
def output {n : ℕ} (A : ClassicalAlg n) (q : ℕ) (f : Bits n → Bits n) : Bits n :=
  A.out (transcript A f q)

/-- The algorithm solves Simon's problem with `q` queries. -/
def Solves {n : ℕ} (A : ClassicalAlg n) (q : ℕ) : Prop :=
  ∀ (f : Bits n → Bits n) (s : Bits n), SimonPromise f s → output A q f = s

/-- The `k`-th query point of the algorithm when all queries are answered by the identity. -/
def qpt {n : ℕ} (A : ClassicalAlg n) (k : ℕ) : Bits n :=
  A.query (transcript A (fun x => x) k)

/-- The set of points queried in the first `q` rounds against the identity answers. -/
noncomputable def queried {n : ℕ} (A : ClassicalAlg n) (q : ℕ) : Finset (Bits n) :=
  (Finset.range q).image (qpt A)

lemma card_queried_le {n : ℕ} (A : ClassicalAlg n) (q : ℕ) : (queried A q).card ≤ q := by
  classical
  calc (queried A q).card ≤ (Finset.range q).card := Finset.card_image_le
    _ = q := Finset.card_range q

/-- If `g` fixes every point queried against the identity, the algorithm cannot tell `g`
from the identity. -/
lemma transcript_stable {n : ℕ} (A : ClassicalAlg n) (q : ℕ) (g : Bits n → Bits n)
    (hg : ∀ x ∈ queried A q, g x = x) :
    ∀ k, k ≤ q → transcript A g k = transcript A (fun x => x) k := by
  intro k
  induction k with
  | zero => intro _; rfl
  | succ k ih =>
    intro hk
    have hk' : k ≤ q := Nat.le_of_succ_le hk
    have hT := ih hk'
    have hmem : qpt A k ∈ queried A q := by
      rw [queried]
      exact Finset.mem_image.2 ⟨k, Finset.mem_range.2 (Nat.lt_of_succ_le hk), rfl⟩
    rw [transcript, transcript, hT, ← qpt, hg _ hmem]

section Construction

variable {n : ℕ}

/-- The canonical representative of the pair `{x, x + s}`, where `s j = 1`. -/
def rep (s : Bits n) (j : Fin n) (x : Bits n) : Bits n := if x j = 0 then x else x + s

lemma rep_eq_iff (s : Bits n) (j : Fin n) (hj : s j = 1) (x y : Bits n) :
    rep s j x = rep s j y ↔ (y = x ∨ y = x + s) := by
  have hadd : ∀ w : Bits n, (w + s) j = w j + 1 := by
    intro w; simp [hj]
  have hcancel : ∀ a b : Bits n, a + s = b + s ↔ a = b := by
    intro a b
    constructor
    · intro h
      have := congrArg (fun w => w + s) h
      simpa [add_assoc, bits_add_self] using this
    · intro h; rw [h]
  have hshift : ∀ a b : Bits n, a = b + s ↔ b = a + s := by
    intro a b
    constructor <;> intro h <;> rw [h] <;> simp [add_assoc, bits_add_self]
  rcases zmod_two_cases (x j) with hx | hx <;> rcases zmod_two_cases (y j) with hy | hy
  · rw [rep, rep, if_pos hx, if_pos hy]
    constructor
    · intro h; exact Or.inl h.symm
    · rintro (h | h)
      · exact h.symm
      · exfalso
        rw [h, hadd, hx] at hy
        exact absurd hy (by decide)
  · rw [rep, rep, if_pos hx, if_neg (by rw [hy]; decide)]
    constructor
    · intro h
      exact Or.inr ((hshift x y).1 h)
    · rintro (h | h)
      · exfalso
        rw [h, hx] at hy
        exact absurd hy (by decide)
      · rw [h]
        rw [add_assoc, bits_add_self, add_zero]
  · rw [rep, rep, if_neg (by rw [hx]; decide), if_pos hy]
    constructor
    · intro h
      exact Or.inr h.symm
    · rintro (h | h)
      · exfalso
        rw [h, hx] at hy
        exact absurd hy (by decide)
      · exact h.symm
  · rw [rep, rep, if_neg (by rw [hx]; decide), if_neg (by rw [hy]; decide), hcancel]
    constructor
    · intro h; exact Or.inl h.symm
    · rintro (h | h)
      · exact h.symm
      · exfalso
        rw [h, hadd, hx] at hy
        exact absurd hy (by decide)

/-- A Simon function with hidden shift `s` fixing all the queried points. -/
lemma exists_simon_fun_fixing (s : Bits n) (hs : s ≠ 0) (Q : Finset (Bits n))
    (hQ : ∀ x ∈ Q, ∀ y ∈ Q, x + y ≠ s) :
    ∃ g : Bits n → Bits n, SimonPromise g s ∧ ∀ x ∈ Q, g x = x := by
  classical
  obtain ⟨j, hj0⟩ : ∃ j, s j ≠ 0 := by
    by_contra h
    push_neg at h
    exact hs (funext h)
  have hj : s j = 1 := by
    rcases zmod_two_cases (s j) with h | h
    · exact absurd h hj0
    · exact h
  set r : Bits n → Bits n := rep s j with hr
  have hrinj : ∀ x ∈ Q, ∀ y ∈ Q, r x = r y → x = y := by
    intro x hx y hy hxy
    rcases (rep_eq_iff s j hj x y).1 hxy with h | h
    · exact h.symm
    · exfalso
      apply hQ x hx y hy
      rw [h, ← add_assoc, bits_add_self, zero_add]
  set R : Finset (Bits n) := Q.image r with hR
  have hphi : Function.Bijective (fun x : {x // x ∈ Q} => (⟨r x.1, by
      rw [hR]; exact Finset.mem_image_of_mem r x.2⟩ : {z // z ∈ R})) := by
    constructor
    · intro a b hab
      have : r a.1 = r b.1 := congrArg Subtype.val hab
      exact Subtype.ext (hrinj a.1 a.2 b.1 b.2 this)
    · rintro ⟨z, hz⟩
      rw [hR, Finset.mem_image] at hz
      obtain ⟨x, hx, hxz⟩ := hz
      exact ⟨⟨x, hx⟩, Subtype.ext hxz⟩
  set e : {z // z ∈ R} ≃ {x // x ∈ Q} := (Equiv.ofBijective _ hphi).symm with he
  set sigma : Equiv.Perm (Bits n) := Equiv.extendSubtype e with hsigma
  refine ⟨fun x => sigma (r x), ⟨hs, ?_⟩, ?_⟩
  · intro x y
    show sigma (r x) = sigma (r y) ↔ (y = x ∨ y = x + s)
    constructor
    · intro h
      have : r x = r y := sigma.injective h
      exact (rep_eq_iff s j hj x y).1 this
    · intro h
      have hrr : r x = r y := (rep_eq_iff s j hj x y).2 h
      rw [hrr]
  · intro x hx
    show sigma (r x) = x
    have hmem : r x ∈ R := by rw [hR]; exact Finset.mem_image_of_mem r hx
    have h1 : sigma (r x) = (e ⟨r x, hmem⟩ : Bits n) := Equiv.extendSubtype_apply_of_mem e _ hmem
    rw [h1, he]
    have : (Equiv.ofBijective _ hphi) ⟨x, hx⟩ = ⟨r x, hmem⟩ := rfl
    rw [← this, Equiv.symm_apply_apply]

end Construction

/-- **Classical lower bound.**  Any deterministic classical algorithm that solves Simon's
problem on `n` bits with `q` queries satisfies `2^n ≤ q^2 + 2`. -/
theorem classical_query_bound {n : ℕ} (A : ClassicalAlg n) (q : ℕ) (hA : Solves A q) :
    2 ^ n ≤ q * q + 2 := by
  classical
  by_contra hcon
  push_neg at hcon
  set Q : Finset (Bits n) := queried A q with hQ
  set t : Bits n := A.out (transcript A (fun x => x) q) with ht
  set F : Finset (Bits n) :=
    insert 0 (insert t ((Q ×ˢ Q).image (fun p => p.1 + p.2))) with hF
  have hFcard : F.card < 2 ^ n := by
    have h1 : ((Q ×ˢ Q).image (fun p : Bits n × Bits n => p.1 + p.2)).card ≤ q * q := by
      calc ((Q ×ˢ Q).image (fun p : Bits n × Bits n => p.1 + p.2)).card
          ≤ (Q ×ˢ Q).card := Finset.card_image_le
        _ = Q.card * Q.card := Finset.card_product _ _
        _ ≤ q * q := Nat.mul_le_mul (card_queried_le A q) (card_queried_le A q)
    have h2 : F.card ≤ q * q + 2 := by
      rw [hF]
      calc (insert 0 (insert t ((Q ×ˢ Q).image (fun p : Bits n × Bits n => p.1 + p.2)))).card
          ≤ (insert t ((Q ×ˢ Q).image (fun p : Bits n × Bits n => p.1 + p.2))).card + 1 :=
            Finset.card_insert_le _ _
        _ ≤ (((Q ×ˢ Q).image (fun p : Bits n × Bits n => p.1 + p.2)).card + 1) + 1 :=
            Nat.add_le_add_right (Finset.card_insert_le _ _) 1
        _ ≤ q * q + 2 := by omega
    omega
  have hexists : ∃ s : Bits n, s ∉ F := by
    by_contra h
    push_neg at h
    have : (Finset.univ : Finset (Bits n)) ⊆ F := fun x _ => h x
    have hcard : (Finset.univ : Finset (Bits n)).card ≤ F.card := Finset.card_le_card this
    simp only [Finset.card_univ] at hcard
    have : Fintype.card (Bits n) = 2 ^ n := by simp
    omega
  obtain ⟨s, hsF⟩ := hexists
  rw [hF] at hsF
  simp only [Finset.mem_insert, Finset.mem_image, Finset.mem_product, not_or] at hsF
  obtain ⟨hs0, hst, hsQ⟩ := hsF
  push_neg at hsQ
  have hQdiff : ∀ x ∈ Q, ∀ y ∈ Q, x + y ≠ s := by
    intro x hx y hy hxy
    exact hsQ (x, y) ⟨hx, hy⟩ hxy
  obtain ⟨g, hgpromise, hgfix⟩ := exists_simon_fun_fixing s hs0 Q hQdiff
  have hstab := transcript_stable A q g (by rw [← hQ]; exact hgfix) q le_rfl
  have hout : output A q g = t := by
    rw [output, hstab, ht]
  have := hA g s hgpromise
  rw [hout] at this
  exact hst this.symm

/-- **Simon's problem needs `Ω(2^(n/2))` classical queries.** -/
theorem classical_query_lower_bound {n : ℕ} (A : ClassicalAlg n) (q : ℕ) (hn : 2 ≤ n)
    (hA : Solves A q) : 2 ^ ((n - 1) / 2) ≤ q := by
  have h1 : 2 ^ n ≤ q * q + 2 := classical_query_bound A q hA
  have h2 : 2 ^ (n - 1) ≤ q * q := by
    have hsplit : (2:ℕ) ^ n = 2 * 2 ^ (n - 1) := by
      rw [← pow_succ']
      congr 1
      omega
    have h3 : (2:ℕ) ^ 1 ≤ 2 ^ (n - 1) := Nat.pow_le_pow_right (by norm_num) (by omega)
    omega
  have h4 : 2 ^ ((n - 1) / 2) * 2 ^ ((n - 1) / 2) ≤ q * q := by
    calc 2 ^ ((n - 1) / 2) * 2 ^ ((n - 1) / 2) = 2 ^ (2 * ((n - 1) / 2)) := by
          rw [two_mul, pow_add]
      _ ≤ 2 ^ (n - 1) := Nat.pow_le_pow_right (by norm_num) (by omega)
      _ ≤ q * q := h2
  exact Nat.mul_self_le_mul_self_iff.1 h4

end QI

/-
Basic combinatorial / linear-algebraic facts about the `F_2`-vector space of bit strings,
used in the formalization of Simon's problem.
-/
import Mathlib

open scoped BigOperators
open scoped Classical
open Finset

set_option maxHeartbeats 1000000
set_option autoImplicit false

namespace QI

/-- The space of `n`-bit strings, an `F₂`-vector space. -/
abbrev Bits (n : ℕ) : Type := Fin n → ZMod 2

/-- The standard `F₂`-valued inner product on bit strings. -/
def bdot {n : ℕ} (x y : Bits n) : ZMod 2 := ∑ i, x i * y i

lemma zmod_two_cases (a : ZMod 2) : a = 0 ∨ a = 1 := by
  revert a; decide

lemma zmod_two_add_self (a : ZMod 2) : a + a = 0 := by
  revert a; decide

lemma zmod_two_eq_of_add_eq_zero {a b : ZMod 2} (h : a + b = 0) : a = b := by
  revert h; revert a; revert b; decide

lemma bits_add_self {n : ℕ} (x : Bits n) : x + x = 0 := by
  funext i; exact zmod_two_add_self _

@[simp] lemma bdot_zero_left {n : ℕ} (y : Bits n) : bdot (0 : Bits n) y = 0 := by
  simp [bdot]

@[simp] lemma bdot_zero_right {n : ℕ} (x : Bits n) : bdot x (0 : Bits n) = 0 := by
  simp [bdot]

lemma bdot_comm {n : ℕ} (x y : Bits n) : bdot x y = bdot y x := by
  simp [bdot, mul_comm]

lemma bdot_add_left {n : ℕ} (x y z : Bits n) : bdot (x + y) z = bdot x z + bdot y z := by
  simp [bdot, add_mul, Finset.sum_add_distrib]

lemma bdot_add_right {n : ℕ} (x y z : Bits n) : bdot x (y + z) = bdot x y + bdot x z := by
  simp [bdot, mul_add, Finset.sum_add_distrib]

lemma bdot_smul_right {n : ℕ} (a : ZMod 2) (x y : Bits n) :
    bdot x (a • y) = a * bdot x y := by
  simp only [bdot, Finset.mul_sum, Pi.smul_apply, smul_eq_mul]
  exact Finset.sum_congr rfl (fun i _ => by ring)

lemma bdot_smul_left {n : ℕ} (a : ZMod 2) (x y : Bits n) :
    bdot (a • x) y = a * bdot x y := by
  rw [bdot_comm, bdot_smul_right, bdot_comm]

/-- Evaluating the pairing against a standard basis vector. -/
lemma bdot_single {n : ℕ} (x : Bits n) (i : Fin n) :
    bdot x (Pi.single i 1) = x i := by
  classical
  rw [bdot, Finset.sum_eq_single i]
  · simp
  · intro j _ hj
    simp [Pi.single_eq_of_ne hj]
  · intro h; exact absurd (Finset.mem_univ i) h

/-- The pairing is nondegenerate. -/
lemma bdot_eq_zero_iff {n : ℕ} (x : Bits n) : (∀ y, bdot x y = 0) ↔ x = 0 := by
  constructor
  · intro h
    funext i
    have := h (Pi.single i 1)
    rwa [bdot_single] at this
  · rintro rfl y; simp

/-- Given a nonzero `s`, and `t` outside `{0, s}`, there is a vector orthogonal to `s`
but not to `t`. -/
lemma exists_orth_nonorth {n : ℕ} (s t : Bits n) (hs : s ≠ 0) (ht0 : t ≠ 0) (hts : t ≠ s) :
    ∃ y : Bits n, bdot y s = 0 ∧ bdot y t = 1 := by
  by_contra hcon
  push_neg at hcon
  have hcon' : ∀ y : Bits n, bdot y s = 0 → bdot y t = 0 := by
    intro y hy
    rcases zmod_two_cases (bdot y t) with h | h
    · exact h
    · exact absurd h (hcon y hy)
  obtain ⟨i, hi⟩ : ∃ i, s i ≠ 0 := by
    by_contra h
    push_neg at h
    exact hs (funext h)
  set e : Bits n := Pi.single i 1 with he
  have hes : bdot e s = 1 := by
    rw [bdot_comm, bdot_single]
    rcases zmod_two_cases (s i) with h | h
    · exact absurd h hi
    · exact h
  set a : ZMod 2 := bdot e t with ha
  have key : ∀ u : Bits n, bdot (t + a • s) u = 0 := by
    intro u
    have h1 : bdot (u + (bdot u s) • e) s = 0 := by
      rw [bdot_add_left, bdot_smul_left, hes, mul_one, zmod_two_add_self]
    have h2 := hcon' _ h1
    rw [bdot_add_left, bdot_smul_left, ← ha] at h2
    have h3 : bdot u t = bdot u s * a := zmod_two_eq_of_add_eq_zero h2
    rw [bdot_add_left, bdot_smul_left, bdot_comm t u, bdot_comm s u, h3, mul_comm,
      zmod_two_add_self]
  have : t + a • s = 0 := (bdot_eq_zero_iff _).1 key
  rcases zmod_two_cases a with h | h
  · rw [h] at this; simp at this; exact ht0 this
  · rw [h, one_smul] at this
    have hts' : t = s := by
      have h4 := congrArg (fun z => z + s) this
      simp only [add_assoc, bits_add_self, add_zero, zero_add] at h4
      exact h4
    exact hts hts'

/-- Translation by `y₀` splits a translation-invariant set in half according to the value of
the pairing with `t`, provided `⟨y₀, t⟩ = 1`. -/
lemma card_split {n : ℕ} (S : Finset (Bits n)) (t y0 : Bits n)
    (hS : ∀ y : Bits n, y ∈ S ↔ y + y0 ∈ S) (h0 : bdot y0 t = 1) :
    2 * (S.filter (fun y => bdot y t = 0)).card = S.card := by
  classical
  have hpart : (S.filter (fun y => bdot y t = 0)).card
      + (S.filter (fun y => ¬ bdot y t = 0)).card = S.card :=
    Finset.card_filter_add_card_filter_not _
  have hcard : (S.filter (fun y => ¬ bdot y t = 0)).card
      = (S.filter (fun y => bdot y t = 0)).card := by
    refine Finset.card_bij' (fun y _ => y + y0) (fun y _ => y + y0) ?_ ?_ ?_ ?_
    · intro y hy
      simp only [Finset.mem_filter] at hy ⊢
      refine ⟨(hS y).1 hy.1, ?_⟩
      rw [bdot_add_left, h0]
      rcases zmod_two_cases (bdot y t) with h | h
      · exact absurd h hy.2
      · rw [h]; decide
    · intro y hy
      simp only [Finset.mem_filter] at hy ⊢
      refine ⟨(hS y).1 hy.1, ?_⟩
      rw [bdot_add_left, h0, hy.2]
      decide
    · intro y _
      simp only [add_assoc, bits_add_self, add_zero]
    · intro y _
      simp only [add_assoc, bits_add_self, add_zero]
  omega

/-- The set of bit strings orthogonal to `s`. -/
def orth {n : ℕ} (s : Bits n) : Finset (Bits n) := Finset.univ.filter (fun y => bdot y s = 0)

@[simp] lemma mem_orth {n : ℕ} (s y : Bits n) : y ∈ orth s ↔ bdot y s = 0 := by
  simp [orth]

/-- For `s ≠ 0`, the orthogonal complement of `s` has `2^(n-1)` elements. -/
lemma card_orth {n : ℕ} (s : Bits n) (hs : s ≠ 0) : 2 * (orth s).card = 2 ^ n := by
  classical
  obtain ⟨i, hi⟩ : ∃ i, s i ≠ 0 := by
    by_contra h
    push_neg at h
    exact hs (funext h)
  have h0 : bdot (Pi.single i (1 : ZMod 2)) s = 1 := by
    rw [bdot_comm, bdot_single]
    rcases zmod_two_cases (s i) with h | h
    · exact absurd h hi
    · exact h
  have := card_split (Finset.univ : Finset (Bits n)) s (Pi.single i (1 : ZMod 2))
    (by intro y; simp) h0
  rw [orth]
  rw [this]
  simp [Finset.card_univ]

/-- For independent `s, t` the pairing with `t` halves the orthogonal complement of `s`. -/
lemma card_orth_inter {n : ℕ} (s t : Bits n) (hs : s ≠ 0) (ht0 : t ≠ 0) (hts : t ≠ s) :
    2 * ((orth s).filter (fun y => bdot y t = 0)).card = (orth s).card := by
  obtain ⟨y0, hy0s, hy0t⟩ := exists_orth_nonorth s t hs ht0 hts
  refine card_split _ t y0 ?_ hy0t
  intro y
  simp only [mem_orth, bdot_add_left, hy0s, add_zero]

end QI

/-
# Simon Algorithm
Category: Frontier Qi
Target: QI.simon_algorithm
Statement: Simon's problem is solved with O(n) quantum queries but needs Ω(2^{n/2}) classically.
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/
-- (The header above is a plain block comment rather than a `/-! -/` module docstring because
-- Lean requires all `import` lines to come before any command; the identical text is repeated
-- as the module docstring immediately after the imports.)
import Mathlib
import RequestProject.SimonBasic
import RequestProject.SimonQuantum
import RequestProject.SimonMulti
import RequestProject.SimonClassical

/-!
# Simon Algorithm
Category: Frontier Qi
Target: QI.simon_algorithm
Statement: Simon's problem is solved with O(n) quantum queries but needs Ω(2^{n/2}) classically.
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
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
set_option pp.piBinderTypes true

set_option grind.warning false

namespace QI

/-- The number of quantum queries used by Simon's algorithm on `n` bits: one query per run
of the circuit `H^{⊗n} · O_f · H^{⊗n}`, repeated `n + 2` times. -/
def simonQuantumQueries (n : ℕ) : ℕ := n + 2

/-!
### Statement of the main theorem

The model, spelled out by the definitions in the imported files:

* `QI.Bits n = Fin n → ZMod 2` is the set of `n`-bit strings, an `F₂`-vector space, and
  `QI.bdot` is the `F₂`-valued inner product.
* `QI.SimonPromise f s` says that `s ≠ 0` and `f x = f y ↔ (y = x ∨ y = x + s)`, i.e. `f` is
  two-to-one with hidden shift `s`. Simon's problem is to find `s`.
* `QI.simonState f = hadFst (oracle f (hadFst (initState n)))` is the quantum state obtained
  from `|0, 0⟩` by a Hadamard transform on the first register, **one** standard quantum query
  `|x, z⟩ ↦ |x, z + f x⟩`, and a second Hadamard transform; `QI.measureFst` is the Born-rule
  probability of an outcome of measuring the first register.
* `QI.tupleState m f` is the product state of `m` independent copies of that circuit — a
  computation using exactly `m` quantum queries — and `QI.measureTuple m f` its outcome
  distribution; `QI.successProb m f s` is the probability that the outcome tuple `QI.determines`
  the hidden shift `s`, i.e. that `s` is the unique nonzero vector orthogonal to all `m`
  measured strings (and hence is recovered by classical linear algebra).
* `QI.ClassicalAlg n` is a deterministic adaptive classical query algorithm, `QI.Solves A q`
  says it outputs the hidden shift for every instance of Simon's problem using `q` queries.

The conjuncts below say:

1. the Hadamard layer and the quantum query are unitary (they preserve the total squared
   amplitude) and the initial state is normalized, so the circuit is a legitimate quantum
   computation;
2. the one-query circuit yields a genuine probability distribution;
3. it samples exactly uniformly from the hyperplane `s^⊥` orthogonal to the hidden shift;
4. `simonQuantumQueries n = n + 2` quantum queries — a number that is `O(n)`, with explicit
   constant `3` in the last line — determine `s` with probability at least `3/4`;
5. every deterministic classical algorithm solving Simon's problem needs `q ≥ 2^((n-1)/2)`
   queries, i.e. `Ω(2^(n/2))` many.
-/
/-- **Simon's problem is solved with `O(n)` quantum queries but needs `Ω(2^(n/2))`
classical queries.** -/
theorem simon_algorithm :
    (∀ (n : ℕ) (psi : Amp n), ∑ p : Bits n × Bits n, Complex.normSq (hadFst psi p)
        = ∑ p : Bits n × Bits n, Complex.normSq (psi p)) ∧
    (∀ (n : ℕ) (f : Bits n → Bits n) (psi : Amp n),
        ∑ p : Bits n × Bits n, Complex.normSq (oracle f psi p)
          = ∑ p : Bits n × Bits n, Complex.normSq (psi p)) ∧
    (∀ n : ℕ, ∑ p : Bits n × Bits n, Complex.normSq (initState n p) = 1) ∧
    (∀ (n : ℕ) (f : Bits n → Bits n) (s : Bits n), SimonPromise f s →
        ∑ y : Bits n, measureFst (simonState f) y = 1) ∧
    (∀ (n : ℕ) (f : Bits n → Bits n) (s y : Bits n), SimonPromise f s →
        measureFst (simonState f) y = if bdot y s = 0 then 2 / 2 ^ n else 0) ∧
    (∀ (n : ℕ) (f : Bits n → Bits n) (s : Bits n), SimonPromise f s →
        (3 : ℝ) / 4 ≤ successProb (simonQuantumQueries n) f s) ∧
    (∀ (n q : ℕ) (A : ClassicalAlg n), 2 ≤ n → Solves A q → 2 ^ ((n - 1) / 2) ≤ q) ∧
    (∀ n : ℕ, simonQuantumQueries n ≤ 3 * (n + 1)) := by
  refine ⟨fun n psi => hadFst_normSq_sum psi,
    fun n f psi => oracle_normSq_sum f psi,
    fun n => initState_normSq_sum n,
    fun n f s hf => measureFst_total f s hf,
    fun n f s y hf => measureFst_simonState f s hf y,
    fun n f s hf => successProb_lower f s hf,
    fun n q A hn hA => classical_query_lower_bound A q hn hA,
    fun n => by simp only [simonQuantumQueries]; omega⟩

end QI

/-
The quantum query model for Simon's problem, and the analysis of one query of
Simon's algorithm.
-/
import RequestProject.SimonBasic

open scoped BigOperators
open scoped Classical
open Finset

set_option maxHeartbeats 1000000
set_option autoImplicit false

namespace QI

/-- The character `x ↦ (-1)^⟨x,y⟩` of the group of bit strings. -/
def sgn {n : ℕ} (x y : Bits n) : ℂ := if bdot x y = 0 then 1 else -1

@[simp] lemma sgn_zero_left {n : ℕ} (y : Bits n) : sgn (0 : Bits n) y = 1 := by
  simp [sgn]

lemma sgn_add_left {n : ℕ} (x x' y : Bits n) : sgn (x + x') y = sgn x y * sgn x' y := by
  simp only [sgn, bdot_add_left]
  rcases zmod_two_cases (bdot x y) with h | h <;> rcases zmod_two_cases (bdot x' y) with h' | h' <;>
      rw [h, h']
  · norm_num
  · rw [if_neg (show ¬ ((0 : ZMod 2) + 1 = 0) from by decide), if_pos rfl,
      if_neg (show ¬ ((1 : ZMod 2) = 0) from by decide)]
    norm_num
  · rw [if_neg (show ¬ ((1 : ZMod 2) + 0 = 0) from by decide), if_pos rfl,
      if_neg (show ¬ ((1 : ZMod 2) = 0) from by decide)]
    norm_num
  · rw [if_pos (show (1 : ZMod 2) + 1 = 0 from by decide),
      if_neg (show ¬ ((1 : ZMod 2) = 0) from by decide)]
    norm_num

lemma sgn_mul_self {n : ℕ} (x y : Bits n) : sgn x y * sgn x y = 1 := by
  simp only [sgn]
  split <;> norm_num

lemma conj_sgn {n : ℕ} (x y : Bits n) : (starRingEnd ℂ) (sgn x y) = sgn x y := by
  simp only [sgn]
  split <;> simp

/-- A (pure) state of the two `n`-qubit registers used by Simon's algorithm, given by its
amplitudes in the computational basis. -/
abbrev Amp (n : ℕ) : Type := Bits n × Bits n → ℂ

/-- The all-zero computational basis state. -/
def initState (n : ℕ) : Amp n := fun p => if p = (0, 0) then 1 else 0

/-- The Hadamard transform `H^{⊗n}` applied to the first register. -/
noncomputable def hadFst {n : ℕ} (psi : Amp n) : Amp n :=
  fun p => ((Real.sqrt (2 ^ n) : ℝ) : ℂ)⁻¹ * ∑ x, sgn x p.1 * psi (x, p.2)

/-- The standard quantum query (oracle) `|x, z⟩ ↦ |x, z + f x⟩`, acting on amplitudes. -/
def oracle {n : ℕ} (f : Bits n → Bits n) (psi : Amp n) : Amp n :=
  fun p => psi (p.1, p.2 - f p.1)

/-- The state produced by one iteration of Simon's algorithm: Hadamard, one query, Hadamard. -/
noncomputable def simonState {n : ℕ} (f : Bits n → Bits n) : Amp n :=
  hadFst (oracle f (hadFst (initState n)))

/-- The probability of observing `y` when measuring the first register. -/
noncomputable def measureFst {n : ℕ} (psi : Amp n) (y : Bits n) : ℝ :=
  ∑ z, Complex.normSq (psi (y, z))

/-- Simon's promise: `f` is invariant under the shift `s ≠ 0` and otherwise injective. -/
def SimonPromise {n : ℕ} (f : Bits n → Bits n) (s : Bits n) : Prop :=
  s ≠ 0 ∧ ∀ x y : Bits n, f x = f y ↔ (y = x ∨ y = x + s)

lemma sqrt_two_pow_ne_zero (n : ℕ) : ((Real.sqrt (2 ^ n) : ℝ) : ℂ) ≠ 0 := by
  have h : (0:ℝ) < Real.sqrt (2 ^ n) := Real.sqrt_pos.2 (by positivity)
  exact_mod_cast h.ne'

lemma sqrt_two_pow_sq (n : ℕ) :
    ((Real.sqrt (2 ^ n) : ℝ) : ℂ) * ((Real.sqrt (2 ^ n) : ℝ) : ℂ) = ((2 : ℂ) ^ n) := by
  rw [← Complex.ofReal_mul, Real.mul_self_sqrt (by positivity)]
  push_cast
  ring

/-- Explicit amplitudes of the state after one Simon iteration. -/
lemma simonState_apply {n : ℕ} (f : Bits n → Bits n) (y z : Bits n) :
    simonState f (y, z) =
      ((2 : ℂ) ^ n)⁻¹ * ∑ x, sgn x y * (if f x = z then 1 else 0) := by
  classical
  have h1 : ∀ x w : Bits n, hadFst (initState n) (x, w)
      = ((Real.sqrt (2 ^ n) : ℝ) : ℂ)⁻¹ * (if w = 0 then 1 else 0) := by
    intro x w
    simp only [hadFst, initState]
    congr 1
    rw [Finset.sum_eq_single (0 : Bits n)]
    · by_cases hw : w = 0 <;> simp [hw]
    · intro b _ hb
      simp [Prod.ext_iff, hb]
    · intro h; exact absurd (Finset.mem_univ (0 : Bits n)) h
  have h2 : ∀ x w : Bits n, oracle f (hadFst (initState n)) (x, w)
      = ((Real.sqrt (2 ^ n) : ℝ) : ℂ)⁻¹ * (if f x = w then 1 else 0) := by
    intro x w
    rw [oracle]
    simp only []
    rw [h1]
    congr 1
    by_cases hw : f x = w
    · simp [hw]
    · have : w - f x ≠ 0 := by
        intro hc
        exact hw (by rw [sub_eq_zero] at hc; exact hc.symm)
      simp [this, hw]
  simp only [simonState, hadFst]
  simp only [h2]
  rw [Finset.mul_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl ?_
  intro x _
  have : ((Real.sqrt (2 ^ n) : ℝ) : ℂ)⁻¹ * ((Real.sqrt (2 ^ n) : ℝ) : ℂ)⁻¹ = ((2:ℂ)^n)⁻¹ := by
    rw [← mul_inv, sqrt_two_pow_sq]
  calc ((Real.sqrt (2 ^ n) : ℝ) : ℂ)⁻¹ *
        (sgn x y * (((Real.sqrt (2 ^ n) : ℝ) : ℂ)⁻¹ * (if f x = z then 1 else 0)))
      = (((Real.sqrt (2 ^ n) : ℝ) : ℂ)⁻¹ * ((Real.sqrt (2 ^ n) : ℝ) : ℂ)⁻¹) *
        (sgn x y * (if f x = z then 1 else 0)) := by ring
    _ = ((2:ℂ)^n)⁻¹ * (sgn x y * (if f x = z then 1 else 0)) := by rw [this]

/-- The key computation: the pair sum `∑_{x,x' : f x = f x'} (-1)^{⟨x+x',y⟩}`. -/
lemma pair_sum {n : ℕ} (f : Bits n → Bits n) (s : Bits n) (hf : SimonPromise f s) (y : Bits n) :
    ∑ x : Bits n, ∑ x' : Bits n, (if f x = f x' then sgn x y * sgn x' y else 0)
      = (2 : ℂ) ^ n * (1 + sgn s y) := by
  classical
  obtain ⟨hs, hfib⟩ := hf
  have hin : ∀ x : Bits n, ∑ x' : Bits n, (if f x = f x' then sgn x y * sgn x' y else 0)
      = 1 + sgn s y := by
    intro x
    have hfilter : (Finset.univ.filter (fun x' : Bits n => f x = f x')) = {x, x + s} := by
      ext x'
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert,
        Finset.mem_singleton]
      rw [hfib x x']
    rw [← Finset.sum_filter, hfilter]
    have hne : x ≠ x + s := by
      intro hc
      exact hs (left_eq_add.mp hc)
    rw [Finset.sum_pair hne, sgn_add_left, sgn_mul_self]
    rw [← mul_assoc, sgn_mul_self, one_mul]
  rw [Finset.sum_congr rfl (fun x _ => hin x)]
  simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  simp [mul_add]

/-! ### The gates of the circuit are unitary -/

lemma sgn_comm {n : ℕ} (x y : Bits n) : sgn x y = sgn y x := by
  rw [sgn, sgn, bdot_comm]

lemma sgn_add_right {n : ℕ} (x y y' : Bits n) : sgn x (y + y') = sgn x y * sgn x y' := by
  rw [sgn_comm, sgn_add_left, sgn_comm y x, sgn_comm y' x]

/-- The sum of a nontrivial character over the group of bit strings vanishes. -/
lemma sum_sgn {n : ℕ} (w : Bits n) :
    ∑ x : Bits n, sgn x w = if w = 0 then (2:ℂ) ^ n else 0 := by
  classical
  by_cases hw : w = 0
  · subst hw
    simp [sgn, Finset.card_univ]
  · rw [if_neg hw]
    simp only [sgn]
    rw [Finset.sum_ite, Finset.sum_const, Finset.sum_const, nsmul_eq_mul, nsmul_eq_mul]
    have hfil : (Finset.univ.filter (fun x : Bits n => bdot x w = 0)) = orth w := rfl
    have hsplit : (Finset.univ.filter (fun x : Bits n => bdot x w = 0)).card
        + (Finset.univ.filter (fun x : Bits n => ¬ bdot x w = 0)).card
        = (Finset.univ : Finset (Bits n)).card :=
      Finset.card_filter_add_card_filter_not _
    have huniv : (Finset.univ : Finset (Bits n)).card = 2 ^ n := by simp
    have h2 : 2 * (orth w).card = 2 ^ n := card_orth w hw
    rw [hfil] at hsplit
    have heq : (Finset.univ.filter (fun x : Bits n => ¬ bdot x w = 0)).card = (orth w).card := by
      omega
    rw [hfil, heq]
    ring

/-- Orthogonality of the characters `x ↦ (-1)^⟨x,y⟩`. -/
lemma sgn_orthogonality {n : ℕ} (y y' : Bits n) :
    ∑ x : Bits n, sgn x y * sgn x y' = if y = y' then (2:ℂ) ^ n else 0 := by
  have h : ∀ x : Bits n, sgn x y * sgn x y' = sgn x (y + y') := by
    intro x; rw [sgn_add_right]
  rw [Finset.sum_congr rfl (fun x _ => h x), sum_sgn]
  by_cases hyy : y = y'
  · subst hyy
    rw [if_pos rfl, if_pos (bits_add_self y)]
  · rw [if_neg hyy, if_neg]
    intro hc
    apply hyy
    have hc2 := congrArg (fun w => w + y') hc
    simp only [add_assoc, bits_add_self, add_zero, zero_add] at hc2
    exact hc2

/-- **The Hadamard layer is unitary**: it preserves the total squared amplitude. -/
theorem hadFst_normSq_sum {n : ℕ} (psi : Amp n) :
    ∑ p : Bits n × Bits n, Complex.normSq (hadFst psi p)
      = ∑ p : Bits n × Bits n, Complex.normSq (psi p) := by
  classical
  have hpow : ((2:ℂ))^n ≠ 0 := pow_ne_zero n two_ne_zero
  have hterm : ∀ y z : Bits n,
      ((Complex.normSq (hadFst psi (y, z)) : ℝ) : ℂ)
        = ((2:ℂ)^n)⁻¹ * ∑ x : Bits n, ∑ x' : Bits n,
            (sgn x y * sgn x' y) * (psi (x, z) * (starRingEnd ℂ) (psi (x', z))) := by
    intro y z
    rw [← Complex.mul_conj, hadFst]
    simp only []
    rw [map_mul, map_sum]
    have hc : (starRingEnd ℂ) (((Real.sqrt (2 ^ n) : ℝ) : ℂ)⁻¹)
        = ((Real.sqrt (2 ^ n) : ℝ) : ℂ)⁻¹ := by
      rw [map_inv₀, Complex.conj_ofReal]
    rw [hc, mul_mul_mul_comm, Finset.sum_mul_sum]
    have hcc : ((Real.sqrt (2 ^ n) : ℝ) : ℂ)⁻¹ * ((Real.sqrt (2 ^ n) : ℝ) : ℂ)⁻¹
        = ((2:ℂ)^n)⁻¹ := by
      rw [← mul_inv, sqrt_two_pow_sq]
    rw [hcc]
    congr 1
    refine Finset.sum_congr rfl ?_
    intro x _
    refine Finset.sum_congr rfl ?_
    intro x' _
    rw [map_mul, conj_sgn]
    ring
  have hz : ∀ z : Bits n,
      ∑ y : Bits n, ∑ x : Bits n, ∑ x' : Bits n,
        (sgn x y * sgn x' y) * (psi (x, z) * (starRingEnd ℂ) (psi (x', z)))
      = (2:ℂ)^n * ∑ x : Bits n, ((Complex.normSq (psi (x, z)) : ℝ) : ℂ) := by
    intro z
    rw [Finset.sum_comm, Finset.mul_sum]
    refine Finset.sum_congr rfl ?_
    intro x _
    rw [Finset.sum_comm]
    have hinner : ∀ x' : Bits n, ∑ y : Bits n,
        (sgn x y * sgn x' y) * (psi (x, z) * (starRingEnd ℂ) (psi (x', z)))
        = (if x = x' then (2:ℂ)^n else 0) * (psi (x, z) * (starRingEnd ℂ) (psi (x', z))) := by
      intro x'
      rw [← Finset.sum_mul]
      congr 1
      rw [Finset.sum_congr rfl (fun y _ => by rw [sgn_comm x y, sgn_comm x' y])]
      exact sgn_orthogonality x x'
    rw [Finset.sum_congr rfl (fun x' _ => hinner x'), Finset.sum_eq_single x]
    · rw [if_pos rfl, ← Complex.mul_conj]
    · intro b _ hb
      rw [if_neg (fun hc => hb hc.symm), zero_mul]
    · intro h; exact absurd (Finset.mem_univ x) h
  have key : ((∑ p : Bits n × Bits n, Complex.normSq (hadFst psi p) : ℝ) : ℂ)
      = ((∑ p : Bits n × Bits n, Complex.normSq (psi p) : ℝ) : ℂ) := by
    rw [Complex.ofReal_sum, Complex.ofReal_sum, Fintype.sum_prod_type, Fintype.sum_prod_type]
    calc ∑ y : Bits n, ∑ z : Bits n, ((Complex.normSq (hadFst psi (y, z)) : ℝ) : ℂ)
        = ∑ y : Bits n, ∑ z : Bits n, ((2:ℂ)^n)⁻¹ * ∑ x : Bits n, ∑ x' : Bits n,
            (sgn x y * sgn x' y) * (psi (x, z) * (starRingEnd ℂ) (psi (x', z))) :=
          Finset.sum_congr rfl (fun y _ => Finset.sum_congr rfl (fun z _ => hterm y z))
      _ = ∑ z : Bits n, ∑ y : Bits n, ((2:ℂ)^n)⁻¹ * ∑ x : Bits n, ∑ x' : Bits n,
            (sgn x y * sgn x' y) * (psi (x, z) * (starRingEnd ℂ) (psi (x', z))) :=
          Finset.sum_comm
      _ = ∑ z : Bits n, ∑ x : Bits n, ((Complex.normSq (psi (x, z)) : ℝ) : ℂ) := by
          refine Finset.sum_congr rfl ?_
          intro z _
          rw [← Finset.mul_sum, hz z, ← mul_assoc, inv_mul_cancel₀ hpow, one_mul]
      _ = ∑ x : Bits n, ∑ z : Bits n, ((Complex.normSq (psi (x, z)) : ℝ) : ℂ) :=
          Finset.sum_comm
  exact_mod_cast key

/-- **The quantum query is unitary**: it preserves the total squared amplitude. -/
theorem oracle_normSq_sum {n : ℕ} (f : Bits n → Bits n) (psi : Amp n) :
    ∑ p : Bits n × Bits n, Complex.normSq (oracle f psi p)
      = ∑ p : Bits n × Bits n, Complex.normSq (psi p) := by
  classical
  rw [Fintype.sum_prod_type, Fintype.sum_prod_type]
  refine Finset.sum_congr rfl ?_
  intro x _
  refine Finset.sum_nbij' (fun z => z - f x) (fun z => z + f x) ?_ ?_ ?_ ?_ ?_
  · intro z _; exact Finset.mem_univ _
  · intro z _; exact Finset.mem_univ _
  · intro z _; simp
  · intro z _; simp
  · intro z _; rfl

/-- The initial state is normalized. -/
theorem initState_normSq_sum (n : ℕ) :
    ∑ p : Bits n × Bits n, Complex.normSq (initState n p) = 1 := by
  classical
  rw [Finset.sum_eq_single ((0 : Bits n), (0 : Bits n))]
  · simp [initState]
  · intro b _ hb
    simp [initState, hb]
  · intro h; exact absurd (Finset.mem_univ _) h

/-- **One quantum query suffices to sample uniformly from `s^⊥`.**  Measuring the first
register after one iteration of Simon's algorithm yields a uniformly random element of the
hyperplane orthogonal to the hidden shift `s`. -/
theorem measureFst_simonState {n : ℕ} (f : Bits n → Bits n) (s : Bits n)
    (hf : SimonPromise f s) (y : Bits n) :
    measureFst (simonState f) y = if bdot y s = 0 then 2 / 2 ^ n else 0 := by
  classical
  have hexp : ∀ z : Bits n, ((Complex.normSq (simonState f (y, z)) : ℝ) : ℂ)
      = ((2:ℂ)^n)⁻¹ * ((2:ℂ)^n)⁻¹ *
        ∑ x : Bits n, ∑ x' : Bits n,
          ((if f x = z then (1:ℂ) else 0) * (if f x' = z then (1:ℂ) else 0)) *
            (sgn x y * sgn x' y) := by
    intro z
    rw [← Complex.mul_conj, simonState_apply]
    rw [map_mul, map_inv₀]
    have hconjpow : (starRingEnd ℂ) ((2:ℂ)^n) = (2:ℂ)^n := by
      rw [map_pow, Complex.conj_ofNat]
    rw [hconjpow, map_sum, mul_mul_mul_comm, Finset.sum_mul_sum]
    congr 1
    refine Finset.sum_congr rfl ?_
    intro x _
    refine Finset.sum_congr rfl ?_
    intro x' _
    rw [map_mul, conj_sgn]
    have hcz : (starRingEnd ℂ) (if f x' = z then (1:ℂ) else 0) = (if f x' = z then (1:ℂ) else 0) := by
      split <;> simp
    rw [hcz]
    ring
  have hswap : ∑ z : Bits n, ∑ x : Bits n, ∑ x' : Bits n,
        ((if f x = z then (1:ℂ) else 0) * (if f x' = z then (1:ℂ) else 0)) *
          (sgn x y * sgn x' y)
      = ∑ x : Bits n, ∑ x' : Bits n, (if f x = f x' then sgn x y * sgn x' y else 0) := by
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl ?_
    intro x _
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl ?_
    intro x' _
    rw [← Finset.sum_mul]
    by_cases hxx : f x = f x'
    · rw [if_pos hxx]
      have hone : ∑ z : Bits n, (if f x = z then (1:ℂ) else 0) * (if f x' = z then (1:ℂ) else 0)
          = 1 := by
        rw [Finset.sum_eq_single (f x)]
        · simp [hxx]
        · intro b _ hb
          simp [Ne.symm hb]
        · intro h; exact absurd (Finset.mem_univ (f x)) h
      rw [hone, one_mul]
    · rw [if_neg hxx]
      have hzero : ∑ z : Bits n, (if f x = z then (1:ℂ) else 0) * (if f x' = z then (1:ℂ) else 0)
          = 0 := by
        refine Finset.sum_eq_zero ?_
        intro z _
        by_cases h1 : f x = z
        · by_cases h2 : f x' = z
          · exact absurd (h1.trans h2.symm) hxx
          · simp [h2]
        · simp [h1]
      rw [hzero, zero_mul]
  have hpow : ((2:ℂ))^n ≠ 0 := pow_ne_zero n two_ne_zero
  have hcomplex : ((measureFst (simonState f) y : ℝ) : ℂ)
      = ((2:ℂ)^n)⁻¹ * (1 + sgn s y) := by
    rw [measureFst]
    push_cast
    rw [Finset.sum_congr rfl (fun z _ => hexp z), ← Finset.mul_sum, hswap,
      pair_sum f s hf y]
    field_simp
  rcases zmod_two_cases (bdot y s) with h | h
  · rw [if_pos h]
    have hsg : sgn s y = 1 := by
      simp [sgn, bdot_comm s y, h]
    rw [hsg] at hcomplex
    have : ((measureFst (simonState f) y : ℝ) : ℂ) = (((2 / 2 ^ n : ℝ)) : ℂ) := by
      rw [hcomplex]; push_cast; ring
    exact_mod_cast this
  · rw [if_neg (by rw [h]; decide)]
    have hsg : sgn s y = -1 := by
      simp [sgn, bdot_comm s y, h]
    rw [hsg] at hcomplex
    have : ((measureFst (simonState f) y : ℝ) : ℂ) = ((0 : ℝ) : ℂ) := by
      rw [hcomplex]; push_cast; ring
    exact_mod_cast this

end QI

