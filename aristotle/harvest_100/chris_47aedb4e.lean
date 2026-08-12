import RequestProject.Machine

/-!
# The inductive counting construction

Given a nondeterministic branching program we build, by Immerman and Szelepcsényi's
inductive counting method, a nondeterministic branching program of polynomially larger
size accepting exactly the complementary language.
-/

namespace CS

namespace Compl

variable {n : ℕ} (P : Setup n)

/-! ### The invariant -/

variable (x : Fin n → Bool)

/-- The set of configurations of the original machine reachable in at most `i` steps. -/
def RS (i : ℕ) : Set P.V := Rle (P.step x) P.st i

/-- All levels below `i` have been certified to contain no accepting configuration. -/
def Cert (i : ℕ) : Prop := ∀ k, k + 1 ≤ i → ∀ y ∈ RS P x k, ¬ P.acc y

/-- The number of vertices of level `i` whose index is below `p`. -/
noncomputable def Cnt (i p : ℕ) : ℕ := {y ∈ RS P x i | P.idx y < p}.ncard

lemma Cnt_zero (i : ℕ) : Cnt P x i 0 = 0 := by
  have hs : {y ∈ RS P x i | P.idx y < 0} = (∅ : Set P.V) := by
    ext y; simp
  rw [Cnt, hs, Set.ncard_empty]

lemma Cnt_full (i : ℕ) : Cnt P x i P.N = (RS P x i).ncard := by
  have hs : {y ∈ RS P x i | P.idx y < P.N} = RS P x i := by
    ext y; simp [P.idx_lt y]
  rw [Cnt, hs]

lemma sep_lt_succ_of_mem {i p : ℕ} (hp : p < P.N) (h : P.vAt p ∈ RS P x i) :
    {y ∈ RS P x i | P.idx y < p + 1} = insert (P.vAt p) {y ∈ RS P x i | P.idx y < p} := by
  ext y
  simp only [Set.mem_sep_iff, Set.mem_insert_iff]
  constructor
  · rintro ⟨hy, hlt⟩
    rcases Nat.lt_succ_iff_lt_or_eq.mp hlt with h1 | h1
    · exact Or.inr ⟨hy, h1⟩
    · exact Or.inl (by rw [← h1, P.vAt_idx])
  · rintro (rfl | ⟨hy, hlt⟩)
    · exact ⟨h, by simp [P.idx_vAt hp]⟩
    · exact ⟨hy, by omega⟩

lemma vAt_not_mem_sep {i p : ℕ} (hp : p < P.N) :
    P.vAt p ∉ {y ∈ RS P x i | P.idx y < p} := by
  rintro ⟨-, hlt⟩
  rw [P.idx_vAt hp] at hlt
  omega

lemma Cnt_succ_mem (i p : ℕ) (hp : p < P.N) (h : P.vAt p ∈ RS P x i) :
    Cnt P x i (p + 1) = Cnt P x i p + 1 := by
  rw [Cnt, sep_lt_succ_of_mem P x hp h,
    Set.ncard_insert_of_notMem (vAt_not_mem_sep P x hp) (Set.toFinite _)]
  rfl

lemma Cnt_succ_not_mem (i p : ℕ) (h : P.vAt p ∉ RS P x i) :
    Cnt P x i (p + 1) = Cnt P x i p := by
  have hsplit : {y ∈ RS P x i | P.idx y < p + 1} = {y ∈ RS P x i | P.idx y < p} := by
    ext y
    simp only [Set.mem_sep_iff]
    constructor
    · rintro ⟨hy, hlt⟩
      refine ⟨hy, ?_⟩
      rcases Nat.lt_succ_iff_lt_or_eq.mp hlt with h1 | h1
      · exact h1
      · exact absurd (by rw [← h1, P.vAt_idx]; exact hy) h
    · rintro ⟨hy, hlt⟩; exact ⟨hy, by omega⟩
  rw [Cnt, hsplit]; rfl

lemma Cnt_le (i p : ℕ) (hp : p ≤ P.N) : Cnt P x i p ≤ p := by
  classical
  induction p with
  | zero => simp [Cnt_zero]
  | succ p ih =>
      by_cases hm : P.vAt p ∈ RS P x i
      · rw [Cnt_succ_mem P x i p (by omega) hm]
        have := ih (by omega)
        omega
      · rw [Cnt_succ_not_mem P x i p hm]
        have := ih (by omega)
        omega

/-- The part of the invariant describing the set of vertices already counted by the
inner loop. -/
def SInv (s : CSt P.N P.V) : Prop :=
  ∃ S : Set P.V, S ⊆ {y ∈ RS P x (s.i : ℕ) | P.idx y < (s.u : ℕ)} ∧ S.ncard = (s.c : ℕ) ∧
    (∀ y ∈ S, ¬ P.acc y) ∧
    (s.fnd = true ↔ ∃ y ∈ S, (y = P.vAt (s.v : ℕ) ∨ P.step x y (P.vAt (s.v : ℕ))))

/-- The invariant at the top of the round loop. -/
def InvRound (s : CSt P.N P.V) : Prop :=
  (s.i : ℕ) ≤ P.N ∧ (s.r : ℕ) = (RS P x (s.i : ℕ)).ncard ∧ Cert P x (s.i : ℕ)

/-- The invariant at the top of the outer loop. -/
def InvOuter (s : CSt P.N P.V) : Prop :=
  (s.i : ℕ) < P.N ∧ (s.r : ℕ) = (RS P x (s.i : ℕ)).ncard ∧ Cert P x (s.i : ℕ) ∧
    (s.v : ℕ) ≤ P.N ∧ (s.r2 : ℕ) = Cnt P x ((s.i : ℕ) + 1) (s.v : ℕ) ∧
    (0 < (s.v : ℕ) → Cert P x ((s.i : ℕ) + 1))

/-- The invariant during one pass of the outer loop. -/
def InvCore (s : CSt P.N P.V) : Prop :=
  (s.i : ℕ) < P.N ∧ (s.r : ℕ) = (RS P x (s.i : ℕ)).ncard ∧ Cert P x (s.i : ℕ) ∧
    (s.v : ℕ) < P.N ∧ (s.r2 : ℕ) = Cnt P x ((s.i : ℕ) + 1) (s.v : ℕ) ∧
    (0 < (s.v : ℕ) → Cert P x ((s.i : ℕ) + 1))

/-- The invariant of the complementing machine. -/
def Inv (s : CSt P.N P.V) : Prop :=
  (s.pc = 0 → InvRound P x s) ∧
  (s.pc = 1 → InvOuter P x s) ∧
  (s.pc = 2 → InvCore P x s ∧ (s.u : ℕ) ≤ P.N ∧ SInv P x s) ∧
  (s.pc = 3 → InvCore P x s ∧ (s.u : ℕ) < P.N ∧ SInv P x s ∧ (s.j : ℕ) ≤ (s.i : ℕ) ∧
      s.w ∈ RS P x (s.j : ℕ)) ∧
  (s.pc = 4 → Cert P x P.N)

lemma inv_start : Inv P x (cstart P) := by
  have hpc : (cstart P).pc = 0 := rfl
  refine ⟨fun _ => ⟨?_, ?_, ?_⟩, ?_, ?_, ?_, ?_⟩
  · simp [cstart]
  · have h1 : RS P x ((cstart P).i : ℕ) = {P.st} := by simp [cstart, RS]
    rw [h1]
    simp [cstart]
  · intro k hk
    simp [cstart] at hk
  all_goals (intro h; rw [hpc] at h; exact absurd h (by decide))

lemma inv_mk0 (s : CSt P.N P.V) (hpc : s.pc = 0) (h : InvRound P x s) : Inv P x s := by
  refine ⟨fun _ => h, ?_, ?_, ?_, ?_⟩ <;>
    (intro hx; rw [hpc] at hx; exact absurd hx (by decide))

lemma inv_mk1 (s : CSt P.N P.V) (hpc : s.pc = 1) (h : InvOuter P x s) : Inv P x s := by
  refine ⟨?_, fun _ => h, ?_, ?_, ?_⟩ <;>
    (intro hx; rw [hpc] at hx; exact absurd hx (by decide))

lemma inv_mk2 (s : CSt P.N P.V) (hpc : s.pc = 2) (hc : InvCore P x s) (hu : (s.u : ℕ) ≤ P.N)
    (hS : SInv P x s) : Inv P x s := by
  refine ⟨?_, ?_, fun _ => ⟨hc, hu, hS⟩, ?_, ?_⟩ <;>
    (intro hx; rw [hpc] at hx; exact absurd hx (by decide))

lemma inv_mk3 (s : CSt P.N P.V) (hpc : s.pc = 3) (hc : InvCore P x s) (hu : (s.u : ℕ) < P.N)
    (hS : SInv P x s) (hj : (s.j : ℕ) ≤ (s.i : ℕ)) (hw : s.w ∈ RS P x (s.j : ℕ)) :
    Inv P x s := by
  refine ⟨?_, ?_, ?_, fun _ => ⟨hc, hu, hS, hj, hw⟩, ?_⟩ <;>
    (intro hx; rw [hpc] at hx; exact absurd hx (by decide))

lemma inv_mk4 (s : CSt P.N P.V) (hpc : s.pc = 4) (h : Cert P x P.N) : Inv P x s := by
  refine ⟨?_, ?_, ?_, ?_, fun _ => h⟩ <;>
    (intro hx; rw [hpc] at hx; exact absurd hx (by decide))

lemma ext_pres {s t : CSt P.N P.V} (hs : Inv P x s) (hE : Ext P s t)
    (hedge : P.step x s.w t.w) : Inv P x t := by
  obtain ⟨hpc, hji, j', w', hj', rfl⟩ := hE
  obtain ⟨hcore, hu, hS, hjle, hw⟩ := hs.2.2.2.1 hpc
  refine inv_mk3 P x _ hpc hcore hu hS ?_ ?_
  · show (j' : ℕ) ≤ (s.i : ℕ)
    omega
  · show w' ∈ RS P x (j' : ℕ)
    rw [hj']
    exact Or.inr ⟨s.w, hw, hedge⟩

lemma base9_pres {s t : CSt P.N P.V} (hs : Inv P x s) (hB : Base9 P s t)
    (hfnd : t.fnd = true ↔
      (s.fnd = true ∨ P.vAt (s.u : ℕ) = P.vAt (s.v : ℕ) ∨
        P.step x (P.vAt (s.u : ℕ)) (P.vAt (s.v : ℕ)))) : Inv P x t := by
  obtain ⟨hpc, hwu, hacc, huN, hcN, c', u', f', hc', hu', rfl⟩ := hB
  obtain ⟨hcore, hult, hSex, hjle, hw⟩ := hs.2.2.2.1 hpc
  obtain ⟨S, hSsub, hScard, hSacc, hSfnd⟩ := hSex
  have hfnd' : f' = true ↔
      (s.fnd = true ∨ P.vAt (s.u : ℕ) = P.vAt (s.v : ℕ) ∨
        P.step x (P.vAt (s.u : ℕ)) (P.vAt (s.v : ℕ))) := hfnd
  have hvu : P.vAt (s.u : ℕ) ∈ RS P x (s.i : ℕ) := by
    rw [← hwu]
    exact Rle_mono (P.step x) P.st hjle hw
  have hnot : P.vAt (s.u : ℕ) ∉ S := by
    intro hmem
    obtain ⟨-, hlt⟩ := hSsub hmem
    rw [P.idx_vAt huN] at hlt
    omega
  refine inv_mk2 P x _ rfl hcore (by show (u' : ℕ) ≤ P.N; omega) ?_
  refine ⟨insert (P.vAt (s.u : ℕ)) S, ?_, ?_, ?_, ?_⟩
  · intro y hy
    rcases hy with rfl | hy
    · exact ⟨hvu, by show P.idx (P.vAt (s.u : ℕ)) < (u' : ℕ); rw [P.idx_vAt huN]; omega⟩
    · obtain ⟨h1, h2⟩ := hSsub hy
      exact ⟨h1, by show P.idx y < (u' : ℕ); omega⟩
  · rw [Set.ncard_insert_of_notMem hnot (Set.toFinite _), hScard]
    show (s.c : ℕ) + 1 = (c' : ℕ)
    omega
  · intro y hy
    rcases hy with rfl | hy
    · rw [← hwu]; exact hacc
    · exact hSacc y hy
  · show f' = true ↔ ∃ y ∈ insert (P.vAt (s.u : ℕ)) S,
      (y = P.vAt (s.v : ℕ) ∨ P.step x y (P.vAt (s.v : ℕ)))
    rw [hfnd']
    constructor
    · rintro (h1 | h1 | h1)
      · obtain ⟨y, hy, hy2⟩ := hSfnd.mp h1
        exact ⟨y, Or.inr hy, hy2⟩
      · exact ⟨P.vAt (s.u : ℕ), Or.inl rfl, Or.inl h1⟩
      · exact ⟨P.vAt (s.u : ℕ), Or.inl rfl, Or.inr h1⟩
    · rintro ⟨y, (rfl | hy), hy2⟩
      · exact Or.inr hy2
      · exact Or.inl (hSfnd.mpr ⟨y, hy, hy2⟩)

lemma inv_step {s t : CSt P.N P.V} (hs : Inv P x s) (h : cstep P x s t) : Inv P x t := by
  have hqa9 : ∀ {t' : CSt P.N P.V}, Base9 P s t' → qa P s t' = P.vAt (s.u : ℕ) := by
    intro t' hB
    have h2 : t'.pc = 2 := Base9_tpc P hB
    rw [qa, if_neg]
    rintro ⟨-, h3⟩
    rw [h2] at h3
    exact absurd h3 (by decide)
  have hqb9 : ∀ {t' : CSt P.N P.V}, Base9 P s t' → qb P s t' = P.vAt (s.v : ℕ) := by
    intro t' hB
    have h2 : t'.pc = 2 := Base9_tpc P hB
    rw [qb, if_neg]
    rintro ⟨-, h3⟩
    rw [h2] at h3
    exact absurd h3 (by decide)
  rcases h with hU | ⟨hP, hq⟩ | ⟨⟨hB, hP0, hf⟩, hq⟩
  · rcases hU with ⟨h1, h2, rfl⟩ | ⟨h1, h2, rfl⟩ | ⟨h1, h2, i', hi', rfl⟩ | ⟨h1, h2, rfl⟩ |
      ⟨h1, h2, h3, r2', v', hr2', hv', rfl⟩ | ⟨h1, h2, u', hu', rfl⟩ | ⟨h1, h2, rfl⟩ |
      ⟨hB, hP0, hf⟩
    -- accept
    · obtain ⟨hi, hr, hcert⟩ := hs.1 h1
      refine inv_mk4 P x _ rfl ?_
      rw [← h2]; exact hcert
    -- start a new round
    · obtain ⟨hi, hr, hcert⟩ := hs.1 h1
      refine inv_mk1 P x _ rfl ⟨h2, hr, hcert, ?_, ?_, ?_⟩
      · show ((0 : Fin (P.N + 1)) : ℕ) ≤ P.N
        simp
      · show ((0 : Fin (P.N + 1)) : ℕ) = Cnt P x ((s.i : ℕ) + 1) ((0 : Fin (P.N + 1)) : ℕ)
        simp [Cnt_zero]
      · intro hpos
        simp at hpos
    -- finish a round
    · obtain ⟨hi, hr, hcert, hv, hr2, hcert1⟩ := hs.2.1 h1
      refine inv_mk0 P x _ rfl ⟨?_, ?_, ?_⟩
      · show (i' : ℕ) ≤ P.N
        omega
      · show (s.r2 : ℕ) = (RS P x (i' : ℕ)).ncard
        rw [hi', hr2, h2, Cnt_full]
      · show Cert P x (i' : ℕ)
        rw [hi']
        exact hcert1 (by have := P.hN; omega)
    -- start a pass of the outer loop
    · obtain ⟨hi, hr, hcert, hv, hr2, hcert1⟩ := hs.2.1 h1
      refine inv_mk2 P x _ rfl ⟨hi, hr, hcert, h2, hr2, hcert1⟩ (by simp) ?_
      refine ⟨∅, by simp, by simp, by simp, ?_⟩
      show (false : Bool) = true ↔ ∃ y ∈ (∅ : Set P.V),
        (y = P.vAt ((s.v : ℕ)) ∨ P.step x y (P.vAt ((s.v : ℕ))))
      simp
    -- finish a pass of the outer loop
    · obtain ⟨⟨hi, hr, hcert, hv, hr2, hcert1⟩, hu, S, hSsub, hScard, hSacc, hSfnd⟩ :=
        hs.2.2.1 h1
      have hsub2 : S ⊆ RS P x (s.i : ℕ) := fun y hy => (hSsub hy).1
      have hcards : (RS P x (s.i : ℕ)).ncard ≤ S.ncard := by
        rw [hScard, h3, hr]
      have hSeq : S = RS P x (s.i : ℕ) :=
        Set.eq_of_subset_of_ncard_le hsub2 hcards (Set.toFinite _)
      have hallacc : ∀ y ∈ RS P x (s.i : ℕ), ¬ P.acc y := by rw [← hSeq]; exact hSacc
      have hcertnew : Cert P x ((s.i : ℕ) + 1) := by
        intro k hk y hy
        rcases Nat.lt_or_ge k (s.i : ℕ) with hlt | hge
        · exact hcert k (by omega) y hy
        · have hki : k = (s.i : ℕ) := by omega
          subst hki
          exact hallacc y hy
      have hfnd2 : s.fnd = true ↔ P.vAt (s.v : ℕ) ∈ RS P x ((s.i : ℕ) + 1) := by
        rw [hSfnd, hSeq]
        constructor
        · rintro ⟨y, hy, (rfl | hstep)⟩
          · exact Or.inl hy
          · exact Or.inr ⟨y, hy, hstep⟩
        · rintro (hmem | ⟨y, hy, hstep⟩)
          · exact ⟨_, hmem, Or.inl rfl⟩
          · exact ⟨y, hy, Or.inr hstep⟩
      refine inv_mk1 P x _ rfl ⟨hi, hr, hcert, ?_, ?_, ?_⟩
      · show (v' : ℕ) ≤ P.N
        omega
      · show (r2' : ℕ) = Cnt P x ((s.i : ℕ) + 1) ((v' : ℕ))
        rw [hv', hr2', hr2]
        cases hb : s.fnd
        · have hnm : P.vAt (s.v : ℕ) ∉ RS P x ((s.i : ℕ) + 1) := by
            intro hm
            rw [hfnd2.mpr hm] at hb
            exact absurd hb (by decide)
          rw [Cnt_succ_not_mem P x _ _ hnm]
          simp
        · rw [Cnt_succ_mem P x _ _ hv (hfnd2.mp hb)]
          simp
      · intro _
        exact hcertnew
    -- skip a vertex in the inner loop
    · obtain ⟨hcore, hu, S, hSsub, hScard, hSacc, hSfnd⟩ := hs.2.2.1 h1
      refine inv_mk2 P x _ h1 hcore (by show (u' : ℕ) ≤ P.N; omega)
        ⟨S, ?_, hScard, hSacc, hSfnd⟩
      intro y hy
      obtain ⟨p1, p2⟩ := hSsub hy
      exact ⟨p1, by show P.idx y < (u' : ℕ); omega⟩
    -- start guessing a path
    · obtain ⟨hcore, hu, hS⟩ := hs.2.2.1 h1
      refine inv_mk3 P x _ rfl hcore h2 hS ?_ ?_
      · show ((0 : Fin (P.N + 1)) : ℕ) ≤ (s.i : ℕ)
        simp
      · show P.st ∈ RS P x ((0 : Fin (P.N + 1)) : ℕ)
        simp [RS]
    -- finish a path, with the flag already set
    · exact base9_pres P x hs hB ⟨fun _ => hP0.imp id Or.inl, fun _ => hf⟩
  · rcases hP with hE | ⟨hB, hP0, hf⟩
    · refine ext_pres P x hs hE ?_
      rw [qa, if_pos ⟨Ext_spc P hE, Ext_tpc P hE⟩, qb,
        if_pos ⟨Ext_spc P hE, Ext_tpc P hE⟩] at hq
      exact hq
    · refine base9_pres P x hs hB ?_
      rw [hqa9 hB, hqb9 hB] at hq
      exact ⟨fun _ => Or.inr (Or.inr hq), fun _ => hf⟩
  · refine base9_pres P x hs hB ?_
    rw [hqa9 hB, hqb9 hB] at hq
    rw [hf]
    push_neg at hP0
    constructor
    · intro h'
      exact absurd h' (by decide)
    · rintro (h1 | h1 | h1)
      · exact absurd h1 hP0.1
      · exact absurd h1 hP0.2
      · have h1' : (P.edg (P.vAt (s.u : ℕ)) (P.vAt (s.v : ℕ))).eval x = true := h1
        rw [hq] at h1'
        exact absurd h1' (by decide)

/-! ### Completeness of the construction -/

lemma inv_of_reach {s : CSt P.N P.V} (h : Relation.ReflTransGen (cstep P x) (cstart P) s) :
    Inv P x s := by
  induction h with
  | refl => exact inv_start P x
  | tail _ hstep ih => exact inv_step P x ih hstep

lemma sound {s : CSt P.N P.V} (h : Relation.ReflTransGen (cstep P x) (cstart P) s)
    (hpc : s.pc = 4) : ∀ y, Relation.ReflTransGen (P.step x) P.st y → ¬ P.acc y := by
  have hInv : Inv P x s := inv_of_reach P x h
  intro y hy hacc
  have hcert := hInv.2.2.2.2 hpc
  have hmem : y ∈ Rle (P.step x) P.st (Fintype.card P.V - 1) :=
    reach_mem_Rle_card (P.step x) P.st hy
  rw [P.card_V] at hmem
  exact hcert (P.N - 1) (by have := P.hN; omega) y hmem hacc

lemma path_complete (m : ℕ) : ∀ (y : P.V), y ∈ RS P x m → ∀ (s : CSt P.N P.V), s.pc = 3 →
    s.w = P.st → (s.j : ℕ) = 0 → m ≤ (s.i : ℕ) →
    ∃ j' : Fin (P.N + 1), (j' : ℕ) ≤ m ∧
      Relation.ReflTransGen (cstep P x) s { s with j := j', w := y } := by
  induction m with
  | zero =>
      intro y hy s hpc hw hj hm
      have hyst : y = P.st := hy
      refine ⟨s.j, by omega, ?_⟩
      have hst : ({ s with j := s.j, w := y } : CSt P.N P.V) = s := by
        rw [hyst, ← hw]
      rw [hst]
  | succ m ih =>
      intro y hy s hpc hw hj hm
      have hiN : (s.i : ℕ) ≤ P.N := by have := s.i.isLt; omega
      rcases hy with hy | ⟨y', hy', hstep⟩
      · obtain ⟨j', hj', hpath⟩ := ih y hy s hpc hw hj (by omega)
        exact ⟨j', by omega, hpath⟩
      · obtain ⟨j', hj'le, hpath⟩ := ih y' hy' s hpc hw hj (by omega)
        refine ⟨⟨(j' : ℕ) + 1, by omega⟩, by simp; omega, ?_⟩
        refine hpath.tail ?_
        have hpc2 : ({ s with j := j', w := y' } : CSt P.N P.V).pc = 3 := hpc
        have hpc3 : ({ s with j := (⟨(j' : ℕ) + 1, by omega⟩ : Fin (P.N + 1)), w := y } :
            CSt P.N P.V).pc = 3 := hpc
        refine Or.inr (Or.inl ⟨Or.inl ⟨hpc2, ?_, ⟨(j' : ℕ) + 1, by omega⟩, y, rfl, rfl⟩, ?_⟩)
        · show (j' : ℕ) < (s.i : ℕ)
          omega
        · rw [qa, if_pos ⟨hpc2, hpc3⟩, qb, if_pos ⟨hpc2, hpc3⟩]
          exact hstep

lemma not_acc_of_mem_RS (hno : ∀ y, Relation.ReflTransGen (P.step x) P.st y → ¬ P.acc y)
    (i : ℕ) (y : P.V) (hy : y ∈ RS P x i) : ¬ P.acc y :=
  hno y (Rle_subset_reach (P.step x) P.st hy)

lemma inner_complete (hno : ∀ y, Relation.ReflTransGen (P.step x) P.st y → ¬ P.acc y) (d : ℕ) :
    ∀ (p : ℕ) (s : CSt P.N P.V), p + d = P.N → s.pc = 2 → (s.u : ℕ) = p →
      (s.c : ℕ) = Cnt P x (s.i : ℕ) p →
      (s.fnd = true ↔ ∃ y ∈ RS P x (s.i : ℕ), P.idx y < p ∧
        (y = P.vAt (s.v : ℕ) ∨ P.step x y (P.vAt (s.v : ℕ)))) →
      ∃ t : CSt P.N P.V, Relation.ReflTransGen (cstep P x) s t ∧ t.pc = 2 ∧ t.i = s.i ∧
        t.r = s.r ∧ t.r2 = s.r2 ∧ t.v = s.v ∧ (t.u : ℕ) = P.N ∧
        (t.c : ℕ) = Cnt P x (s.i : ℕ) P.N ∧
        (t.fnd = true ↔ ∃ y ∈ RS P x (s.i : ℕ), P.idx y < P.N ∧
          (y = P.vAt (s.v : ℕ) ∨ P.step x y (P.vAt (s.v : ℕ)))) := by
  classical
  induction d with
  | zero =>
      intro p s hpd hpc hu hc hfnd
      have hp : p = P.N := by omega
      subst hp
      exact ⟨s, .refl, hpc, rfl, rfl, rfl, rfl, hu, hc, hfnd⟩
  | succ d ih =>
      intro p s hpd hpc hu hc hfnd
      have hpN : p < P.N := by omega
      have hcp : (s.c : ℕ) ≤ p := by
        rw [hc]; exact Cnt_le P x _ _ (by omega)
      by_cases hmem : P.vAt p ∈ RS P x (s.i : ℕ)
      · -- count the vertex `vAt p`
        obtain ⟨c', hc'⟩ : ∃ c' : Fin (P.N + 1), (c' : ℕ) = (s.c : ℕ) + 1 :=
          ⟨⟨(s.c : ℕ) + 1, by omega⟩, rfl⟩
        obtain ⟨u', hu'⟩ : ∃ u' : Fin (P.N + 1), (u' : ℕ) = p + 1 := ⟨⟨p + 1, by omega⟩, rfl⟩
        set s1 : CSt P.N P.V := { s with pc := 3, w := P.st, j := 0 } with hs1
        have hstep1 : cstep P x s s1 :=
          Or.inl (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl
             ⟨hpc, by omega, rfl⟩)))))))
        obtain ⟨j', hj'le, hpath⟩ :=
          path_complete P x (s.i : ℕ) (P.vAt p) hmem s1 rfl rfl (by simp [hs1]) le_rfl
        set s2 : CSt P.N P.V := { s1 with j := j', w := P.vAt p } with hs2
        set f' : Bool := (s.fnd || decide (P.vAt p = P.vAt (s.v : ℕ)) ||
          decide (P.step x (P.vAt p) (P.vAt (s.v : ℕ)))) with hf'def
        set s3 : CSt P.N P.V := { s2 with pc := 2, c := c', u := u', fnd := f' } with hs3
        have hfndnew : f' = true ↔ ∃ y ∈ RS P x (s.i : ℕ), P.idx y < p + 1 ∧
            (y = P.vAt (s.v : ℕ) ∨ P.step x y (P.vAt (s.v : ℕ))) := by
          rw [hf'def]
          simp only [Bool.or_eq_true, decide_eq_true_eq]
          constructor
          · rintro ((h1 | h1) | h1)
            · obtain ⟨y, hy, hlt, hy2⟩ := hfnd.mp h1
              exact ⟨y, hy, by omega, hy2⟩
            · exact ⟨P.vAt p, hmem, by rw [P.idx_vAt hpN]; omega, Or.inl h1⟩
            · exact ⟨P.vAt p, hmem, by rw [P.idx_vAt hpN]; omega, Or.inr h1⟩
          · rintro ⟨y, hy, hlt, hy2⟩
            rcases Nat.lt_succ_iff_lt_or_eq.mp hlt with h1 | h1
            · exact Or.inl (Or.inl (hfnd.mpr ⟨y, hy, h1, hy2⟩))
            · have hyv : y = P.vAt p := by rw [← h1, P.vAt_idx]
              subst hyv
              rcases hy2 with h2 | h2
              · exact Or.inl (Or.inr h2)
              · exact Or.inr h2
        have hB : Base9 P s2 s3 := by
          refine ⟨rfl, ?_, ?_, ?_, ?_, c', u', f', ?_, ?_, rfl⟩
          · show P.vAt p = P.vAt (s.u : ℕ)
            rw [hu]
          · show ¬ P.acc (P.vAt p)
            exact not_acc_of_mem_RS P x hno _ _ hmem
          · show (s.u : ℕ) < P.N
            omega
          · show (s.c : ℕ) < P.N
            omega
          · show (c' : ℕ) = (s.c : ℕ) + 1
            exact hc'
          · show (u' : ℕ) = (s.u : ℕ) + 1
            omega
        have hqa : qa P s2 s3 = P.vAt p := by
          rw [qa, if_neg (by rintro ⟨-, h3⟩; exact absurd (show (2 : Fin 5) = 3 from h3) (by decide))]
          show P.vAt (s.u : ℕ) = P.vAt p
          rw [hu]
        have hqb : qb P s2 s3 = P.vAt (s.v : ℕ) := by
          rw [qb, if_neg (by rintro ⟨-, h3⟩; exact absurd (show (2 : Fin 5) = 3 from h3) (by decide))]
        have hstep3 : cstep P x s2 s3 := by
          by_cases hP0 : (s2.fnd = true ∨ P.vAt (s2.u : ℕ) = P.vAt (s2.v : ℕ))
          · refine Or.inl (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
              ⟨hB, hP0, ?_⟩)))))))
            show f' = true
            rw [hf'def]
            rcases hP0 with h1 | h1
            · simp [show s.fnd = true from h1]
            · have h2 : P.vAt p = P.vAt (s.v : ℕ) := by
                rw [← h1]; show P.vAt p = P.vAt (s.u : ℕ); rw [hu]
              simp [h2]
          · by_cases hg : (P.edg (P.vAt p) (P.vAt (s.v : ℕ))).eval x = true
            · refine Or.inr (Or.inl ⟨Or.inr ⟨hB, hP0, ?_⟩, ?_⟩)
              · show f' = true
                rw [hf'def]
                simp [show P.step x (P.vAt p) (P.vAt (s.v : ℕ)) from hg]
              · rw [hqa, hqb]; exact hg
            · refine Or.inr (Or.inr ⟨⟨hB, hP0, ?_⟩, ?_⟩)
              · show f' = false
                push_neg at hP0
                rw [hf'def]
                have h1 : s.fnd = false := by
                  cases hb : s.fnd
                  · rfl
                  · exact absurd (show s2.fnd = true from hb) hP0.1
                have h2 : ¬ (P.vAt p = P.vAt (s.v : ℕ)) := by
                  intro h
                  refine hP0.2 ?_
                  show P.vAt (s.u : ℕ) = P.vAt (s.v : ℕ)
                  rw [hu]; exact h
                have h3 : ¬ P.step x (P.vAt p) (P.vAt (s.v : ℕ)) := hg
                simp [h1, h2, h3]
              · rw [hqa, hqb]
                simpa using hg
        obtain ⟨t, ht, ht2⟩ := ih (p + 1) s3 (by omega) rfl (by exact hu')
          (by
            show (c' : ℕ) = Cnt P x (s.i : ℕ) (p + 1)
            rw [hc', hc, Cnt_succ_mem P x _ _ hpN hmem])
          (by exact hfndnew)
        refine ⟨t, ?_, ht2.1, ht2.2.1, ht2.2.2.1, ht2.2.2.2.1, ht2.2.2.2.2.1,
          ht2.2.2.2.2.2.1, ht2.2.2.2.2.2.2.1, ht2.2.2.2.2.2.2.2⟩
        exact (Relation.ReflTransGen.head hstep1 (hpath.tail hstep3)).trans ht
      · -- skip the vertex `vAt p`
        obtain ⟨u', hu'⟩ : ∃ u' : Fin (P.N + 1), (u' : ℕ) = p + 1 := ⟨⟨p + 1, by omega⟩, rfl⟩
        have hstep1 : cstep P x s { s with u := u' } :=
          Or.inl (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl
            ⟨hpc, by omega, u', by omega, rfl⟩))))))
        have hfnd1 : ({ s with u := u' } : CSt P.N P.V).fnd = true ↔
            ∃ y ∈ RS P x (s.i : ℕ), P.idx y < p + 1 ∧
              (y = P.vAt (s.v : ℕ) ∨ P.step x y (P.vAt (s.v : ℕ))) := by
          show s.fnd = true ↔ _
          rw [hfnd]
          constructor
          · rintro ⟨y, hy, hlt, hy2⟩
            exact ⟨y, hy, by omega, hy2⟩
          · rintro ⟨y, hy, hlt, hy2⟩
            refine ⟨y, hy, ?_, hy2⟩
            rcases Nat.lt_succ_iff_lt_or_eq.mp hlt with h1 | h1
            · exact h1
            · exact absurd (by rw [← h1, P.vAt_idx]; exact hy) hmem
        obtain ⟨t, ht, ht2⟩ := ih (p + 1) { s with u := u' } (by omega) hpc (by exact hu')
          (by
            show (s.c : ℕ) = Cnt P x (s.i : ℕ) (p + 1)
            rw [hc, Cnt_succ_not_mem P x _ _ hmem])
          hfnd1
        refine ⟨t, ?_, ht2.1, ht2.2.1, ht2.2.2.1, ht2.2.2.2.1, ht2.2.2.2.2.1,
          ht2.2.2.2.2.2.1, ht2.2.2.2.2.2.2.1, ht2.2.2.2.2.2.2.2⟩
        exact Relation.ReflTransGen.head hstep1 ht

lemma outer_complete (hno : ∀ y, Relation.ReflTransGen (P.step x) P.st y → ¬ P.acc y) (d : ℕ) :
    ∀ (p : ℕ) (s : CSt P.N P.V), p + d = P.N → s.pc = 1 → (s.v : ℕ) = p → (s.i : ℕ) < P.N →
      (s.r : ℕ) = (RS P x (s.i : ℕ)).ncard → (s.r2 : ℕ) = Cnt P x ((s.i : ℕ) + 1) p →
      ∃ t : CSt P.N P.V, Relation.ReflTransGen (cstep P x) s t ∧ t.pc = 1 ∧ t.i = s.i ∧
        t.r = s.r ∧ (t.v : ℕ) = P.N ∧ (t.r2 : ℕ) = Cnt P x ((s.i : ℕ) + 1) P.N := by
  classical
  induction d with
  | zero =>
      intro p s hpd hpc hv hi hr hr2
      have hp : p = P.N := by omega
      subst hp
      exact ⟨s, .refl, hpc, rfl, rfl, hv, hr2⟩
  | succ d ih =>
      intro p s hpd hpc hv hi hr hr2
      have hpN : p < P.N := by omega
      have hstep1 : cstep P x s { s with pc := 2, c := 0, u := 0, fnd := false } :=
        Or.inl (Or.inr (Or.inr (Or.inr (Or.inl ⟨hpc, by omega, rfl⟩))))
      obtain ⟨t1, ht1, ht1pc, ht1i, ht1r, ht1r2, ht1v, ht1u, ht1c, ht1f⟩ :=
        inner_complete P x hno P.N 0 { s with pc := 2, c := 0, u := 0, fnd := false }
          (by omega) rfl (by simp) (by simp [Cnt_zero]) (by simp)
      have ht1i' : t1.i = s.i := ht1i
      have ht1r' : t1.r = s.r := ht1r
      have ht1r2' : t1.r2 = s.r2 := ht1r2
      have ht1v' : t1.v = s.v := ht1v
      have ht1c' : (t1.c : ℕ) = Cnt P x (s.i : ℕ) P.N := ht1c
      have ht1f' : t1.fnd = true ↔ ∃ y ∈ RS P x (s.i : ℕ), P.idx y < P.N ∧
          (y = P.vAt (s.v : ℕ) ∨ P.step x y (P.vAt (s.v : ℕ))) := ht1f
      have hmemiff : t1.fnd = true ↔ P.vAt p ∈ RS P x ((s.i : ℕ) + 1) := by
        rw [ht1f', hv]
        constructor
        · rintro ⟨y, hy, -, (rfl | hstep)⟩
          · exact Or.inl hy
          · exact Or.inr ⟨y, hy, hstep⟩
        · rintro (hm | ⟨y, hy, hstep⟩)
          · exact ⟨_, hm, P.idx_lt _, Or.inl rfl⟩
          · exact ⟨y, hy, P.idx_lt _, Or.inr hstep⟩
      have hcr : t1.c = t1.r := by
        apply Fin.ext
        rw [ht1c', ht1r', hr, Cnt_full]
      have hr2le : (s.r2 : ℕ) ≤ p := by
        rw [hr2]; exact Cnt_le P x _ _ (by omega)
      obtain ⟨r2', hr2'⟩ : ∃ r2' : Fin (P.N + 1),
          (r2' : ℕ) = (t1.r2 : ℕ) + (if t1.fnd = true then 1 else 0) := by
        refine ⟨⟨(t1.r2 : ℕ) + (if t1.fnd = true then 1 else 0), ?_⟩, rfl⟩
        rw [ht1r2']
        split_ifs <;> omega
      obtain ⟨v', hv'⟩ : ∃ v' : Fin (P.N + 1), (v' : ℕ) = (t1.v : ℕ) + 1 := by
        refine ⟨⟨(t1.v : ℕ) + 1, ?_⟩, rfl⟩
        rw [ht1v']
        omega
      have hstep2 : cstep P x t1 { t1 with pc := 1, r2 := r2', v := v' } :=
        Or.inl (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl
          ⟨ht1pc, ht1u, hcr, r2', v', hr2', hv', rfl⟩)))))
      have hnewr2 : (r2' : ℕ) = Cnt P x ((s.i : ℕ) + 1) ((v' : ℕ)) := by
        rw [hv', ht1v', hv, hr2', ht1r2', hr2]
        cases hb : t1.fnd
        · have hnm : P.vAt p ∉ RS P x ((s.i : ℕ) + 1) := by
            intro hm
            rw [hmemiff.mpr hm] at hb
            exact absurd hb (by decide)
          rw [Cnt_succ_not_mem P x _ _ hnm]
          simp
        · rw [Cnt_succ_mem P x _ _ hpN (hmemiff.mp hb)]
          simp
      obtain ⟨t, ht, htpc, hti, htr, htv, htr2⟩ :=
        ih (p + 1) { t1 with pc := 1, r2 := r2', v := v' } (by omega) rfl
          (by show (v' : ℕ) = p + 1; rw [hv', ht1v', hv])
          (by show ((t1.i : ℕ)) < P.N; rw [ht1i']; exact hi)
          (by show (t1.r : ℕ) = (RS P x ((t1.i : ℕ))).ncard; rw [ht1r', ht1i']; exact hr)
          (by
            show (r2' : ℕ) = Cnt P x ((t1.i : ℕ) + 1) (p + 1)
            have hvp : ((v' : ℕ)) = p + 1 := by rw [hv', ht1v', hv]
            rw [ht1i', ← hvp]
            exact hnewr2)
      refine ⟨t, (Relation.ReflTransGen.head hstep1 ht1).trans (Relation.ReflTransGen.head
        hstep2 ht), htpc, ?_, ?_, htv, ?_⟩
      · rw [hti]; exact ht1i'
      · rw [htr]; exact ht1r'
      · rw [htr2, ht1i']

lemma round_complete (hno : ∀ y, Relation.ReflTransGen (P.step x) P.st y → ¬ P.acc y) (d : ℕ) :
    ∀ (m : ℕ) (s : CSt P.N P.V), m + d = P.N → s.pc = 0 → (s.i : ℕ) = m →
      (s.r : ℕ) = (RS P x m).ncard →
      ∃ t : CSt P.N P.V, Relation.ReflTransGen (cstep P x) s t ∧ t.pc = 0 ∧ (t.i : ℕ) = P.N := by
  induction d with
  | zero =>
      intro m s hmd hpc hi hr
      exact ⟨s, .refl, hpc, by omega⟩
  | succ d ih =>
      intro m s hmd hpc hi hr
      have hmN : m < P.N := by omega
      have hstep1 : cstep P x s { s with pc := 1, r2 := 0, v := 0 } :=
        Or.inl (Or.inr (Or.inl ⟨hpc, by omega, rfl⟩))
      obtain ⟨t1, ht1, ht1pc, ht1i, ht1r, ht1v, ht1r2⟩ :=
        outer_complete P x hno P.N 0 { s with pc := 1, r2 := 0, v := 0 } (by omega) rfl
          (by simp) (by show (s.i : ℕ) < P.N; omega)
          (by show (s.r : ℕ) = (RS P x (s.i : ℕ)).ncard; rw [hi]; exact hr)
          (by simp [Cnt_zero])
      have ht1i' : t1.i = s.i := ht1i
      have ht1r2' : (t1.r2 : ℕ) = Cnt P x ((s.i : ℕ) + 1) P.N := ht1r2
      obtain ⟨i', hi'⟩ : ∃ i' : Fin (P.N + 1), (i' : ℕ) = (t1.i : ℕ) + 1 := by
        refine ⟨⟨(t1.i : ℕ) + 1, ?_⟩, rfl⟩
        rw [ht1i', hi]
        omega
      have hstep2 : cstep P x t1 { t1 with pc := 0, i := i', r := t1.r2 } :=
        Or.inl (Or.inr (Or.inr (Or.inl ⟨ht1pc, ht1v, i', hi', rfl⟩)))
      obtain ⟨t, ht, htpc, hti⟩ :=
        ih (m + 1) { t1 with pc := 0, i := i', r := t1.r2 } (by omega) rfl
          (by show (i' : ℕ) = m + 1; rw [hi', ht1i', hi])
          (by
            show (t1.r2 : ℕ) = (RS P x (m + 1)).ncard
            rw [ht1r2', hi, Cnt_full])
      exact ⟨t, (Relation.ReflTransGen.head hstep1 ht1).trans
        (Relation.ReflTransGen.head hstep2 ht), htpc, hti⟩

/-- If no accepting configuration of the original machine is reachable, then the
complementing machine has an accepting run. -/
lemma complete (hno : ∀ y, Relation.ReflTransGen (P.step x) P.st y → ¬ P.acc y) :
    ∃ t : CSt P.N P.V, t.pc = 4 ∧ Relation.ReflTransGen (cstep P x) (cstart P) t := by
  obtain ⟨t, ht, htpc, hti⟩ :=
    round_complete P x hno P.N 0 (cstart P) (by omega) rfl (by simp [cstart])
      (by
        show ((cstart P).r : ℕ) = (RS P x 0).ncard
        simp [cstart, RS])
  refine ⟨{ t with pc := 4 }, rfl, ht.tail ?_⟩
  exact Or.inl (Or.inl ⟨htpc, hti, rfl⟩)

/-! ### The complementing branching program -/

/-- The complementing nondeterministic branching program. -/
noncomputable def cNBP (P : Setup n) : NBP n where
  V := CSt P.N P.V
  fin := inferInstance
  start := cstart P
  accept := fun s => s.pc = 4
  edges := cedg P

lemma cNBP_size (P : Setup n) : (cNBP P).size = 10 * (P.N + 1) ^ 7 * P.N := by
  show Fintype.card (CSt P.N P.V) = _
  rw [card_CSt, P.card_V]

lemma cNBP_accepts (P : Setup n) (x : Fin n → Bool) :
    (cNBP P).Accepts x ↔ ¬ ∃ y, P.acc y ∧ Relation.ReflTransGen (P.step x) P.st y := by
  constructor
  · rintro ⟨s, hs4, hreach⟩ ⟨y, hacc, hy⟩
    have hreach' : Relation.ReflTransGen (cstep P x) (cstart P) s :=
      hreach.mono (fun a b h => (cedg_eval P x a b).mp h)
    exact sound P x hreach' hs4 y hy hacc
  · intro hno
    push_neg at hno
    obtain ⟨t, htpc, ht⟩ := complete P x (fun y hy hacc => hno y hacc hy)
    exact ⟨t, htpc, ht.mono (fun a b h => (cedg_eval P x a b).mpr h)⟩

end Compl

/-- The setup associated with a nondeterministic branching program. -/
noncomputable def NBP.toSetup {n : ℕ} (B : NBP n) : Compl.Setup n where
  V := B.V
  N := B.size
  e := Fintype.equivFin B.V
  st := B.start
  acc := B.accept
  edg := B.edges

/-- **Immerman-Szelepcsényi, machine form.**  For every nondeterministic branching
program there is a nondeterministic branching program of polynomially larger size
which accepts exactly the complementary set of inputs. -/
theorem NBP.exists_complement {n : ℕ} (B : NBP n) :
    ∃ B' : NBP n, B'.size ≤ 10 * (B.size + 1) ^ 8 ∧ ∀ x, (B'.Accepts x ↔ ¬ B.Accepts x) := by
  refine ⟨Compl.cNBP B.toSetup, ?_, ?_⟩
  · rw [Compl.cNBP_size]
    show 10 * (B.size + 1) ^ 7 * B.size ≤ 10 * (B.size + 1) ^ 8
    have h1 : B.size ≤ B.size + 1 := by omega
    calc 10 * (B.size + 1) ^ 7 * B.size ≤ 10 * (B.size + 1) ^ 7 * (B.size + 1) :=
          Nat.mul_le_mul_left _ h1
      _ = 10 * (B.size + 1) ^ 8 := by ring
  · intro x
    exact Compl.cNBP_accepts B.toSetup x

end CS

import RequestProject.Reach

/-!
# The states and transitions of the complementing machine

This file sets up the machine used in Immerman and Szelepcsényi's inductive counting
argument: its states, its transitions, and the guards realizing those transitions in a
nondeterministic branching program.
-/

namespace CS

namespace Compl

/-- All the data of the nondeterministic branching program we are complementing:
the configuration set `V`, an enumeration `e` of it, the start configuration, the
accepting configurations, and the guards. -/
structure Setup (n : ℕ) : Type 1 where
  /-- The configuration set. -/
  V : Type
  /-- The number of configurations. -/
  N : ℕ
  /-- An enumeration of the configurations. -/
  e : V ≃ Fin N
  /-- The start configuration. -/
  st : V
  /-- The accepting configurations. -/
  acc : V → Prop
  /-- The guards. -/
  edg : V → V → Guard n

variable {n : ℕ}

/-- The `k`-th configuration in the enumeration (junk for `k ≥ N`). -/
def Setup.vAt (P : Setup n) (k : ℕ) : P.V := if h : k < P.N then P.e.symm ⟨k, h⟩ else P.st

/-- The index of a configuration in the enumeration. -/
def Setup.idx (P : Setup n) (y : P.V) : ℕ := (P.e y : ℕ)

/-- The one-step relation of the given program on the input `x`. -/
def Setup.step (P : Setup n) (x : Fin n → Bool) : P.V → P.V → Prop :=
  fun a b => (P.edg a b).eval x = true

lemma Setup.hN (P : Setup n) : 1 ≤ P.N := by
  have := (P.e P.st).isLt; omega

lemma Setup.idx_lt (P : Setup n) (y : P.V) : P.idx y < P.N := (P.e y).isLt

@[simp] lemma Setup.idx_vAt (P : Setup n) {k : ℕ} (h : k < P.N) : P.idx (P.vAt k) = k := by
  simp [Setup.idx, Setup.vAt, h]

@[simp] lemma Setup.vAt_idx (P : Setup n) (y : P.V) : P.vAt (P.idx y) = y := by
  simp [Setup.idx, Setup.vAt]

instance (P : Setup n) : Fintype P.V := Fintype.ofEquiv _ P.e.symm

lemma Setup.card_V (P : Setup n) : Fintype.card P.V = P.N := by
  simpa using Fintype.card_congr P.e

/-! ### The states of the complementing program -/

/-- A state of the complementing machine: a program counter together with a fixed number
of counters (each at most `N`), one configuration of the original machine and one
Boolean flag. -/
structure CSt (N : ℕ) (V : Type) where
  /-- Program counter: `0` round loop, `1` outer loop, `2` inner loop, `3` path guessing,
  `4` accept. -/
  pc : Fin 5
  /-- The current round (`= level of the reachability set`). -/
  i : Fin (N + 1)
  /-- The (verified) size of the current level. -/
  r : Fin (N + 1)
  /-- The accumulator for the size of the next level. -/
  r2 : Fin (N + 1)
  /-- The position of the outer loop. -/
  v : Fin (N + 1)
  /-- The number of vertices counted in the inner loop. -/
  c : Fin (N + 1)
  /-- The position of the inner loop. -/
  u : Fin (N + 1)
  /-- The length of the path guessed so far. -/
  j : Fin (N + 1)
  /-- The endpoint of the path guessed so far. -/
  w : V
  /-- Whether the outer loop vertex was already found to be in the next level. -/
  fnd : Bool

/-- The states of the complementing machine as a product type. -/
def CSt.equivProd (N : ℕ) (V : Type) :
    CSt N V ≃ (Fin 5 × Fin (N + 1) × Fin (N + 1) × Fin (N + 1) × Fin (N + 1) × Fin (N + 1) ×
      Fin (N + 1) × Fin (N + 1) × V × Bool) where
  toFun s := (s.pc, s.i, s.r, s.r2, s.v, s.c, s.u, s.j, s.w, s.fnd)
  invFun t := ⟨t.1, t.2.1, t.2.2.1, t.2.2.2.1, t.2.2.2.2.1, t.2.2.2.2.2.1, t.2.2.2.2.2.2.1,
    t.2.2.2.2.2.2.2.1, t.2.2.2.2.2.2.2.2.1, t.2.2.2.2.2.2.2.2.2⟩
  left_inv s := by cases s; rfl
  right_inv t := rfl

instance (N : ℕ) (V : Type) [Fintype V] : Fintype (CSt N V) :=
  Fintype.ofEquiv _ (CSt.equivProd N V).symm

lemma card_CSt (N : ℕ) (V : Type) [Fintype V] :
    Fintype.card (CSt N V) = 10 * (N + 1) ^ 7 * Fintype.card V := by
  rw [Fintype.card_congr (CSt.equivProd N V)]
  simp [Fintype.card_prod]
  ring

/-! ### The transitions of the complementing program -/

variable (P : Setup n)

/-- The transitions of the inner loop that finish a guessed path, apart from the update
of the `fnd` flag (which involves an edge query). -/
def Base9 (s t : CSt P.N P.V) : Prop :=
  s.pc = 3 ∧ s.w = P.vAt (s.u : ℕ) ∧ ¬ P.acc s.w ∧ (s.u : ℕ) < P.N ∧ (s.c : ℕ) < P.N ∧
    ∃ (c' u' : Fin (P.N + 1)) (f' : Bool),
      (c' : ℕ) = (s.c : ℕ) + 1 ∧ (u' : ℕ) = (s.u : ℕ) + 1 ∧
      t = { s with pc := 2, c := c', u := u', fnd := f' }

/-- The transitions extending a guessed path by one edge (apart from the edge query). -/
def Ext (s t : CSt P.N P.V) : Prop :=
  s.pc = 3 ∧ (s.j : ℕ) < (s.i : ℕ) ∧
    ∃ (j' : Fin (P.N + 1)) (w' : P.V), (j' : ℕ) = (s.j : ℕ) + 1 ∧ t = { s with j := j', w := w' }

/-- The transitions that do not query the input. -/
def Uncond (s t : CSt P.N P.V) : Prop :=
  (s.pc = 0 ∧ (s.i : ℕ) = P.N ∧ t = { s with pc := 4 })
  ∨ (s.pc = 0 ∧ (s.i : ℕ) < P.N ∧ t = { s with pc := 1, r2 := 0, v := 0 })
  ∨ (s.pc = 1 ∧ (s.v : ℕ) = P.N ∧ ∃ i' : Fin (P.N + 1), (i' : ℕ) = (s.i : ℕ) + 1 ∧
      t = { s with pc := 0, i := i', r := s.r2 })
  ∨ (s.pc = 1 ∧ (s.v : ℕ) < P.N ∧ t = { s with pc := 2, c := 0, u := 0, fnd := false })
  ∨ (s.pc = 2 ∧ (s.u : ℕ) = P.N ∧ s.c = s.r ∧ ∃ r2' v' : Fin (P.N + 1),
      (r2' : ℕ) = (s.r2 : ℕ) + (if s.fnd then 1 else 0) ∧ (v' : ℕ) = (s.v : ℕ) + 1 ∧
      t = { s with pc := 1, r2 := r2', v := v' })
  ∨ (s.pc = 2 ∧ (s.u : ℕ) < P.N ∧ ∃ u' : Fin (P.N + 1), (u' : ℕ) = (s.u : ℕ) + 1 ∧
      t = { s with u := u' })
  ∨ (s.pc = 2 ∧ (s.u : ℕ) < P.N ∧ t = { s with pc := 3, w := P.st, j := 0 })
  ∨ (Base9 P s t ∧ (s.fnd = true ∨ P.vAt (s.u : ℕ) = P.vAt (s.v : ℕ)) ∧ t.fnd = true)

/-- The transitions taken when the queried edge is present. -/
def CondPos (s t : CSt P.N P.V) : Prop :=
  Ext P s t ∨
    (Base9 P s t ∧ ¬ (s.fnd = true ∨ P.vAt (s.u : ℕ) = P.vAt (s.v : ℕ)) ∧ t.fnd = true)

/-- The transitions taken when the queried edge is absent. -/
def CondNeg (s t : CSt P.N P.V) : Prop :=
  Base9 P s t ∧ ¬ (s.fnd = true ∨ P.vAt (s.u : ℕ) = P.vAt (s.v : ℕ)) ∧ t.fnd = false

/-- The source of the queried edge. -/
def qa (s t : CSt P.N P.V) : P.V := if s.pc = 3 ∧ t.pc = 3 then s.w else P.vAt (s.u : ℕ)

/-- The target of the queried edge. -/
def qb (s t : CSt P.N P.V) : P.V := if s.pc = 3 ∧ t.pc = 3 then t.w else P.vAt (s.v : ℕ)

open Classical in
/-- The guards of the complementing program. -/
noncomputable def cedg (s t : CSt P.N P.V) : Guard n :=
  if Uncond P s t then Guard.always
  else if CondPos P s t then P.edg (qa P s t) (qb P s t)
  else if CondNeg P s t then (P.edg (qa P s t) (qb P s t)).neg
  else Guard.never

/-- The one-step relation of the complementing program on the input `x`. -/
def cstep (x : Fin n → Bool) (s t : CSt P.N P.V) : Prop :=
  Uncond P s t
    ∨ (CondPos P s t ∧ (P.edg (qa P s t) (qb P s t)).eval x = true)
    ∨ (CondNeg P s t ∧ (P.edg (qa P s t) (qb P s t)).eval x = false)

/-- The start state of the complementing program. -/
def cstart : CSt P.N P.V :=
  { pc := 0, i := 0, r := ⟨1, by have := P.hN; omega⟩, r2 := 0, v := 0, c := 0, u := 0, j := 0,
    w := P.st, fnd := false }

lemma Base9_spc {s t : CSt P.N P.V} (h : Base9 P s t) : s.pc = 3 := h.1

lemma Base9_tpc {s t : CSt P.N P.V} (h : Base9 P s t) : t.pc = 2 := by
  obtain ⟨-, -, -, -, -, c', u', f', -, -, rfl⟩ := h
  rfl

lemma Ext_spc {s t : CSt P.N P.V} (h : Ext P s t) : s.pc = 3 := h.1

lemma Ext_tpc {s t : CSt P.N P.V} (h : Ext P s t) : t.pc = 3 := by
  obtain ⟨h1, -, j', w', -, rfl⟩ := h
  exact h1

lemma uncond_not_condPos {s t : CSt P.N P.V} (h : Uncond P s t) : ¬ CondPos P s t := by
  rintro (hE | ⟨hB, hP, -⟩)
  · rcases h with ⟨h1, -⟩ | ⟨h1, -⟩ | ⟨h1, -⟩ | ⟨h1, -⟩ | ⟨h1, -⟩ | ⟨h1, -⟩ | ⟨h1, -⟩ | ⟨hB, -, -⟩
    · rw [Ext_spc P hE] at h1; exact absurd h1 (by decide)
    · rw [Ext_spc P hE] at h1; exact absurd h1 (by decide)
    · rw [Ext_spc P hE] at h1; exact absurd h1 (by decide)
    · rw [Ext_spc P hE] at h1; exact absurd h1 (by decide)
    · rw [Ext_spc P hE] at h1; exact absurd h1 (by decide)
    · rw [Ext_spc P hE] at h1; exact absurd h1 (by decide)
    · rw [Ext_spc P hE] at h1; exact absurd h1 (by decide)
    · have h2 := Base9_tpc P hB
      rw [Ext_tpc P hE] at h2; exact absurd h2 (by decide)
  · rcases h with ⟨h1, -⟩ | ⟨h1, -⟩ | ⟨h1, -⟩ | ⟨h1, -⟩ | ⟨h1, -⟩ | ⟨h1, -⟩ | ⟨h1, -⟩ | ⟨-, hP', -⟩
    · rw [Base9_spc P hB] at h1; exact absurd h1 (by decide)
    · rw [Base9_spc P hB] at h1; exact absurd h1 (by decide)
    · rw [Base9_spc P hB] at h1; exact absurd h1 (by decide)
    · rw [Base9_spc P hB] at h1; exact absurd h1 (by decide)
    · rw [Base9_spc P hB] at h1; exact absurd h1 (by decide)
    · rw [Base9_spc P hB] at h1; exact absurd h1 (by decide)
    · rw [Base9_spc P hB] at h1; exact absurd h1 (by decide)
    · exact hP hP'

lemma uncond_not_condNeg {s t : CSt P.N P.V} (h : Uncond P s t) : ¬ CondNeg P s t := by
  rintro ⟨hB, hP, -⟩
  rcases h with ⟨h1, -⟩ | ⟨h1, -⟩ | ⟨h1, -⟩ | ⟨h1, -⟩ | ⟨h1, -⟩ | ⟨h1, -⟩ | ⟨h1, -⟩ | ⟨-, hP', -⟩
  · rw [Base9_spc P hB] at h1; exact absurd h1 (by decide)
  · rw [Base9_spc P hB] at h1; exact absurd h1 (by decide)
  · rw [Base9_spc P hB] at h1; exact absurd h1 (by decide)
  · rw [Base9_spc P hB] at h1; exact absurd h1 (by decide)
  · rw [Base9_spc P hB] at h1; exact absurd h1 (by decide)
  · rw [Base9_spc P hB] at h1; exact absurd h1 (by decide)
  · rw [Base9_spc P hB] at h1; exact absurd h1 (by decide)
  · exact hP hP'

lemma condPos_not_condNeg {s t : CSt P.N P.V} (h : CondPos P s t) : ¬ CondNeg P s t := by
  rintro ⟨hB, -, hf⟩
  rcases h with hE | ⟨-, -, hf'⟩
  · have h2 := Base9_tpc P hB
    rw [Ext_tpc P hE] at h2; exact absurd h2 (by decide)
  · rw [hf] at hf'; exact absurd hf' (by decide)

lemma cedg_eval (x : Fin n → Bool) (s t : CSt P.N P.V) :
    (cedg P s t).eval x = true ↔ cstep P x s t := by
  classical
  unfold cedg cstep
  split_ifs with h1 h2 h3
  · simp only [Guard.eval_always, true_iff]
    exact Or.inl h1
  · constructor
    · intro hq; exact Or.inr (Or.inl ⟨h2, hq⟩)
    · rintro (hU | ⟨-, hq⟩ | ⟨hN, -⟩)
      · exact absurd hU h1
      · exact hq
      · exact absurd hN (condPos_not_condNeg P h2)
  · rw [Guard.eval_neg]
    constructor
    · intro hq
      refine Or.inr (Or.inr ⟨h3, ?_⟩)
      simpa using hq
    · rintro (hU | ⟨hp, -⟩ | ⟨-, hq⟩)
      · exact absurd hU h1
      · exact absurd hp h2
      · simp [hq]
  · refine iff_of_false (by simp) ?_
    rintro (hU | ⟨hp, -⟩ | ⟨hn, -⟩)
    · exact absurd hU h1
    · exact absurd hp h2
    · exact absurd hn h3

end Compl

end CS

import Mathlib

/-!
# Nondeterministic space-bounded computation

We formalize nondeterministic space-bounded computation by *nondeterministic branching
programs* (NBPs).  An NBP over inputs of length `n` is a finite directed graph whose
vertices are the configurations of the machine, together with a distinguished start
configuration and a set of accepting configurations.  Each potential edge carries a
`Guard`: it is either absent (`never`), always present (`always`), or present exactly
when a single designated bit of the input takes a prescribed value (`bit i b`).  This is
the standard "configuration graph" picture of a space-bounded machine: a machine using
space `s` has `2^{O(s)}` configurations, and a single step of the machine looks at one
bit of the input.

Acceptance is reachability from the start configuration to an accepting configuration.
-/

namespace CS

/-- The condition under which an edge of a nondeterministic branching program is
present: never, always, or exactly when input bit `i` has value `b`. -/
inductive Guard (n : ℕ) : Type
  | never : Guard n
  | always : Guard n
  | bit (i : Fin n) (b : Bool) : Guard n
  deriving DecidableEq

/-- Evaluate a guard on an input. -/
def Guard.eval {n : ℕ} : Guard n → (Fin n → Bool) → Bool
  | .never, _ => false
  | .always, _ => true
  | .bit i b, x => decide (x i = b)

/-- The negation of a guard. -/
def Guard.neg {n : ℕ} : Guard n → Guard n
  | .never => .always
  | .always => .never
  | .bit i b => .bit i (!b)

@[simp] lemma Guard.eval_never {n : ℕ} (x : Fin n → Bool) :
    (Guard.never : Guard n).eval x = false := rfl

@[simp] lemma Guard.eval_always {n : ℕ} (x : Fin n → Bool) :
    (Guard.always : Guard n).eval x = true := rfl

@[simp] lemma Guard.eval_neg {n : ℕ} (g : Guard n) (x : Fin n → Bool) :
    (g.neg).eval x = !(g.eval x) := by
  cases g with
  | never => rfl
  | always => rfl
  | bit i b => cases hb : x i <;> cases b <;> simp [Guard.eval, Guard.neg, hb]

/-- A nondeterministic branching program on inputs of length `n`. -/
structure NBP (n : ℕ) : Type 1 where
  /-- The set of configurations. -/
  V : Type
  /-- Finiteness of the configuration set. -/
  fin : Fintype V
  /-- The initial configuration. -/
  start : V
  /-- The accepting configurations. -/
  accept : V → Prop
  /-- The guard of the edge from one configuration to another. -/
  edges : V → V → Guard n

attribute [instance] NBP.fin

/-- The one-step relation of an NBP on a given input. -/
def NBP.step {n : ℕ} (B : NBP n) (x : Fin n → Bool) : B.V → B.V → Prop :=
  fun a b => (B.edges a b).eval x = true

/-- An NBP accepts an input when some accepting configuration is reachable from the
start configuration. -/
def NBP.Accepts {n : ℕ} (B : NBP n) (x : Fin n → Bool) : Prop :=
  ∃ v, B.accept v ∧ Relation.ReflTransGen (B.step x) B.start v

/-- The number of configurations of an NBP (i.e. `2^space`). -/
def NBP.size {n : ℕ} (B : NBP n) : ℕ := Fintype.card B.V

/-- A language: a predicate on binary strings, indexed by their length. -/
abbrev Language : Type := (n : ℕ) → (Fin n → Bool) → Prop

/-- `InNL L` says that `L` is decided by a family of nondeterministic branching
programs of polynomial size, i.e. by nondeterministic machines running in logarithmic
space (nonuniformly). -/
def InNL (L : Language) : Prop :=
  ∃ c k : ℕ, ∀ n : ℕ, ∃ B : NBP n, B.size ≤ c * (n + 1) ^ k ∧ ∀ x, (B.Accepts x ↔ L n x)

/-- Nondeterministic logarithmic space. -/
def NL : Set Language := {L | InNL L}

/-- The complements of the languages in `NL`. -/
def coNL : Set Language := {L | InNL (fun n x => ¬ L n x)}

end CS

import RequestProject.Basic

/-!
# Bounded reachability levels

For a relation `E` on a finite type `V` and a start vertex `st`, `Rle E st i` is the set
of vertices reachable from `st` by a walk of length at most `i`.  The main result is
that these sets stabilize: every reachable vertex lies in `Rle E st (card V - 1)`.
-/

namespace CS

section
variable {V : Type} (E : V → V → Prop) (st : V)

/-- The set of vertices reachable from `st` in at most `i` steps. -/
def Rle : ℕ → Set V
  | 0 => {st}
  | (i + 1) => Rle i ∪ {z | ∃ y ∈ Rle i, E y z}

@[simp] lemma Rle_zero : Rle E st 0 = {st} := rfl

lemma Rle_succ (i : ℕ) : Rle E st (i + 1) = Rle E st i ∪ {z | ∃ y ∈ Rle E st i, E y z} := rfl

lemma mem_Rle_succ {i : ℕ} {z : V} :
    z ∈ Rle E st (i + 1) ↔ (z ∈ Rle E st i ∨ ∃ y ∈ Rle E st i, E y z) := Iff.rfl

lemma start_mem_Rle (i : ℕ) : st ∈ Rle E st i := by
  induction i with
  | zero => simp
  | succ i ih => exact Or.inl ih

lemma Rle_subset_succ (i : ℕ) : Rle E st i ⊆ Rle E st (i + 1) := fun _ h => Or.inl h

lemma Rle_mono : Monotone (Rle E st) := by
  intro i j hij
  induction hij with
  | refl => exact le_refl _
  | step _ ih => exact ih.trans (Rle_subset_succ E st _)

lemma Rle_subset_reach {i : ℕ} {y : V} (h : y ∈ Rle E st i) :
    Relation.ReflTransGen E st y := by
  induction i generalizing y with
  | zero => cases h; exact Relation.ReflTransGen.refl
  | succ i ih =>
      rcases h with h | ⟨z, hz, hzy⟩
      · exact ih h
      · exact (ih hz).tail hzy

lemma exists_mem_Rle {y : V} (h : Relation.ReflTransGen E st y) :
    ∃ i, y ∈ Rle E st i := by
  induction h with
  | refl => exact ⟨0, rfl⟩
  | tail _ hbc ih =>
      obtain ⟨i, hi⟩ := ih
      exact ⟨i + 1, Or.inr ⟨_, hi, hbc⟩⟩

lemma Rle_stable {i : ℕ} (h : Rle E st (i + 1) = Rle E st i) :
    ∀ j, i ≤ j → Rle E st j = Rle E st i := by
  intro j hj
  induction j with
  | zero => simp [Nat.le_zero.mp hj]
  | succ j ih =>
      rcases Nat.lt_or_ge i (j + 1) with hlt | hge
      · have hij : i ≤ j := Nat.lt_succ_iff.mp hlt
        have hj' : Rle E st j = Rle E st i := ih hij
        rw [Rle_succ, hj']
        rw [Rle_succ] at h
        exact h
      · have : i = j + 1 := le_antisymm hj hge
        subst this; rfl

lemma Rle_ncard_ge [Fintype V] {i : ℕ} (h : ∀ k, k < i → Rle E st k ≠ Rle E st (k + 1)) :
    i + 1 ≤ (Rle E st i).ncard := by
  induction i with
  | zero => simp
  | succ i ih =>
      have hih : i + 1 ≤ (Rle E st i).ncard := ih (fun k hk => h k (Nat.lt_succ_of_lt hk))
      have hss : Rle E st i ⊂ Rle E st (i + 1) :=
        ssubset_of_subset_of_ne (Rle_subset_succ E st i) (h i (Nat.lt_succ_self i))
      have := Set.ncard_lt_ncard hss (Set.toFinite _)
      omega

/-- Every vertex reachable from `st` is reachable by a walk of length at most
`card V - 1`. -/
theorem reach_mem_Rle_card [Fintype V] {y : V} (h : Relation.ReflTransGen E st y) :
    y ∈ Rle E st (Fintype.card V - 1) := by
  classical
  set N := Fintype.card V with hN
  have hNpos : 1 ≤ N := Fintype.card_pos_iff.mpr ⟨st⟩
  have hstab : ∃ i, i ≤ N - 1 ∧ Rle E st (i + 1) = Rle E st i := by
    by_contra hcon
    push_neg at hcon
    have hne : ∀ k, k < N - 1 → Rle E st k ≠ Rle E st (k + 1) := by
      intro k hk hEq
      exact hcon k (le_of_lt hk) hEq.symm
    have hcard : (N - 1) + 1 ≤ (Rle E st (N - 1)).ncard := Rle_ncard_ge E st hne
    have huniv : Rle E st (N - 1) = Set.univ := by
      have hu : (Set.univ : Set V).ncard = N := by
        simp [Set.ncard_univ, Nat.card_eq_fintype_card, ← hN]
      have hle : (Set.univ : Set V).ncard ≤ (Rle E st (N - 1)).ncard := by omega
      exact Set.eq_of_subset_of_ncard_le (Set.subset_univ _) hle (Set.toFinite _)
    have hfix : Rle E st (N - 1 + 1) = Rle E st (N - 1) := by
      refine Set.Subset.antisymm ?_ (Rle_subset_succ E st _)
      rw [huniv]; exact Set.subset_univ _
    exact hcon (N - 1) le_rfl hfix
  obtain ⟨i, hi, hstab⟩ := hstab
  obtain ⟨m, hm⟩ := exists_mem_Rle E st h
  have h1 : Rle E st (max m i) = Rle E st i := Rle_stable E st hstab _ (le_max_right _ _)
  have h2 : y ∈ Rle E st i := h1 ▸ (Rle_mono E st (le_max_left m i) hm)
  exact Rle_mono E st hi h2

end

end CS

import Mathlib
import RequestProject.Basic
import RequestProject.Reach
import RequestProject.Complement

/-!
# Immerman Szelepcsenyi
Category: Frontier Cs
Target: CS.immerman_szelepcsenyi
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

/-!
(The header comment above has to follow the `import` lines: Lean 4 requires `import`
commands to come first in a module.)

`NL` is formalized as the class of languages decided by polynomial-size families of
nondeterministic branching programs — the configuration graphs of nondeterministic
machines using logarithmic work space, where a single step inspects one bit of the
input.  `coNL` is the class of complements of languages in `NL`.  The theorem
`CS.immerman_szelepcsenyi` states `NL = coNL`.

The mathematical content is the explicit inductive counting construction
`CS.NBP.exists_complement`: from any nondeterministic branching program `B` one builds a
nondeterministic branching program of size at most `10 * (B.size + 1) ^ 8` accepting
exactly the inputs rejected by `B`.
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

namespace CS

/-- A polynomial bound on the size of the complementing machine. -/
lemma size_bound (c k S n : ℕ) (h : S ≤ c * (n + 1) ^ k) :
    10 * (S + 1) ^ 8 ≤ (10 * (c + 1) ^ 8) * (n + 1) ^ (k * 8) := by
  have hp : 1 ≤ (n + 1) ^ k := Nat.one_le_pow _ _ (Nat.succ_pos n)
  have h1 : S + 1 ≤ (c + 1) * (n + 1) ^ k := by
    calc S + 1 ≤ c * (n + 1) ^ k + (n + 1) ^ k := by omega
      _ = (c + 1) * (n + 1) ^ k := by ring
  calc 10 * (S + 1) ^ 8 ≤ 10 * ((c + 1) * (n + 1) ^ k) ^ 8 :=
        Nat.mul_le_mul_left _ (Nat.pow_le_pow_left h1 8)
    _ = 10 * (c + 1) ^ 8 * ((n + 1) ^ k) ^ 8 := by rw [mul_pow]; ring
    _ = 10 * (c + 1) ^ 8 * (n + 1) ^ (k * 8) := by rw [← pow_mul]

/-- Nondeterministic logarithmic space is closed under complement. -/
theorem InNL_compl {L : Language} (h : InNL L) : InNL (fun n x => ¬ L n x) := by
  obtain ⟨c, k, h⟩ := h
  refine ⟨10 * (c + 1) ^ 8, k * 8, fun n => ?_⟩
  obtain ⟨B, hsize, hacc⟩ := h n
  obtain ⟨B', hs', ha'⟩ := B.exists_complement
  refine ⟨B', le_trans hs' (size_bound c k B.size n hsize), fun x => ?_⟩
  rw [ha' x, hacc x]

/-- **The Immerman-Szelepcsényi theorem**: nondeterministic space is closed under
complement, `NL = coNL`. -/
theorem immerman_szelepcsenyi : NL = coNL := by
  ext L
  constructor
  · intro hL
    exact InNL_compl hL
  · intro hL
    have h2 : InNL (fun n x => ¬ ¬ L n x) := InNL_compl hL
    have heq : (fun n x => ¬ ¬ L n x) = L := by
      funext n x
      exact propext not_not
    rwa [heq] at h2

end CS

import RequestProject.Basic

/-!
# A sanity check on the model

To confirm that the model of nondeterministic space-bounded computation used here is
not degenerate, we exhibit a small nondeterministic branching program: it guesses an
index `i` and accepts if the `i`-th input bit is `1`, so it accepts exactly the inputs
containing a `1`.  Consequently the language `OR` belongs to `NL`.
-/

namespace CS

namespace OrLang

/-- The three-layer machine deciding `OR`: guess an index, then read that bit. -/
def machine (n : ℕ) : NBP n where
  V := Unit ⊕ Fin n ⊕ Unit
  fin := inferInstance
  start := Sum.inl ()
  accept := fun v => v = Sum.inr (Sum.inr ())
  edges := fun a b =>
    match a, b with
    | Sum.inl (), Sum.inr (Sum.inl _) => Guard.always
    | Sum.inr (Sum.inl i), Sum.inr (Sum.inr ()) => Guard.bit i true
    | _, _ => Guard.never

lemma machine_size (n : ℕ) : (machine n).size = n + 2 := by
  show Fintype.card (Unit ⊕ Fin n ⊕ Unit) = n + 2
  simp
  omega

lemma reach_cases (n : ℕ) (x : Fin n → Bool) (w : Unit ⊕ Fin n ⊕ Unit)
    (hw : Relation.ReflTransGen ((machine n).step x) (Sum.inl ()) w) :
    w = Sum.inl () ∨ (∃ i, w = Sum.inr (Sum.inl i)) ∨ (∃ i, x i = true) := by
  induction hw with
  | refl => exact Or.inl rfl
  | tail _ hbc ih =>
      rcases ih with rfl | ⟨i, rfl⟩ | h
      · rename_i c _
        rcases c with ⟨⟩ | ⟨i | ⟨⟩⟩
        · exact absurd hbc (by simp [machine, NBP.step, Guard.eval])
        · exact Or.inr (Or.inl ⟨i, rfl⟩)
        · exact absurd hbc (by simp [machine, NBP.step, Guard.eval])
      · rename_i c _
        rcases c with ⟨⟩ | ⟨i' | ⟨⟩⟩
        · exact absurd hbc (by simp [machine, NBP.step, Guard.eval])
        · exact absurd hbc (by simp [machine, NBP.step, Guard.eval])
        · refine Or.inr (Or.inr ⟨i, ?_⟩)
          have : (Guard.bit i true).eval x = true := hbc
          simpa [Guard.eval] using this
      · exact Or.inr (Or.inr h)

lemma machine_accepts (n : ℕ) (x : Fin n → Bool) :
    (machine n).Accepts x ↔ ∃ i, x i = true := by
  constructor
  · rintro ⟨v, hv, hreach⟩
    have hv' : v = Sum.inr (Sum.inr ()) := hv
    rcases reach_cases n x v hreach with h | ⟨i, h⟩ | h
    · rw [hv'] at h; exact absurd h (by simp)
    · rw [hv'] at h; exact absurd h (by simp)
    · exact h
  · rintro ⟨i, hi⟩
    refine ⟨Sum.inr (Sum.inr ()), rfl, ?_⟩
    refine Relation.ReflTransGen.head (b := Sum.inr (Sum.inl i)) ?_
      (Relation.ReflTransGen.single ?_)
    · show (Guard.always : Guard n).eval x = true
      rfl
    · show (Guard.bit i true).eval x = true
      simp [Guard.eval, hi]

end OrLang

/-- The language `OR` (some input bit is `1`) lies in `NL`; in particular `NL` is not
a degenerate class. -/
theorem or_mem_NL : (fun n (x : Fin n → Bool) => ∃ i, x i = true) ∈ NL := by
  refine ⟨2, 1, fun n => ⟨OrLang.machine n, ?_, OrLang.machine_accepts n⟩⟩
  rw [OrLang.machine_size]
  simp
  omega

end CS

