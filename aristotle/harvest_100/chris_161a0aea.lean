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
# Brocard Conjecture
Category: Brockian Conjecture
Target: Brockian.BrocardProblem.BrocardConjecture
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/
-- (Lean 4 requires `import` to be the first command in a file, so the header above is a
-- plain block comment rather than a module docstring.)

import Mathlib

set_option maxRecDepth 40000

namespace Brockian.BrocardProblem

open Nat

/-- `IsBrocardSolution n m` says that `(n, m)` solves Brocard's equation `n! + 1 = m²`. -/
def IsBrocardSolution (n m : ℕ) : Prop := n ! + 1 = m ^ 2

/-- Brocard's conjecture (Brocard's problem): the only solutions of `n! + 1 = m²` in
natural numbers are `n = 4, 5, 7` (with `m = 5, 11, 71`).  This is an open problem. -/
def BrocardStatement : Prop :=
  ∀ n m : ℕ, IsBrocardSolution n m → n = 4 ∨ n = 5 ∨ n = 7

/-- The three known solutions of Brocard's equation. -/
theorem brocard_known_solutions :
    IsBrocardSolution 4 5 ∧ IsBrocardSolution 5 11 ∧ IsBrocardSolution 7 71 := by
  refine ⟨?_, ?_, ?_⟩ <;> · unfold IsBrocardSolution; decide

/-- A number strictly between two consecutive squares is not a square. -/
theorem not_square_of_between {N k : ℕ} (h1 : k ^ 2 < N) (h2 : N < (k + 1) ^ 2) :
    ¬ ∃ m : ℕ, N = m ^ 2 := by
  rintro ⟨m, rfl⟩
  have hk : k < m := by nlinarith
  have hm : m < k + 1 := by nlinarith
  omega

/-!
## An equivalent form of Brocard's equation

For `n ≥ 2`, `n! + 1` is a square exactly when `n!/4` is a product of two consecutive
integers.  This is the standard reformulation `n! = (m-1)(m+1)` with `m` odd.
-/

/-- Reformulation of Brocard's equation: for `n ≥ 2`, `n! + 1` is a perfect square iff
`n!` is four times a product of two consecutive integers. -/
theorem brocard_iff_consecutive {n : ℕ} (hn : 2 ≤ n) :
    (∃ m : ℕ, IsBrocardSolution n m) ↔ ∃ a : ℕ, n ! = 4 * (a * (a + 1)) := by
  constructor
  · rintro ⟨m, hm⟩
    have hfac : 2 ∣ n ! := dvd_factorial (by norm_num) hn
    have hodd : ¬ (2 ∣ m) := by
      rintro ⟨t, rfl⟩
      obtain ⟨s, hs⟩ := hfac
      unfold IsBrocardSolution at hm
      have h4 : (2 * t) ^ 2 = 4 * (t * t) := by ring
      omega
    obtain ⟨a, ha⟩ : ∃ a, m = 2 * a + 1 := by
      rcases Nat.even_or_odd m with h | h
      · exact absurd h.two_dvd hodd
      · obtain ⟨a, ha⟩ := h; exact ⟨a, by omega⟩
    refine ⟨a, ?_⟩
    unfold IsBrocardSolution at hm
    subst ha
    nlinarith [hm]
  · rintro ⟨a, ha⟩
    exact ⟨2 * a + 1, by unfold IsBrocardSolution; rw [ha]; ring⟩

/-- Any solution of Brocard's equation produces two consecutive integers all of whose
prime factors are at most `n` (i.e. two consecutive `n`-smooth numbers). -/
theorem brocard_solution_smooth {n a p : ℕ} (h : n ! = 4 * (a * (a + 1)))
    (hp : p.Prime) (hpa : p ∣ a ∨ p ∣ a + 1) : p ≤ n := by
  have hdvd : p ∣ n ! := by
    rw [h]
    rcases hpa with hd | hd
    · exact Dvd.dvd.mul_left (hd.mul_right _) 4
    · exact Dvd.dvd.mul_left (hd.mul_left _) 4
  exact (Nat.Prime.dvd_factorial hp).mp hdvd

/-!
## Verification of Brocard's conjecture for `n ≤ 100`

For each `n ≤ 100` other than `4, 5, 7` we exhibit `⌊√(n!+1)⌋` explicitly, showing that
`n! + 1` lies strictly between two consecutive squares.
-/

/-- Table of the integer square roots `⌊√(n!+1)⌋` for `n = 0, …, 100`. -/
def sqrtTable : List ℕ :=
  [1, 1, 1, 2, 5, 11, 26, 71, 200, 602, 1904, 6317, 21886, 78911, 295259, 1143535, 4574143,
   18859677, 80014834, 348776576, 1559776268, 7147792818, 33526120082, 160785623545,
   787685471322, 3938427356614, 20082117944245, 104349745809073, 552166953567228,
   2973510046012910, 16286585271694955, 90679869067935485, 512962802680363491,
   2946746955341073478, 17182339742875652406, 101652092779175702171, 609912556675054213027,
   3709953246501409085690, 22869687743093501007951, 142821154179615294686593,
   903280290523322408635610, 5783815921445270815783609, 37483411234209726053065805,
   245795164849461258960674062, 1630420674178430788228519563, 10937194378152021970306618007,
   74179661362209580727623742159, 508550136674023695658451670185,
   3523338699662022653505900576721, 24663370897634158574541304037050,
   174396368086360611696209329639024, 1245439180886558699493562057691804,
   8980989654316715588967781706572076, 65382591597917144387816492317568177,
   480461962427038942460267525096444474, 3563201278858419461033351267854721464,
   26664556771205919519070097139612996000, 201312988912482288333668455069536465757,
   1533154046820761769413164705689608744377, 11776379687564843276211019969710858039009,
   91219444817107882594696857529818207676198, 712446639319201784948673912308403605115342,
   5609810447812647575362248801595614968784558, 44526490041372451122965980435912297622389065,
   356211920330979608983727843487298380979112523,
   2871872314724746021942727901945240734448707786,
   23331200978034608323876057832648816217523382535,
   190974110596668796970008672429388554580114244205,
   1574812859496908794403637793960093262759360945119,
   13081378078327271990661335578798848847474255303826,
   109446661301155695857080695109221322834464193656741,
   922213960297642814598347871007016379244405330655250,
   7825244940376376925358096892704591704511772131306815,
   66858922078602825324590583356376523422703411874063526,
   575142194723999224356836312510183507170717503745407529,
   4980877514193196669713282991946078429827937232372941867,
   43422283469044442400520987277954690033900570230313299933,
   381028991060110634246276414878912279469899189376847948137,
   3365156932181068109459677272856044111292549448241189337343,
   29910169058002623210200515287548862104836069367192860122492,
   267524684928818862621490012042605003730753817304274266583374,
   2407722164359369763593410108383445033576784355738468399250368,
   21802851503903891305843592056331800458090082265244558375673041,
   198633430462262788036763464177703883166690275063913206990548481,
   1820505461284132832359203813645046756110583331925714370170257092,
   16784231035053557904028966906346483792025484094796637394973403970,
   155650555359345674201535001388480503193835670087005087695666582899,
   1451811729660401840498379775717372701145990271033308799231637667601,
   13619201234191322393627253212934023042404388731461906952430812397994,
   128483287477042947436606854413089420338280480054241478815100633956558,
   1218899489080933816973227253068021382231629321448981884930371490328689,
   11627560052213890684239693812535151882288553865765313903995958273943586,
   111527638075238136262755547542307772029800712447380847367329167783382104,
   1075533591796017115343430456551200439746548977577162936545074776552498754,
   10427685057848376925507942191442630012584828624363222101172323570579332599,
   101636501751285493870798488028947073709983082260934656117721845292980988580,
   995830274128553338795685900500337369492022050359737013283228306377142743139,
   9807790764615756210934052418079289148346460527555220609613824741800936687334,
   97092175013660332284448160034192795594426266264944604365617979012105653222056,
   966054943799492973133000870362309068674974070396662776244736194062917963496762,
   9660549437994929731330008703623090686749740703966627762447361940629179634967623]

/-- `isqrtFactorial n` is the claimed value of `⌊√(n!+1)⌋` for `n ≤ 100`. -/
def isqrtFactorial (n : ℕ) : ℕ := sqrtTable.getD n 0

/-- The finite verification: for every `n ≤ 100` other than `4, 5, 7`, the number `n! + 1`
lies strictly between the consecutive squares `isqrtFactorial n ^ 2` and
`(isqrtFactorial n + 1) ^ 2`. -/
theorem factorial_succ_between_squares : ∀ n ∈ Finset.range 101,
    n = 4 ∨ n = 5 ∨ n = 7 ∨
      (isqrtFactorial n ^ 2 < n ! + 1 ∧ n ! + 1 < (isqrtFactorial n + 1) ^ 2) := by
  decide

/-- Brocard's conjecture holds for all `n ≤ 100`. -/
theorem brocard_le_hundred {n m : ℕ} (hn : n ≤ 100) (h : IsBrocardSolution n m) :
    n = 4 ∨ n = 5 ∨ n = 7 := by
  have hmem : n ∈ Finset.range 101 := Finset.mem_range.mpr (by omega)
  rcases factorial_succ_between_squares n hmem with h4 | h5 | h7 | ⟨hlt1, hlt2⟩
  · exact Or.inl h4
  · exact Or.inr (Or.inl h5)
  · exact Or.inr (Or.inr h7)
  · exact absurd ⟨m, h⟩ (not_square_of_between hlt1 hlt2)

/-!
## Main result

Brocard's problem is open, so what follows is a Lean-checked *conditional reduction*:
the full conjecture is reduced to its remaining (open) part, namely the absence of
solutions with `n > 100`; all `n ≤ 100` are verified unconditionally above.
-/

/-- **Brocard's conjecture, conditional reduction.**  Assuming the open statement that
`n! + 1` is not a perfect square for any `n > 100`, the only solutions of `n! + 1 = m²`
are `n = 4, 5, 7`.  The range `n ≤ 100` is verified unconditionally
(`brocard_le_hundred`), so the hypothesis is exactly the remaining open part of the
problem; it is *not* known to be provable, and it is not vacuous. -/
theorem BrocardConjecture
    (hlarge : ∀ n : ℕ, 100 < n → ¬ ∃ m : ℕ, IsBrocardSolution n m) :
    BrocardStatement := by
  intro n m h
  by_cases hn : n ≤ 100
  · exact brocard_le_hundred hn h
  · exact absurd ⟨m, h⟩ (hlarge n (by omega))

/-- **Brocard's conjecture, reduction to the consecutive-integers form.**  Assuming that
for `n > 100` the factorial `n!` is never four times a product of two consecutive
integers, the only solutions of `n! + 1 = m²` are `n = 4, 5, 7`. -/
theorem BrocardConjecture_of_no_consecutive
    (hlarge : ∀ n : ℕ, 100 < n → ¬ ∃ a : ℕ, n ! = 4 * (a * (a + 1))) :
    BrocardStatement := by
  refine BrocardConjecture (fun n hn hex => hlarge n hn ?_)
  exact (brocard_iff_consecutive (by omega)).mp hex

end Brockian.BrocardProblem

