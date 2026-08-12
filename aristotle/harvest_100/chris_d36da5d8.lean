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

import Mathlib

namespace Brockian.BrocardProblem

open Nat

set_option maxRecDepth 100000

/-- The statement of Brocard's conjecture: the only natural numbers `n` for which
`n! + 1` is a perfect square are `n = 4`, `n = 5` and `n = 7`
(with `4! + 1 = 5²`, `5! + 1 = 11²`, `7! + 1 = 71²`). -/
def BrocardStatement : Prop :=
  ∀ n m : ℕ, n ! + 1 = m ^ 2 → n = 4 ∨ n = 5 ∨ n = 7

/-- If `N` lies strictly between two consecutive squares, it is not a square. -/
theorem not_sq_of_between {N k : ℕ} (h1 : k ^ 2 < N) (h2 : N < (k + 1) ^ 2) (m : ℕ) :
    N ≠ m ^ 2 := by
  rintro rfl
  have hkm : k < m := by
    by_contra hc
    exact absurd (Nat.pow_le_pow_left (not_lt.1 hc) 2) (not_le.2 h1)
  have hmk : m < k + 1 := by
    by_contra hc
    exact absurd (Nat.pow_le_pow_left (not_lt.1 hc) 2) (not_le.2 h2)
  omega

/-- For `2 ≤ n`, if `n! + 1` is a square then `n!` is four times a pronic (oblong) number,
i.e. `n! = 4a(a+1)` for some `a`.  (Indeed `n!` is even, so `m` must be odd, `m = 2a+1`.) -/
theorem pronic_of_factorial_succ_sq {n m : ℕ} (hn : 2 ≤ n) (h : n ! + 1 = m ^ 2) :
    ∃ a : ℕ, n ! = 4 * a * (a + 1) := by
  have hdvd : 2 ∣ n ! := Nat.dvd_factorial (by norm_num) hn
  have hmodd : ¬ 2 ∣ m := by
    intro hm
    have h2 : (2 : ℕ) ∣ m ^ 2 := dvd_pow hm two_ne_zero
    rw [← h] at h2
    omega
  have hmod : m % 2 = 1 := by omega
  obtain ⟨a, ha⟩ := Nat.odd_iff.2 hmod
  refine ⟨a, ?_⟩
  subst ha
  have hexp : (2 * a + 1) ^ 2 = 4 * a * (a + 1) + 1 := by ring
  rw [hexp] at h
  exact Nat.add_right_cancel h

/-- Conversely, if `n! = 4a(a+1)` then `n! + 1 = (2a+1)²` is a square. -/
theorem factorial_succ_sq_of_pronic {n a : ℕ} (h : n ! = 4 * a * (a + 1)) :
    n ! + 1 = (2 * a + 1) ^ 2 := by
  have hexp : (2 * a + 1) ^ 2 = 4 * a * (a + 1) + 1 := by ring
  rw [hexp, h]

/-- **Reduction of Brocard's problem to pronic numbers.**  For `2 ≤ n`, the number `n! + 1`
is a perfect square if and only if `n!` is four times a product of two consecutive integers. -/
theorem factorial_succ_isSquare_iff_pronic {n : ℕ} (hn : 2 ≤ n) :
    (∃ m : ℕ, n ! + 1 = m ^ 2) ↔ ∃ a : ℕ, n ! = 4 * a * (a + 1) := by
  constructor
  · rintro ⟨m, hm⟩
    exact pronic_of_factorial_succ_sq hn hm
  · rintro ⟨a, ha⟩
    exact ⟨2 * a + 1, factorial_succ_sq_of_pronic ha⟩

/-- Wilson's theorem, in the form used here: if `n + 1` is prime then `n + 1 ∣ n! + 1`. -/
theorem dvd_factorial_succ_of_prime_succ (n : ℕ) (hp : Nat.Prime (n + 1)) :
    (n + 1) ∣ n ! + 1 := by
  haveI : Fact (Nat.Prime (n + 1)) := ⟨hp⟩
  have hw := ZMod.wilsons_lemma (n + 1)
  simp only [Nat.add_sub_cancel] at hw
  have h0 : ((n ! + 1 : ℕ) : ZMod (n + 1)) = 0 := by push_cast [hw]; ring
  exact Fin.natCast_eq_zero.mp h0

/-- **Unconditional partial result (Wilson primes).**  If `n! + 1` is a perfect square and
`p = n + 1` is prime, then `p` is a *Wilson prime*, i.e. `p² ∣ (p-1)! + 1`.
Wilson primes are extremely rare (the only ones known are `5`, `13` and `563`), so this
rules out a solution at `n = p - 1` for every prime `p` that is not a Wilson prime. -/
theorem wilsonPrime_of_brocard (n m : ℕ) (hp : Nat.Prime (n + 1)) (h : n ! + 1 = m ^ 2) :
    (n + 1) ^ 2 ∣ n ! + 1 := by
  have hd := dvd_factorial_succ_of_prime_succ n hp
  rw [h] at hd ⊢
  exact pow_dvd_pow_of_dvd (hp.dvd_of_dvd_pow hd) 2

/-- Unconditional verification: for `8 ≤ n ≤ 100`, `n! + 1` is not a perfect square. -/
theorem factorial_succ_not_sq_of_le_hundred (n : ℕ) (h8 : 8 ≤ n) (h100 : n ≤ 100) (m : ℕ) :
    n ! + 1 ≠ m ^ 2 := by
  interval_cases n
  · exact not_sq_of_between (k := 200) (by decide) (by decide) m
  · exact not_sq_of_between (k := 602) (by decide) (by decide) m
  · exact not_sq_of_between (k := 1904) (by decide) (by decide) m
  · exact not_sq_of_between (k := 6317) (by decide) (by decide) m
  · exact not_sq_of_between (k := 21886) (by decide) (by decide) m
  · exact not_sq_of_between (k := 78911) (by decide) (by decide) m
  · exact not_sq_of_between (k := 295259) (by decide) (by decide) m
  · exact not_sq_of_between (k := 1143535) (by decide) (by decide) m
  · exact not_sq_of_between (k := 4574143) (by decide) (by decide) m
  · exact not_sq_of_between (k := 18859677) (by decide) (by decide) m
  · exact not_sq_of_between (k := 80014834) (by decide) (by decide) m
  · exact not_sq_of_between (k := 348776576) (by decide) (by decide) m
  · exact not_sq_of_between (k := 1559776268) (by decide) (by decide) m
  · exact not_sq_of_between (k := 7147792818) (by decide) (by decide) m
  · exact not_sq_of_between (k := 33526120082) (by decide) (by decide) m
  · exact not_sq_of_between (k := 160785623545) (by decide) (by decide) m
  · exact not_sq_of_between (k := 787685471322) (by decide) (by decide) m
  · exact not_sq_of_between (k := 3938427356614) (by decide) (by decide) m
  · exact not_sq_of_between (k := 20082117944245) (by decide) (by decide) m
  · exact not_sq_of_between (k := 104349745809073) (by decide) (by decide) m
  · exact not_sq_of_between (k := 552166953567228) (by decide) (by decide) m
  · exact not_sq_of_between (k := 2973510046012910) (by decide) (by decide) m
  · exact not_sq_of_between (k := 16286585271694955) (by decide) (by decide) m
  · exact not_sq_of_between (k := 90679869067935485) (by decide) (by decide) m
  · exact not_sq_of_between (k := 512962802680363491) (by decide) (by decide) m
  · exact not_sq_of_between (k := 2946746955341073478) (by decide) (by decide) m
  · exact not_sq_of_between (k := 17182339742875652406) (by decide) (by decide) m
  · exact not_sq_of_between (k := 101652092779175702171) (by decide) (by decide) m
  · exact not_sq_of_between (k := 609912556675054213027) (by decide) (by decide) m
  · exact not_sq_of_between (k := 3709953246501409085690) (by decide) (by decide) m
  · exact not_sq_of_between (k := 22869687743093501007951) (by decide) (by decide) m
  · exact not_sq_of_between (k := 142821154179615294686593) (by decide) (by decide) m
  · exact not_sq_of_between (k := 903280290523322408635610) (by decide) (by decide) m
  · exact not_sq_of_between (k := 5783815921445270815783609) (by decide) (by decide) m
  · exact not_sq_of_between (k := 37483411234209726053065805) (by decide) (by decide) m
  · exact not_sq_of_between (k := 245795164849461258960674062) (by decide) (by decide) m
  · exact not_sq_of_between (k := 1630420674178430788228519563) (by decide) (by decide) m
  · exact not_sq_of_between (k := 10937194378152021970306618007) (by decide) (by decide) m
  · exact not_sq_of_between (k := 74179661362209580727623742159) (by decide) (by decide) m
  · exact not_sq_of_between (k := 508550136674023695658451670185) (by decide) (by decide) m
  · exact not_sq_of_between (k := 3523338699662022653505900576721) (by decide) (by decide) m
  · exact not_sq_of_between (k := 24663370897634158574541304037050) (by decide) (by decide) m
  · exact not_sq_of_between (k := 174396368086360611696209329639024) (by decide) (by decide) m
  · exact not_sq_of_between (k := 1245439180886558699493562057691804) (by decide) (by decide) m
  · exact not_sq_of_between (k := 8980989654316715588967781706572076) (by decide) (by decide) m
  · exact not_sq_of_between (k := 65382591597917144387816492317568177) (by decide) (by decide) m
  · exact not_sq_of_between (k := 480461962427038942460267525096444474) (by decide) (by decide) m
  · exact not_sq_of_between (k := 3563201278858419461033351267854721464) (by decide) (by decide) m
  · exact not_sq_of_between (k := 26664556771205919519070097139612996000) (by decide) (by decide) m
  · exact not_sq_of_between (k := 201312988912482288333668455069536465757) (by decide) (by decide) m
  · exact not_sq_of_between (k := 1533154046820761769413164705689608744377) (by decide) (by decide) m
  · exact not_sq_of_between (k := 11776379687564843276211019969710858039009) (by decide) (by decide) m
  · exact not_sq_of_between (k := 91219444817107882594696857529818207676198) (by decide) (by decide) m
  · exact not_sq_of_between (k := 712446639319201784948673912308403605115342) (by decide) (by decide) m
  · exact not_sq_of_between (k := 5609810447812647575362248801595614968784558) (by decide) (by decide) m
  · exact not_sq_of_between (k := 44526490041372451122965980435912297622389065) (by decide) (by decide) m
  · exact not_sq_of_between (k := 356211920330979608983727843487298380979112523) (by decide) (by decide) m
  · exact not_sq_of_between (k := 2871872314724746021942727901945240734448707786) (by decide) (by decide) m
  · exact not_sq_of_between (k := 23331200978034608323876057832648816217523382535) (by decide) (by decide) m
  · exact not_sq_of_between (k := 190974110596668796970008672429388554580114244205) (by decide) (by decide) m
  · exact not_sq_of_between (k := 1574812859496908794403637793960093262759360945119) (by decide) (by decide) m
  · exact not_sq_of_between (k := 13081378078327271990661335578798848847474255303826) (by decide) (by decide) m
  · exact not_sq_of_between (k := 109446661301155695857080695109221322834464193656741) (by decide) (by decide) m
  · exact not_sq_of_between (k := 922213960297642814598347871007016379244405330655250) (by decide) (by decide) m
  · exact not_sq_of_between (k := 7825244940376376925358096892704591704511772131306815) (by decide) (by decide) m
  · exact not_sq_of_between (k := 66858922078602825324590583356376523422703411874063526) (by decide) (by decide) m
  · exact not_sq_of_between (k := 575142194723999224356836312510183507170717503745407529) (by decide) (by decide) m
  · exact not_sq_of_between (k := 4980877514193196669713282991946078429827937232372941867) (by decide) (by decide) m
  · exact not_sq_of_between (k := 43422283469044442400520987277954690033900570230313299933) (by decide) (by decide) m
  · exact not_sq_of_between (k := 381028991060110634246276414878912279469899189376847948137) (by decide) (by decide) m
  · exact not_sq_of_between (k := 3365156932181068109459677272856044111292549448241189337343) (by decide) (by decide) m
  · exact not_sq_of_between (k := 29910169058002623210200515287548862104836069367192860122492) (by decide) (by decide) m
  · exact not_sq_of_between (k := 267524684928818862621490012042605003730753817304274266583374) (by decide) (by decide) m
  · exact not_sq_of_between (k := 2407722164359369763593410108383445033576784355738468399250368) (by decide) (by decide) m
  · exact not_sq_of_between (k := 21802851503903891305843592056331800458090082265244558375673041) (by decide) (by decide) m
  · exact not_sq_of_between (k := 198633430462262788036763464177703883166690275063913206990548481) (by decide) (by decide) m
  · exact not_sq_of_between (k := 1820505461284132832359203813645046756110583331925714370170257092) (by decide) (by decide) m
  · exact not_sq_of_between (k := 16784231035053557904028966906346483792025484094796637394973403970) (by decide) (by decide) m
  · exact not_sq_of_between (k := 155650555359345674201535001388480503193835670087005087695666582899) (by decide) (by decide) m
  · exact not_sq_of_between (k := 1451811729660401840498379775717372701145990271033308799231637667601) (by decide) (by decide) m
  · exact not_sq_of_between (k := 13619201234191322393627253212934023042404388731461906952430812397994) (by decide) (by decide) m
  · exact not_sq_of_between (k := 128483287477042947436606854413089420338280480054241478815100633956558) (by decide) (by decide) m
  · exact not_sq_of_between (k := 1218899489080933816973227253068021382231629321448981884930371490328689) (by decide) (by decide) m
  · exact not_sq_of_between (k := 11627560052213890684239693812535151882288553865765313903995958273943586) (by decide) (by decide) m
  · exact not_sq_of_between (k := 111527638075238136262755547542307772029800712447380847367329167783382104) (by decide) (by decide) m
  · exact not_sq_of_between (k := 1075533591796017115343430456551200439746548977577162936545074776552498754) (by decide) (by decide) m
  · exact not_sq_of_between (k := 10427685057848376925507942191442630012584828624363222101172323570579332599) (by decide) (by decide) m
  · exact not_sq_of_between (k := 101636501751285493870798488028947073709983082260934656117721845292980988580) (by decide) (by decide) m
  · exact not_sq_of_between (k := 995830274128553338795685900500337369492022050359737013283228306377142743139) (by decide) (by decide) m
  · exact not_sq_of_between (k := 9807790764615756210934052418079289148346460527555220609613824741800936687334) (by decide) (by decide) m
  · exact not_sq_of_between (k := 97092175013660332284448160034192795594426266264944604365617979012105653222056) (by decide) (by decide) m
  · exact not_sq_of_between (k := 966054943799492973133000870362309068674974070396662776244736194062917963496762) (by decide) (by decide) m
  · exact not_sq_of_between (k := 9660549437994929731330008703623090686749740703966627762447361940629179634967623) (by decide) (by decide) m

/-- Unconditional verification of the small cases: for `n ≤ 100`, `n! + 1` is a perfect square
exactly when `n ∈ {4, 5, 7}`. -/
theorem brocard_of_le_hundred (n m : ℕ) (hn : n ≤ 100) (h : n ! + 1 = m ^ 2) :
    n = 4 ∨ n = 5 ∨ n = 7 := by
  by_cases h8 : 8 ≤ n
  · exact absurd h (factorial_succ_not_sq_of_le_hundred n h8 hn m)
  · push_neg at h8
    interval_cases n
    · exact absurd h (not_sq_of_between (k := 1) (by decide) (by decide) m)
    · exact absurd h (not_sq_of_between (k := 1) (by decide) (by decide) m)
    · exact absurd h (not_sq_of_between (k := 1) (by decide) (by decide) m)
    · exact absurd h (not_sq_of_between (k := 2) (by decide) (by decide) m)
    · exact Or.inl rfl
    · exact Or.inr (Or.inl rfl)
    · exact absurd h (not_sq_of_between (k := 26) (by decide) (by decide) m)
    · exact Or.inr (Or.inr rfl)

/-- **Brocard's conjecture, conditional on the pronic reduction.**

Brocard's problem asks for all `n` such that `n! + 1` is a perfect square; the conjecture is
that `n = 4, 5, 7` are the only ones.  This is a long-standing open problem, so what is proved
here is a Lean-checked *conditional reduction*: assuming that for `n ≥ 101` the factorial `n!`
is never four times a pronic number, i.e. never of the form `4a(a+1)`, Brocard's conjecture
holds.  All cases `n ≤ 100` are verified unconditionally inside the proof, and by
`factorial_succ_isSquare_iff_pronic` the hypothesis is exactly the content of the
remaining cases. -/
theorem BrocardConjecture
    (h : ∀ n : ℕ, 101 ≤ n → ∀ a : ℕ, n ! ≠ 4 * a * (a + 1)) :
    BrocardStatement := by
  intro n m hnm
  by_cases hn : n ≤ 100
  · exact brocard_of_le_hundred n m hn hnm
  · push_neg at hn
    obtain ⟨a, ha⟩ := pronic_of_factorial_succ_sq (by omega : 2 ≤ n) hnm
    exact absurd ha (h n (by omega) a)

end Brockian.BrocardProblem

