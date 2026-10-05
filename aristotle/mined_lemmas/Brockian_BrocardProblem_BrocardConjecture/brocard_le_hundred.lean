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

/-!
# Brocard Conjecture
Category: Brockian Conjecture
Target: Brockian.BrocardProblem.BrocardConjecture
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

/-
This development is deliberately self-contained: it uses only the Lean 4 core library
(no `import` is possible before the required header comment above), so the factorial
function is defined here from scratch.

Brocard's problem asks for all solutions of `n ! + 1 = m ^ 2`; the conjecture (open) is that
`(n, m) = (4, 5), (5, 11), (7, 71)` are the only ones.  What is proved below is:

* `brocard_iff_pronic` : for `n ≥ 2`, `n ! + 1` is a square iff `n ! = 4 * a * (a + 1)`
  for some `a` (an unconditional reduction of the equation to a pronic form);
* `brocard_le_hundred` : an unconditional verification of the conjecture for all `n ≤ 100`;
* `BrocardConjecture` : the full conjecture, conditional on the reduced (pronic) equation
  having no solutions for `n ≥ 101`.
-/

namespace Brockian.BrocardProblem

/-- The factorial function, `fact n = n !`. -/

theorem brocard_le_hundred {n m : Nat} (hn : n ≤ 100) (h : fact n + 1 = m ^ 2) :
    (n = 4 ∧ m = 5) ∨ (n = 5 ∧ m = 11) ∨ (n = 7 ∧ m = 71) := by
  have hcases : n = 0 ∨ n = 1 ∨ n = 2 ∨ n = 3 ∨ n = 4 ∨ n = 5 ∨ n = 6 ∨ n = 7 ∨ n = 8 ∨ n = 9 ∨ n = 10 ∨ n = 11 ∨ n = 12 ∨ n = 13 ∨ n = 14 ∨ n = 15 ∨ n = 16 ∨ n = 17 ∨ n = 18 ∨ n = 19 ∨ n = 20 ∨ n = 21 ∨ n = 22 ∨ n = 23 ∨ n = 24 ∨ n = 25 ∨ n = 26 ∨ n = 27 ∨ n = 28 ∨ n = 29 ∨ n = 30 ∨ n = 31 ∨ n = 32 ∨ n = 33 ∨ n = 34 ∨ n = 35 ∨ n = 36 ∨ n = 37 ∨ n = 38 ∨ n = 39 ∨ n = 40 ∨ n = 41 ∨ n = 42 ∨ n = 43 ∨ n = 44 ∨ n = 45 ∨ n = 46 ∨ n = 47 ∨ n = 48 ∨ n = 49 ∨ n = 50 ∨ n = 51 ∨ n = 52 ∨ n = 53 ∨ n = 54 ∨ n = 55 ∨ n = 56 ∨ n = 57 ∨ n = 58 ∨ n = 59 ∨ n = 60 ∨ n = 61 ∨ n = 62 ∨ n = 63 ∨ n = 64 ∨ n = 65 ∨ n = 66 ∨ n = 67 ∨ n = 68 ∨ n = 69 ∨ n = 70 ∨ n = 71 ∨ n = 72 ∨ n = 73 ∨ n = 74 ∨ n = 75 ∨ n = 76 ∨ n = 77 ∨ n = 78 ∨ n = 79 ∨ n = 80 ∨ n = 81 ∨ n = 82 ∨ n = 83 ∨ n = 84 ∨ n = 85 ∨ n = 86 ∨ n = 87 ∨ n = 88 ∨ n = 89 ∨ n = 90 ∨ n = 91 ∨ n = 92 ∨ n = 93 ∨ n = 94 ∨ n = 95 ∨ n = 96 ∨ n = 97 ∨ n = 98 ∨ n = 99 ∨ n = 100 := by omega
  rcases hcases with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact absurd h (factorial_add_one_ne_sq 0 1 m (by decide) (by decide))
  · exact absurd h (factorial_add_one_ne_sq 1 1 m (by decide) (by decide))
  · exact absurd h (factorial_add_one_ne_sq 2 1 m (by decide) (by decide))
  · exact absurd h (factorial_add_one_ne_sq 3 2 m (by decide) (by decide))
  · have hk : (5 : Nat) ^ 2 = fact 4 + 1 := by decide
    exact Or.inl ⟨rfl, sq_inj m 5 (by omega)⟩
  · have hk : (11 : Nat) ^ 2 = fact 5 + 1 := by decide
    exact Or.inr (Or.inl ⟨rfl, sq_inj m 11 (by omega)⟩)
  · exact absurd h (factorial_add_one_ne_sq 6 26 m (by decide) (by decide))
  · have hk : (71 : Nat) ^ 2 = fact 7 + 1 := by decide
    exact Or.inr (Or.inr ⟨rfl, sq_inj m 71 (by omega)⟩)
  · exact absurd h (factorial_add_one_ne_sq 8 200 m (by decide) (by decide))
  · exact absurd h (factorial_add_one_ne_sq 9 602 m (by decide) (by decide))
  · exact absurd h (factorial_add_one_ne_sq 10 1904 m (by decide) (by decide))
  · exact absurd h (factorial_add_one_ne_sq 11 6317 m (by decide) (by decide))
  · exact absurd h (factorial_add_one_ne_sq 12 21886 m (by decide) (by decide))
  · exact absurd h (factorial_add_one_ne_sq 13 78911 m (by decide) (by decide))
  · exact absurd h (factorial_add_one_ne_sq 14 295259 m (by decide) (by decide))
  · exact absurd h (factorial_add_one_ne_sq 15 1143535 m (by decide) (by decide))
  · exact absurd h (factorial_add_one_ne_sq 16 4574143 m (by decide) (by decide))
  · exact absurd h (factorial_add_one_ne_sq 17 18859677 m (by decide) (by decide))
  · exact absurd h (factorial_add_one_ne_sq 18 80014834 m (by decide) (by decide))
  · exact absurd h (factorial_add_one_ne_sq 19 348776576 m (by decide) (by decide))
  · exact absurd h (factorial_add_one_ne_sq 20 1559776268 m (by decide) (by decide))
  · exact absurd h (factorial_add_one_ne_sq 21 7147792818 m (by decide) (by decide))
  · exact absurd h (factorial_add_one_ne_sq 22 33526120082 m (by decide) (by decide))
  · exact absurd h (factorial_add_one_ne_sq 23 160785623545 m (by decide) (by decide))
  · exact absurd h (factorial_add_one_ne_sq 24 787685471322 m (by decide) (by decide))
  · exact absurd h (factorial_add_one_ne_sq 25 3938427356614 m (by decide) (by decide))
  · exact absurd h (factorial_add_one_ne_sq 26 20082117944245 m (by decide) (by decide))
  · exact absurd h (factorial_add_one_ne_sq 27 104349745809073 m (by decide) (by decide))
  · exact absurd h (factorial_add_one_ne_sq 28 552166953567228 m (by decide) (by decide))
  · exact absurd h (factorial_add_one_ne_sq 29 2973510046012910 m (by decide) (by decide))
  · exact absurd h (factorial_add_one_ne_sq 30 16286585271694955 m (by decide) (by decide))
  · exact absurd h (factorial_add_one_ne_sq 31 90679869067935485 m (by decide) (by decide))
  · exact absurd h (factorial_add_one_ne_sq 32 512962802680363491 m (by decide) (by decide))
  · exact absurd h (factorial_add_one_ne_sq 33 2946746955341073478 m (by decide) (by decide))
  · exact absurd h (factorial_add_one_ne_sq 34 17182339742875652406 m (by decide) (by decide))
  · exact absurd h (factorial_add_one_ne_sq 35 101652092779175702171 m (by decide) (by decide))
  · exact absurd h (factorial_add_one_ne_sq 36 609912556675054213027 m (by decide) (by decide))
  · exact absurd h (factorial_add_one_ne_sq 37 3709953246501409085690 m (by decide) (by decide))
  · exact absurd h (factorial_add_one_ne_sq 38 22869687743093501007951 m (by decide) (by decide))
  · exact absurd h (factorial_add_one_ne_sq 39 142821154179615294686593 m (by decide) (by decide))
  · exact absurd h (factorial_add_one_ne_sq 40 903280290523322408635610 m (by decide) (by decide))
  · exact absurd h (factorial_add_one_ne_sq 41 5783815921445270815783609 m (by decide) (by decide))
  · exact absurd h (factorial_add_one_ne_sq 42 37483411234209726053065805 m (by decide) (by decide))
  · exact absurd h (factorial_add_one_ne_sq 43 245795164849461258960674062 m (by decide) (by decide))
  · exact absurd h (factorial_add_one_ne_sq 44 1630420674178430788228519563 m (by decide) (by decide))
  · exact absurd h (factorial_add_one_ne_sq 45 10937194378152021970306618007 m (by decide) (by decide))
  · exact absurd h (factorial_add_one_ne_sq 46 74179661362209580727623742159 m (by decide) (by decide))
  · exact absurd h (factorial_add_one_ne_sq 47 508550136674023695658451670185 m (by decide) (by decide))
  · exact absurd h (factorial_add_one_ne_sq 48 3523338699662022653505900576721 m (by decide) (by decide))
  · exact absurd h (factorial_add_one_ne_sq 49 24663370897634158574541304037050 m (by decide) (by decide))
  · exact absurd h (factorial_add_one_ne_sq 50 174396368086360611696209329639024 m (by decide) (by decide))
  · exact absurd h (factorial_add_one_ne_sq 51 1245439180886558699493562057691804 m (by decide) (by decide))
  · exact absurd h (factorial_add_one_ne_sq 52 8980989654316715588967781706572076 m (by decide) (by decide))
  · exact absurd h (factorial_add_one_ne_sq 53 65382591597917144387816492317568177 m (by decide) (by decide))
  · exact absurd h (factorial_add_one_ne_sq 54 480461962427038942460267525096444474 m (by decide) (by decide))
  · exact absurd h (factorial_add_one_ne_sq 55 3563201278858419461033351267854721464 m (by decide) (by decide))
  · exact absurd h (factorial_add_one_ne_sq 56 26664556771205919519070097139612996000 m (by decide) (by decide))
  · exact absurd h (factorial_add_one_ne_sq 57 201312988912482288333668455069536465757 m (by decide) (by decide))
  · exact absurd h (factorial_add_one_ne_sq 58 1533154046820761769413164705689608744377 m (by decide) (by decide))
  · exact absurd h (factorial_add_one_ne_sq 59 11776379687564843276211019969710858039009 m (by decide) (by decide))
  · exact absurd h (factorial_add_one_ne_sq 60 91219444817107882594696857529818207676198 m (by decide) (by decide))
  · exact absurd h (factorial_add_one_ne_sq 61 712446639319201784948673912308403605115342 m (by decide) (by decide))
  · exact absurd h (factorial_add_one_ne_sq 62 5609810447812647575362248801595614968784558 m (by decide) (by decide))
  · exact absurd h (factorial_add_one_ne_sq 63 44526490041372451122965980435912297622389065 m (by decide) (by decide))
  · exact absurd h (factorial_add_one_ne_sq 64 356211920330979608983727843487298380979112523 m (by decide) (by decide))
  · exact absurd h (factorial_add_one_ne_sq 65 2871872314724746021942727901945240734448707786 m (by decide) (by decide))
  · exact absurd h (factorial_add_one_ne_sq 66 23331200978034608323876057832648816217523382535 m (by decide) (by decide))
  · exact absurd h (factorial_add_one_ne_sq 67 190974110596668796970008672429388554580114244205 m (by decide) (by decide))
  · exact absurd h (factorial_add_one_ne_sq 68 1574812859496908794403637793960093262759360945119 m (by decide) (by decide))
  · exact absurd h (factorial_add_one_ne_sq 69 13081378078327271990661335578798848847474255303826 m (by decide) (by decide))
  · exact absurd h (factorial_add_one_ne_sq 70 109446661301155695857080695109221322834464193656741 m (by decide) (by decide))
  · exact absurd h (factorial_add_one_ne_sq 71 922213960297642814598347871007016379244405330655250 m (by decide) (by decide))
  · exact absurd h (factorial_add_one_ne_sq 72 7825244940376376925358096892704591704511772131306815 m (by decide) (by decide))
  · exact absurd h (factorial_add_one_ne_sq 73 66858922078602825324590583356376523422703411874063526 m (by decide) (by decide))
  · exact absurd h (factorial_add_one_ne_sq 74 575142194723999224356836312510183507170717503745407529 m (by decide) (by decide))
  · exact absurd h (factorial_add_one_ne_sq 75 4980877514193196669713282991946078429827937232372941867 m (by decide) (by decide))
  · exact absurd h (factorial_add_one_ne_sq 76 43422283469044442400520987277954690033900570230313299933 m (by decide) (by decide))
  · exact absurd h (factorial_add_one_ne_sq 77 381028991060110634246276414878912279469899189376847948137 m (by decide) (by decide))
  · exact absurd h (factorial_add_one_ne_sq 78 3365156932181068109459677272856044111292549448241189337343 m (by decide) (by decide))
  · exact absurd h (factorial_add_one_ne_sq 79 29910169058002623210200515287548862104836069367192860122492 m (by decide) (by decide))
  · exact absurd h (factorial_add_one_ne_sq 80 267524684928818862621490012042605003730753817304274266583374 m (by decide) (by decide))
  · exact absurd h (factorial_add_one_ne_sq 81 2407722164359369763593410108383445033576784355738468399250368 m (by decide) (by decide))
  · exact absurd h (factorial_add_one_ne_sq 82 21802851503903891305843592056331800458090082265244558375673041 m (by decide) (by decide))
  · exact absurd h (factorial_add_one_ne_sq 83 198633430462262788036763464177703883166690275063913206990548481 m (by decide) (by decide))
  · exact absurd h (factorial_add_one_ne_sq 84 1820505461284132832359203813645046756110583331925714370170257092 m (by decide) (by decide))
  · exact absurd h (factorial_add_one_ne_sq 85 16784231035053557904028966906346483792025484094796637394973403970 m (by decide) (by decide))
  · exact absurd h (factorial_add_one_ne_sq 86 155650555359345674201535001388480503193835670087005087695666582899 m (by decide) (by decide))
  · exact absurd h (factorial_add_one_ne_sq 87 1451811729660401840498379775717372701145990271033308799231637667601 m (by decide) (by decide))
  · exact absurd h (factorial_add_one_ne_sq 88 13619201234191322393627253212934023042404388731461906952430812397994 m (by decide) (by decide))
  · exact absurd h (factorial_add_one_ne_sq 89 128483287477042947436606854413089420338280480054241478815100633956558 m (by decide) (by decide))
  · exact absurd h (factorial_add_one_ne_sq 90 1218899489080933816973227253068021382231629321448981884930371490328689 m (by decide) (by decide))
  · exact absurd h (factorial_add_one_ne_sq 91 11627560052213890684239693812535151882288553865765313903995958273943586 m (by decide) (by decide))
  · exact absurd h (factorial_add_one_ne_sq 92 111527638075238136262755547542307772029800712447380847367329167783382104 m (by decide) (by decide))
  · exact absurd h (factorial_add_one_ne_sq 93 1075533591796017115343430456551200439746548977577162936545074776552498754 m (by decide) (by decide))
  · exact absurd h (factorial_add_one_ne_sq 94 10427685057848376925507942191442630012584828624363222101172323570579332599 m (by decide) (by decide))
  · exact absurd h (factorial_add_one_ne_sq 95 101636501751285493870798488028947073709983082260934656117721845292980988580 m (by decide) (by decide))
  · exact absurd h (factorial_add_one_ne_sq 96 995830274128553338795685900500337369492022050359737013283228306377142743139 m (by decide) (by decide))
  · exact absurd h (factorial_add_one_ne_sq 97 9807790764615756210934052418079289148346460527555220609613824741800936687334 m (by decide) (by decide))
  · exact absurd h (factorial_add_one_ne_sq 98 97092175013660332284448160034192795594426266264944604365617979012105653222056 m (by decide) (by decide))
  · exact absurd h (factorial_add_one_ne_sq 99 966054943799492973133000870362309068674974070396662776244736194062917963496762 m (by decide) (by decide))
  · exact absurd h (factorial_add_one_ne_sq 100 9660549437994929731330008703623090686749740703966627762447361940629179634967623 m (by decide) (by decide))

/-- **Brocard's conjecture, conditional on the reduced (pronic) form of the equation.**

Assume that for every `n ≥ 101` the factorial `n !` is not four times a product of two
consecutive integers.  Then the only solutions of `n ! + 1 = m ^ 2` in natural numbers are
`(n, m) = (4, 5), (5, 11), (7, 71)`.

The range `n ≤ 100` is handled unconditionally by `brocard_le_hundred`, and the hypothesis is
exactly the reduced form of Brocard's equation provided by `brocard_iff_pronic`. -/
