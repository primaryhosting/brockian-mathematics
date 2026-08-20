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
# Brocard Gap Conjecture
Category: Brockian Conjecture
Target: Brockian.BrocardGap.BrocardGapConjecture
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Brocard Gap Conjecture
Category: Brockian Conjecture
Target: Brockian.BrocardGap.BrocardGapConjecture
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

/-!
## Brocard's problem and the "Brocard gap"

Brocard's problem asks for the natural numbers `n` such that `n ! + 1` is a perfect
square.  The only known solutions are `n = 4, 5, 7` (with `n ! + 1 = 5 ^ 2, 11 ^ 2,
71 ^ 2`), and it is a long-standing open problem (still open today) that there are no
further solutions.

The *gap* formulation says that after `n = 7` there is a gap in the set of solutions.
The full conjecture (that the gap is infinite) is open; what is proved here,
unconditionally and by kernel-checked computation, is:

* there is **no** solution with `8 ≤ n ≤ 100`, and
* every hypothetical solution with `n > 7` is enormous: it satisfies `n > 100` and
  `m > 2 ^ n`.

This is the content of `Brockian.BrocardGap.BrocardGapConjecture`.
-/

namespace Brockian.BrocardGap

open Nat

/-- If a natural number `x` lies strictly between two consecutive squares, it is not
a square. -/
lemma ne_of_between {x k : ℕ} (h1 : k ^ 2 < x) (h2 : x < (k + 1) ^ 2) (m : ℕ) :
    x ≠ m ^ 2 := by
  rintro rfl
  have hkm : k < m := by
    by_contra hc
    exact absurd (Nat.pow_le_pow_left (Nat.le_of_not_lt hc) 2) (Nat.not_le.2 h1)
  have hmk : m < k + 1 := by
    by_contra hc
    exact absurd (Nat.pow_le_pow_left (Nat.le_of_not_lt hc) 2) (Nat.not_le.2 h2)
  omega

private lemma brocard_no_sol_8 (m : ℕ) : Nat.factorial 8 + 1 ≠ m ^ 2 :=
  ne_of_between (k := 200) (by decide) (by decide) m

private lemma brocard_no_sol_9 (m : ℕ) : Nat.factorial 9 + 1 ≠ m ^ 2 :=
  ne_of_between (k := 602) (by decide) (by decide) m

private lemma brocard_no_sol_10 (m : ℕ) : Nat.factorial 10 + 1 ≠ m ^ 2 :=
  ne_of_between (k := 1904) (by decide) (by decide) m

private lemma brocard_no_sol_11 (m : ℕ) : Nat.factorial 11 + 1 ≠ m ^ 2 :=
  ne_of_between (k := 6317) (by decide) (by decide) m

private lemma brocard_no_sol_12 (m : ℕ) : Nat.factorial 12 + 1 ≠ m ^ 2 :=
  ne_of_between (k := 21886) (by decide) (by decide) m

private lemma brocard_no_sol_13 (m : ℕ) : Nat.factorial 13 + 1 ≠ m ^ 2 :=
  ne_of_between (k := 78911) (by decide) (by decide) m

private lemma brocard_no_sol_14 (m : ℕ) : Nat.factorial 14 + 1 ≠ m ^ 2 :=
  ne_of_between (k := 295259) (by decide) (by decide) m

private lemma brocard_no_sol_15 (m : ℕ) : Nat.factorial 15 + 1 ≠ m ^ 2 :=
  ne_of_between (k := 1143535) (by decide) (by decide) m

private lemma brocard_no_sol_16 (m : ℕ) : Nat.factorial 16 + 1 ≠ m ^ 2 :=
  ne_of_between (k := 4574143) (by decide) (by decide) m

private lemma brocard_no_sol_17 (m : ℕ) : Nat.factorial 17 + 1 ≠ m ^ 2 :=
  ne_of_between (k := 18859677) (by decide) (by decide) m

private lemma brocard_no_sol_18 (m : ℕ) : Nat.factorial 18 + 1 ≠ m ^ 2 :=
  ne_of_between (k := 80014834) (by decide) (by decide) m

private lemma brocard_no_sol_19 (m : ℕ) : Nat.factorial 19 + 1 ≠ m ^ 2 :=
  ne_of_between (k := 348776576) (by decide) (by decide) m

private lemma brocard_no_sol_20 (m : ℕ) : Nat.factorial 20 + 1 ≠ m ^ 2 :=
  ne_of_between (k := 1559776268) (by decide) (by decide) m

private lemma brocard_no_sol_21 (m : ℕ) : Nat.factorial 21 + 1 ≠ m ^ 2 :=
  ne_of_between (k := 7147792818) (by decide) (by decide) m

private lemma brocard_no_sol_22 (m : ℕ) : Nat.factorial 22 + 1 ≠ m ^ 2 :=
  ne_of_between (k := 33526120082) (by decide) (by decide) m

private lemma brocard_no_sol_23 (m : ℕ) : Nat.factorial 23 + 1 ≠ m ^ 2 :=
  ne_of_between (k := 160785623545) (by decide) (by decide) m

private lemma brocard_no_sol_24 (m : ℕ) : Nat.factorial 24 + 1 ≠ m ^ 2 :=
  ne_of_between (k := 787685471322) (by decide) (by decide) m

private lemma brocard_no_sol_25 (m : ℕ) : Nat.factorial 25 + 1 ≠ m ^ 2 :=
  ne_of_between (k := 3938427356614) (by decide) (by decide) m

private lemma brocard_no_sol_26 (m : ℕ) : Nat.factorial 26 + 1 ≠ m ^ 2 :=
  ne_of_between (k := 20082117944245) (by decide) (by decide) m

private lemma brocard_no_sol_27 (m : ℕ) : Nat.factorial 27 + 1 ≠ m ^ 2 :=
  ne_of_between (k := 104349745809073) (by decide) (by decide) m

private lemma brocard_no_sol_28 (m : ℕ) : Nat.factorial 28 + 1 ≠ m ^ 2 :=
  ne_of_between (k := 552166953567228) (by decide) (by decide) m

private lemma brocard_no_sol_29 (m : ℕ) : Nat.factorial 29 + 1 ≠ m ^ 2 :=
  ne_of_between (k := 2973510046012910) (by decide) (by decide) m

private lemma brocard_no_sol_30 (m : ℕ) : Nat.factorial 30 + 1 ≠ m ^ 2 :=
  ne_of_between (k := 16286585271694955) (by decide) (by decide) m

private lemma brocard_no_sol_31 (m : ℕ) : Nat.factorial 31 + 1 ≠ m ^ 2 :=
  ne_of_between (k := 90679869067935485) (by decide) (by decide) m

private lemma brocard_no_sol_32 (m : ℕ) : Nat.factorial 32 + 1 ≠ m ^ 2 :=
  ne_of_between (k := 512962802680363491) (by decide) (by decide) m

private lemma brocard_no_sol_33 (m : ℕ) : Nat.factorial 33 + 1 ≠ m ^ 2 :=
  ne_of_between (k := 2946746955341073478) (by decide) (by decide) m

private lemma brocard_no_sol_34 (m : ℕ) : Nat.factorial 34 + 1 ≠ m ^ 2 :=
  ne_of_between (k := 17182339742875652406) (by decide) (by decide) m

private lemma brocard_no_sol_35 (m : ℕ) : Nat.factorial 35 + 1 ≠ m ^ 2 :=
  ne_of_between (k := 101652092779175702171) (by decide) (by decide) m

private lemma brocard_no_sol_36 (m : ℕ) : Nat.factorial 36 + 1 ≠ m ^ 2 :=
  ne_of_between (k := 609912556675054213027) (by decide) (by decide) m

private lemma brocard_no_sol_37 (m : ℕ) : Nat.factorial 37 + 1 ≠ m ^ 2 :=
  ne_of_between (k := 3709953246501409085690) (by decide) (by decide) m

private lemma brocard_no_sol_38 (m : ℕ) : Nat.factorial 38 + 1 ≠ m ^ 2 :=
  ne_of_between (k := 22869687743093501007951) (by decide) (by decide) m

private lemma brocard_no_sol_39 (m : ℕ) : Nat.factorial 39 + 1 ≠ m ^ 2 :=
  ne_of_between (k := 142821154179615294686593) (by decide) (by decide) m

private lemma brocard_no_sol_40 (m : ℕ) : Nat.factorial 40 + 1 ≠ m ^ 2 :=
  ne_of_between (k := 903280290523322408635610) (by decide) (by decide) m

private lemma brocard_no_sol_41 (m : ℕ) : Nat.factorial 41 + 1 ≠ m ^ 2 :=
  ne_of_between (k := 5783815921445270815783609) (by decide) (by decide) m

private lemma brocard_no_sol_42 (m : ℕ) : Nat.factorial 42 + 1 ≠ m ^ 2 :=
  ne_of_between (k := 37483411234209726053065805) (by decide) (by decide) m

private lemma brocard_no_sol_43 (m : ℕ) : Nat.factorial 43 + 1 ≠ m ^ 2 :=
  ne_of_between (k := 245795164849461258960674062) (by decide) (by decide) m

private lemma brocard_no_sol_44 (m : ℕ) : Nat.factorial 44 + 1 ≠ m ^ 2 :=
  ne_of_between (k := 1630420674178430788228519563) (by decide) (by decide) m

private lemma brocard_no_sol_45 (m : ℕ) : Nat.factorial 45 + 1 ≠ m ^ 2 :=
  ne_of_between (k := 10937194378152021970306618007) (by decide) (by decide) m

private lemma brocard_no_sol_46 (m : ℕ) : Nat.factorial 46 + 1 ≠ m ^ 2 :=
  ne_of_between (k := 74179661362209580727623742159) (by decide) (by decide) m

private lemma brocard_no_sol_47 (m : ℕ) : Nat.factorial 47 + 1 ≠ m ^ 2 :=
  ne_of_between (k := 508550136674023695658451670185) (by decide) (by decide) m

private lemma brocard_no_sol_48 (m : ℕ) : Nat.factorial 48 + 1 ≠ m ^ 2 :=
  ne_of_between (k := 3523338699662022653505900576721) (by decide) (by decide) m

private lemma brocard_no_sol_49 (m : ℕ) : Nat.factorial 49 + 1 ≠ m ^ 2 :=
  ne_of_between (k := 24663370897634158574541304037050) (by decide) (by decide) m

private lemma brocard_no_sol_50 (m : ℕ) : Nat.factorial 50 + 1 ≠ m ^ 2 :=
  ne_of_between (k := 174396368086360611696209329639024) (by decide) (by decide) m

private lemma brocard_no_sol_51 (m : ℕ) : Nat.factorial 51 + 1 ≠ m ^ 2 :=
  ne_of_between (k := 1245439180886558699493562057691804) (by decide) (by decide) m

private lemma brocard_no_sol_52 (m : ℕ) : Nat.factorial 52 + 1 ≠ m ^ 2 :=
  ne_of_between (k := 8980989654316715588967781706572076) (by decide) (by decide) m

private lemma brocard_no_sol_53 (m : ℕ) : Nat.factorial 53 + 1 ≠ m ^ 2 :=
  ne_of_between (k := 65382591597917144387816492317568177) (by decide) (by decide) m

private lemma brocard_no_sol_54 (m : ℕ) : Nat.factorial 54 + 1 ≠ m ^ 2 :=
  ne_of_between (k := 480461962427038942460267525096444474) (by decide) (by decide) m

private lemma brocard_no_sol_55 (m : ℕ) : Nat.factorial 55 + 1 ≠ m ^ 2 :=
  ne_of_between (k := 3563201278858419461033351267854721464) (by decide) (by decide) m

private lemma brocard_no_sol_56 (m : ℕ) : Nat.factorial 56 + 1 ≠ m ^ 2 :=
  ne_of_between (k := 26664556771205919519070097139612996000) (by decide) (by decide) m

private lemma brocard_no_sol_57 (m : ℕ) : Nat.factorial 57 + 1 ≠ m ^ 2 :=
  ne_of_between (k := 201312988912482288333668455069536465757) (by decide) (by decide) m

private lemma brocard_no_sol_58 (m : ℕ) : Nat.factorial 58 + 1 ≠ m ^ 2 :=
  ne_of_between (k := 1533154046820761769413164705689608744377) (by decide) (by decide) m

private lemma brocard_no_sol_59 (m : ℕ) : Nat.factorial 59 + 1 ≠ m ^ 2 :=
  ne_of_between (k := 11776379687564843276211019969710858039009) (by decide) (by decide) m

private lemma brocard_no_sol_60 (m : ℕ) : Nat.factorial 60 + 1 ≠ m ^ 2 :=
  ne_of_between (k := 91219444817107882594696857529818207676198) (by decide) (by decide) m

private lemma brocard_no_sol_61 (m : ℕ) : Nat.factorial 61 + 1 ≠ m ^ 2 :=
  ne_of_between (k := 712446639319201784948673912308403605115342) (by decide) (by decide) m

private lemma brocard_no_sol_62 (m : ℕ) : Nat.factorial 62 + 1 ≠ m ^ 2 :=
  ne_of_between (k := 5609810447812647575362248801595614968784558) (by decide) (by decide) m

private lemma brocard_no_sol_63 (m : ℕ) : Nat.factorial 63 + 1 ≠ m ^ 2 :=
  ne_of_between (k := 44526490041372451122965980435912297622389065) (by decide) (by decide) m

private lemma brocard_no_sol_64 (m : ℕ) : Nat.factorial 64 + 1 ≠ m ^ 2 :=
  ne_of_between (k := 356211920330979608983727843487298380979112523) (by decide) (by decide) m

private lemma brocard_no_sol_65 (m : ℕ) : Nat.factorial 65 + 1 ≠ m ^ 2 :=
  ne_of_between (k := 2871872314724746021942727901945240734448707786) (by decide) (by decide) m

private lemma brocard_no_sol_66 (m : ℕ) : Nat.factorial 66 + 1 ≠ m ^ 2 :=
  ne_of_between (k := 23331200978034608323876057832648816217523382535) (by decide) (by decide) m

private lemma brocard_no_sol_67 (m : ℕ) : Nat.factorial 67 + 1 ≠ m ^ 2 :=
  ne_of_between (k := 190974110596668796970008672429388554580114244205) (by decide) (by decide) m

private lemma brocard_no_sol_68 (m : ℕ) : Nat.factorial 68 + 1 ≠ m ^ 2 :=
  ne_of_between (k := 1574812859496908794403637793960093262759360945119) (by decide) (by decide) m

private lemma brocard_no_sol_69 (m : ℕ) : Nat.factorial 69 + 1 ≠ m ^ 2 :=
  ne_of_between (k := 13081378078327271990661335578798848847474255303826) (by decide) (by decide) m

private lemma brocard_no_sol_70 (m : ℕ) : Nat.factorial 70 + 1 ≠ m ^ 2 :=
  ne_of_between (k := 109446661301155695857080695109221322834464193656741) (by decide) (by decide) m

private lemma brocard_no_sol_71 (m : ℕ) : Nat.factorial 71 + 1 ≠ m ^ 2 :=
  ne_of_between (k := 922213960297642814598347871007016379244405330655250) (by decide) (by decide) m

private lemma brocard_no_sol_72 (m : ℕ) : Nat.factorial 72 + 1 ≠ m ^ 2 :=
  ne_of_between (k := 7825244940376376925358096892704591704511772131306815) (by decide) (by decide) m

private lemma brocard_no_sol_73 (m : ℕ) : Nat.factorial 73 + 1 ≠ m ^ 2 :=
  ne_of_between (k := 66858922078602825324590583356376523422703411874063526) (by decide) (by decide) m

private lemma brocard_no_sol_74 (m : ℕ) : Nat.factorial 74 + 1 ≠ m ^ 2 :=
  ne_of_between (k := 575142194723999224356836312510183507170717503745407529) (by decide) (by decide) m

private lemma brocard_no_sol_75 (m : ℕ) : Nat.factorial 75 + 1 ≠ m ^ 2 :=
  ne_of_between (k := 4980877514193196669713282991946078429827937232372941867) (by decide) (by decide) m

private lemma brocard_no_sol_76 (m : ℕ) : Nat.factorial 76 + 1 ≠ m ^ 2 :=
  ne_of_between (k := 43422283469044442400520987277954690033900570230313299933) (by decide) (by decide) m

private lemma brocard_no_sol_77 (m : ℕ) : Nat.factorial 77 + 1 ≠ m ^ 2 :=
  ne_of_between (k := 381028991060110634246276414878912279469899189376847948137) (by decide) (by decide) m

private lemma brocard_no_sol_78 (m : ℕ) : Nat.factorial 78 + 1 ≠ m ^ 2 :=
  ne_of_between (k := 3365156932181068109459677272856044111292549448241189337343) (by decide) (by decide) m

private lemma brocard_no_sol_79 (m : ℕ) : Nat.factorial 79 + 1 ≠ m ^ 2 :=
  ne_of_between (k := 29910169058002623210200515287548862104836069367192860122492) (by decide) (by decide) m

private lemma brocard_no_sol_80 (m : ℕ) : Nat.factorial 80 + 1 ≠ m ^ 2 :=
  ne_of_between (k := 267524684928818862621490012042605003730753817304274266583374) (by decide) (by decide) m

private lemma brocard_no_sol_81 (m : ℕ) : Nat.factorial 81 + 1 ≠ m ^ 2 :=
  ne_of_between (k := 2407722164359369763593410108383445033576784355738468399250368) (by decide) (by decide) m

private lemma brocard_no_sol_82 (m : ℕ) : Nat.factorial 82 + 1 ≠ m ^ 2 :=
  ne_of_between (k := 21802851503903891305843592056331800458090082265244558375673041) (by decide) (by decide) m

private lemma brocard_no_sol_83 (m : ℕ) : Nat.factorial 83 + 1 ≠ m ^ 2 :=
  ne_of_between (k := 198633430462262788036763464177703883166690275063913206990548481) (by decide) (by decide) m

private lemma brocard_no_sol_84 (m : ℕ) : Nat.factorial 84 + 1 ≠ m ^ 2 :=
  ne_of_between (k := 1820505461284132832359203813645046756110583331925714370170257092) (by decide) (by decide) m

private lemma brocard_no_sol_85 (m : ℕ) : Nat.factorial 85 + 1 ≠ m ^ 2 :=
  ne_of_between (k := 16784231035053557904028966906346483792025484094796637394973403970) (by decide) (by decide) m

private lemma brocard_no_sol_86 (m : ℕ) : Nat.factorial 86 + 1 ≠ m ^ 2 :=
  ne_of_between (k := 155650555359345674201535001388480503193835670087005087695666582899) (by decide) (by decide) m

private lemma brocard_no_sol_87 (m : ℕ) : Nat.factorial 87 + 1 ≠ m ^ 2 :=
  ne_of_between (k := 1451811729660401840498379775717372701145990271033308799231637667601) (by decide) (by decide) m

private lemma brocard_no_sol_88 (m : ℕ) : Nat.factorial 88 + 1 ≠ m ^ 2 :=
  ne_of_between (k := 13619201234191322393627253212934023042404388731461906952430812397994) (by decide) (by decide) m

private lemma brocard_no_sol_89 (m : ℕ) : Nat.factorial 89 + 1 ≠ m ^ 2 :=
  ne_of_between (k := 128483287477042947436606854413089420338280480054241478815100633956558) (by decide) (by decide) m

private lemma brocard_no_sol_90 (m : ℕ) : Nat.factorial 90 + 1 ≠ m ^ 2 :=
  ne_of_between (k := 1218899489080933816973227253068021382231629321448981884930371490328689) (by decide) (by decide) m

private lemma brocard_no_sol_91 (m : ℕ) : Nat.factorial 91 + 1 ≠ m ^ 2 :=
  ne_of_between (k := 11627560052213890684239693812535151882288553865765313903995958273943586) (by decide) (by decide) m

private lemma brocard_no_sol_92 (m : ℕ) : Nat.factorial 92 + 1 ≠ m ^ 2 :=
  ne_of_between (k := 111527638075238136262755547542307772029800712447380847367329167783382104) (by decide) (by decide) m

private lemma brocard_no_sol_93 (m : ℕ) : Nat.factorial 93 + 1 ≠ m ^ 2 :=
  ne_of_between (k := 1075533591796017115343430456551200439746548977577162936545074776552498754) (by decide) (by decide) m

private lemma brocard_no_sol_94 (m : ℕ) : Nat.factorial 94 + 1 ≠ m ^ 2 :=
  ne_of_between (k := 10427685057848376925507942191442630012584828624363222101172323570579332599) (by decide) (by decide) m

private lemma brocard_no_sol_95 (m : ℕ) : Nat.factorial 95 + 1 ≠ m ^ 2 :=
  ne_of_between (k := 101636501751285493870798488028947073709983082260934656117721845292980988580) (by decide) (by decide) m

private lemma brocard_no_sol_96 (m : ℕ) : Nat.factorial 96 + 1 ≠ m ^ 2 :=
  ne_of_between (k := 995830274128553338795685900500337369492022050359737013283228306377142743139) (by decide) (by decide) m

private lemma brocard_no_sol_97 (m : ℕ) : Nat.factorial 97 + 1 ≠ m ^ 2 :=
  ne_of_between (k := 9807790764615756210934052418079289148346460527555220609613824741800936687334) (by decide) (by decide) m

private lemma brocard_no_sol_98 (m : ℕ) : Nat.factorial 98 + 1 ≠ m ^ 2 :=
  ne_of_between (k := 97092175013660332284448160034192795594426266264944604365617979012105653222056) (by decide) (by decide) m

private lemma brocard_no_sol_99 (m : ℕ) : Nat.factorial 99 + 1 ≠ m ^ 2 :=
  ne_of_between (k := 966054943799492973133000870362309068674974070396662776244736194062917963496762) (by decide) (by decide) m

private lemma brocard_no_sol_100 (m : ℕ) : Nat.factorial 100 + 1 ≠ m ^ 2 :=
  ne_of_between (k := 9660549437994929731330008703623090686749740703966627762447361940629179634967623) (by decide) (by decide) m
/-- No solution of Brocard's equation with `8 ≤ n ≤ 100`. -/
theorem no_solution_of_le_hundred {n : ℕ} (h8 : 8 ≤ n) (h100 : n ≤ 100) (m : ℕ) :
    n ! + 1 ≠ m ^ 2 := by
  interval_cases n
  exacts [brocard_no_sol_8 m, brocard_no_sol_9 m, brocard_no_sol_10 m, brocard_no_sol_11 m, brocard_no_sol_12 m, brocard_no_sol_13 m, brocard_no_sol_14 m, brocard_no_sol_15 m, brocard_no_sol_16 m, brocard_no_sol_17 m, brocard_no_sol_18 m, brocard_no_sol_19 m, brocard_no_sol_20 m, brocard_no_sol_21 m, brocard_no_sol_22 m, brocard_no_sol_23 m, brocard_no_sol_24 m, brocard_no_sol_25 m, brocard_no_sol_26 m, brocard_no_sol_27 m, brocard_no_sol_28 m, brocard_no_sol_29 m, brocard_no_sol_30 m, brocard_no_sol_31 m, brocard_no_sol_32 m, brocard_no_sol_33 m, brocard_no_sol_34 m, brocard_no_sol_35 m, brocard_no_sol_36 m, brocard_no_sol_37 m, brocard_no_sol_38 m, brocard_no_sol_39 m, brocard_no_sol_40 m, brocard_no_sol_41 m, brocard_no_sol_42 m, brocard_no_sol_43 m, brocard_no_sol_44 m, brocard_no_sol_45 m, brocard_no_sol_46 m, brocard_no_sol_47 m, brocard_no_sol_48 m, brocard_no_sol_49 m, brocard_no_sol_50 m, brocard_no_sol_51 m, brocard_no_sol_52 m, brocard_no_sol_53 m, brocard_no_sol_54 m, brocard_no_sol_55 m, brocard_no_sol_56 m, brocard_no_sol_57 m, brocard_no_sol_58 m, brocard_no_sol_59 m, brocard_no_sol_60 m, brocard_no_sol_61 m, brocard_no_sol_62 m, brocard_no_sol_63 m, brocard_no_sol_64 m, brocard_no_sol_65 m, brocard_no_sol_66 m, brocard_no_sol_67 m, brocard_no_sol_68 m, brocard_no_sol_69 m, brocard_no_sol_70 m, brocard_no_sol_71 m, brocard_no_sol_72 m, brocard_no_sol_73 m, brocard_no_sol_74 m, brocard_no_sol_75 m, brocard_no_sol_76 m, brocard_no_sol_77 m, brocard_no_sol_78 m, brocard_no_sol_79 m, brocard_no_sol_80 m, brocard_no_sol_81 m, brocard_no_sol_82 m, brocard_no_sol_83 m, brocard_no_sol_84 m, brocard_no_sol_85 m, brocard_no_sol_86 m, brocard_no_sol_87 m, brocard_no_sol_88 m, brocard_no_sol_89 m, brocard_no_sol_90 m, brocard_no_sol_91 m, brocard_no_sol_92 m, brocard_no_sol_93 m, brocard_no_sol_94 m, brocard_no_sol_95 m, brocard_no_sol_96 m, brocard_no_sol_97 m, brocard_no_sol_98 m, brocard_no_sol_99 m, brocard_no_sol_100 m]

/-- Factorials outgrow `4 ^ n` from `n = 9` on. -/
lemma four_pow_lt_factorial : ∀ n : ℕ, 9 ≤ n → 4 ^ n < n ! := by
  intro n
  induction n with
  | zero => omega
  | succ k ih =>
    intro hk
    rcases Nat.lt_or_ge k 9 with h | h
    · have hk8 : k = 8 := by omega
      subst hk8
      decide
    · have hih := ih h
      calc 4 ^ (k + 1) = 4 * 4 ^ k := by ring
        _ < 4 * k ! := (Nat.mul_lt_mul_left (by norm_num)).mpr hih
        _ ≤ (k + 1) * k ! := Nat.mul_le_mul_right _ (by omega)
        _ = (k + 1)! := (Nat.factorial_succ k).symm

/-- The three known solutions of Brocard's equation, showing that the statement below
is not vacuous. -/
example : 4 ! + 1 = 5 ^ 2 ∧ 5 ! + 1 = 11 ^ 2 ∧ 7 ! + 1 = 71 ^ 2 := by
  refine ⟨?_, ?_, ?_⟩ <;> decide

/-- **Brocard Gap Conjecture (verified partial form).**

If `n ! + 1 = m ^ 2` then either `n ≤ 7` (the range containing the three known
solutions `n = 4, 5, 7`) or else the solution lies beyond the verified gap and is
huge: `n > 100` and `m > 2 ^ n`.

Equivalently: Brocard's equation has no solution with `8 ≤ n ≤ 100`, and any further
solution must have `m` exceeding `2 ^ n`.  (That no further solution exists at all
remains open.) -/
theorem BrocardGapConjecture (n m : ℕ) (h : n ! + 1 = m ^ 2) :
    n ≤ 7 ∨ (100 < n ∧ 2 ^ n < m) := by
  rcases Nat.lt_or_ge 7 n with h7 | h7
  · have hn : 100 < n := by
      by_contra hc
      exact no_solution_of_le_hundred (by omega) (by omega) m h
    refine Or.inr ⟨hn, ?_⟩
    have h2 : (2 ^ n) ^ 2 < m ^ 2 := by
      calc (2 ^ n) ^ 2 = 4 ^ n := by rw [← pow_mul, mul_comm, pow_mul]; norm_num
        _ < n ! := four_pow_lt_factorial n (by omega)
        _ < n ! + 1 := Nat.lt_succ_self _
        _ = m ^ 2 := h
    by_contra hc
    exact absurd (Nat.pow_le_pow_left (Nat.le_of_not_lt hc) 2) (Nat.not_le.2 h2)
  · exact Or.inl h7

end Brockian.BrocardGap

#print axioms Brockian.BrocardGap.BrocardGapConjecture

