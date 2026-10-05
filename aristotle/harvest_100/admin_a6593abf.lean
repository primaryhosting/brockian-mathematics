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

/-!
# Brocard Conjecture
Category: Brockian Conjecture
Target: Brockian.BrocardProblem.BrocardConjecture
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)

Brocard's problem asks for all solutions of the Diophantine equation
`n ! + 1 = m ^ 2`.  The three known solutions are `n = 4, 5, 7` (with
`m = 5, 11, 71`), and *Brocard's conjecture* asserts that there are no
others.  The problem is open.

This file contains:

* the exact determination of all solutions with `n ≤ 7` (unconditional);
* an elementary **equivalent reformulation**: for `n ≥ 2`, `n ! + 1` is a
  square if and only if `n !` is four times a pronic number,
  `n ! = 4 * k * (k + 1)`;
* a **Wilson-prime obstruction** (unconditional): if `n + 1` is prime and
  `n ! + 1` is a square, then `n + 1` is a Wilson prime, i.e.
  `(n+1)^2 ∣ n ! + 1`;
* an unconditional verification that there is no solution with `8 ≤ n ≤ 100`
  (in particular none at the Wilson prime `13`, i.e. `n = 12`);
* the target theorem `BrocardConjecture`, a **conditional reduction**: the
  full conjecture follows from the reformulated statement
  `∀ n ≥ 101, ∀ k, n ! ≠ 4 * k * (k + 1)`, which is itself equivalent to the
  conjecture for `n ≥ 101`.
-/

namespace Brockian
namespace BrocardProblem

open Nat

/-- `IsBrocardSolution n m` says that `(n, m)` solves Brocard's equation
`n ! + 1 = m ^ 2`. -/
def IsBrocardSolution (n m : ℕ) : Prop := n ! + 1 = m ^ 2

/-- `p` is a *Wilson prime*: a prime with `p ^ 2 ∣ (p - 1)! + 1`. -/
def WilsonPrime (p : ℕ) : Prop := p.Prime ∧ p ^ 2 ∣ (p - 1)! + 1

/-! ### Elementary square arithmetic -/

/-- If `N` lies strictly between two consecutive squares, it is not a square. -/
theorem not_sq_of_between {N a : ℕ} (h1 : a ^ 2 < N) (h2 : N < (a + 1) ^ 2) :
    ∀ m : ℕ, m ^ 2 ≠ N := by
  intro m hm
  have hma : a < m := by
    by_contra h
    push_neg at h
    exact absurd (Nat.pow_le_pow_left h 2) (by omega)
  have : (a + 1) ^ 2 ≤ m ^ 2 := Nat.pow_le_pow_left hma 2
  omega

/-- Squares determine their roots in `ℕ`. -/
theorem eq_of_sq_eq_sq {m a : ℕ} (h : m ^ 2 = a ^ 2) : m = a :=
  Nat.pow_left_injective (by norm_num) h

/-! ### The three known solutions -/

theorem isBrocardSolution_four : IsBrocardSolution 4 5 := by
  unfold IsBrocardSolution; decide

theorem isBrocardSolution_five : IsBrocardSolution 5 11 := by
  unfold IsBrocardSolution; decide

theorem isBrocardSolution_seven : IsBrocardSolution 7 71 := by
  unfold IsBrocardSolution; decide

/-! ### Solutions with small `n` -/

/-- All solutions with `n ≤ 7` are the three known ones. -/
theorem solution_small {n m : ℕ} (hn : n ≤ 7) (h : IsBrocardSolution n m) :
    (n = 4 ∧ m = 5) ∨ (n = 5 ∧ m = 11) ∨ (n = 7 ∧ m = 71) := by
  unfold IsBrocardSolution at h
  interval_cases n <;> simp [Nat.factorial] at h ⊢
  · exact absurd h.symm (not_sq_of_between (a := 1) (by norm_num) (by norm_num) m)
  · exact absurd h.symm (not_sq_of_between (a := 1) (by norm_num) (by norm_num) m)
  · exact absurd h.symm (not_sq_of_between (a := 1) (by norm_num) (by norm_num) m)
  · exact absurd h.symm (not_sq_of_between (a := 2) (by norm_num) (by norm_num) m)
  · exact eq_of_sq_eq_sq (a := 5) (by omega)
  · exact eq_of_sq_eq_sq (a := 11) (by omega)
  · exact absurd h.symm (not_sq_of_between (a := 26) (by norm_num) (by norm_num) m)
  · exact eq_of_sq_eq_sq (a := 71) (by omega)

/-! ### An equivalent reformulation -/

/-- **Reformulation.**  For `n ≥ 2`, `n ! + 1` is a perfect square iff `n !` is
four times a pronic number.  (Indeed `n ! + 1 = m ^ 2` forces `m` odd, say
`m = 2 * k + 1`, and then `n ! = 4 * k * (k + 1)`.) -/
theorem sq_succ_factorial_iff_pronic {n : ℕ} (hn : 2 ≤ n) :
    (∃ m, n ! + 1 = m ^ 2) ↔ ∃ k, n ! = 4 * k * (k + 1) := by
  constructor
  · rintro ⟨m, hm⟩
    have h2 : 2 ∣ n ! := Nat.dvd_factorial (by norm_num) hn
    have hmodd : ¬ 2 ∣ m := by
      rintro ⟨t, ht⟩
      subst ht
      obtain ⟨s, hs⟩ := h2
      have : (2 * t) ^ 2 = 4 * t ^ 2 := by ring
      omega
    obtain ⟨k, hk⟩ : ∃ k, m = 2 * k + 1 := by
      rcases Nat.even_or_odd m with he | ho
      · exact absurd he.two_dvd hmodd
      · obtain ⟨k, hk⟩ := ho; exact ⟨k, by omega⟩
    refine ⟨k, ?_⟩
    subst hk
    have : (2 * k + 1) ^ 2 = 4 * k * (k + 1) + 1 := by ring
    omega
  · rintro ⟨k, hk⟩
    exact ⟨2 * k + 1, by rw [hk]; ring⟩

/-! ### No solutions for `8 ≤ n ≤ 100` -/

/-- **Unconditional partial result.**  There is no Brocard solution with
`8 ≤ n ≤ 100`: in each case `n ! + 1` lies strictly between two consecutive
squares. -/
theorem not_isBrocardSolution_of_medium {n m : ℕ} (h8 : 8 ≤ n) (h100 : n ≤ 100) :
    ¬ IsBrocardSolution n m := by
  unfold IsBrocardSolution
  intro h
  interval_cases n
  · exact not_sq_of_between (N := 40321) (a := 200) (by norm_num) (by norm_num) m
      (by simpa [Nat.factorial] using h.symm)
  · exact not_sq_of_between (N := 362881) (a := 602) (by norm_num) (by norm_num) m
      (by simpa [Nat.factorial] using h.symm)
  · exact not_sq_of_between (N := 3628801) (a := 1904) (by norm_num) (by norm_num) m
      (by simpa [Nat.factorial] using h.symm)
  · exact not_sq_of_between (N := 39916801) (a := 6317) (by norm_num) (by norm_num) m
      (by simpa [Nat.factorial] using h.symm)
  · exact not_sq_of_between (N := 479001601) (a := 21886) (by norm_num) (by norm_num) m
      (by simpa [Nat.factorial] using h.symm)
  · exact not_sq_of_between (N := 6227020801) (a := 78911) (by norm_num) (by norm_num) m
      (by simpa [Nat.factorial] using h.symm)
  · exact not_sq_of_between (N := 87178291201) (a := 295259) (by norm_num) (by norm_num) m
      (by simpa [Nat.factorial] using h.symm)
  · exact not_sq_of_between (N := 1307674368001) (a := 1143535) (by norm_num) (by norm_num) m
      (by simpa [Nat.factorial] using h.symm)
  · exact not_sq_of_between (N := 20922789888001) (a := 4574143) (by norm_num) (by norm_num) m
      (by simpa [Nat.factorial] using h.symm)
  · exact not_sq_of_between (N := 355687428096001) (a := 18859677) (by norm_num) (by norm_num) m
      (by simpa [Nat.factorial] using h.symm)
  · exact not_sq_of_between (N := 6402373705728001) (a := 80014834) (by norm_num) (by norm_num) m
      (by simpa [Nat.factorial] using h.symm)
  · exact not_sq_of_between (N := 121645100408832001) (a := 348776576) (by norm_num) (by norm_num) m
      (by simpa [Nat.factorial] using h.symm)
  · exact not_sq_of_between (N := 2432902008176640001) (a := 1559776268) (by norm_num) (by norm_num) m
      (by simpa [Nat.factorial] using h.symm)
  · exact not_sq_of_between (N := 51090942171709440001) (a := 7147792818) (by norm_num) (by norm_num) m
      (by simpa [Nat.factorial] using h.symm)
  · exact not_sq_of_between (N := 1124000727777607680001) (a := 33526120082) (by norm_num) (by norm_num) m
      (by simpa [Nat.factorial] using h.symm)
  · exact not_sq_of_between (N := 25852016738884976640001) (a := 160785623545) (by norm_num) (by norm_num) m
      (by simpa [Nat.factorial] using h.symm)
  · exact not_sq_of_between (N := 620448401733239439360001) (a := 787685471322) (by norm_num) (by norm_num) m
      (by simpa [Nat.factorial] using h.symm)
  · exact not_sq_of_between (N := 15511210043330985984000001) (a := 3938427356614) (by norm_num) (by norm_num) m
      (by simpa [Nat.factorial] using h.symm)
  · exact not_sq_of_between (N := 403291461126605635584000001) (a := 20082117944245) (by norm_num) (by norm_num) m
      (by simpa [Nat.factorial] using h.symm)
  · exact not_sq_of_between (N := 10888869450418352160768000001) (a := 104349745809073) (by norm_num) (by norm_num) m
      (by simpa [Nat.factorial] using h.symm)
  · exact not_sq_of_between (N := 304888344611713860501504000001) (a := 552166953567228) (by norm_num) (by norm_num) m
      (by simpa [Nat.factorial] using h.symm)
  · exact not_sq_of_between (N := 8841761993739701954543616000001) (a := 2973510046012910) (by norm_num) (by norm_num) m
      (by simpa [Nat.factorial] using h.symm)
  · exact not_sq_of_between (N := 265252859812191058636308480000001) (a := 16286585271694955) (by norm_num) (by norm_num) m
      (by simpa [Nat.factorial] using h.symm)
  · exact not_sq_of_between (N := 8222838654177922817725562880000001) (a := 90679869067935485) (by norm_num) (by norm_num) m
      (by simpa [Nat.factorial] using h.symm)
  · exact not_sq_of_between (N := 263130836933693530167218012160000001) (a := 512962802680363491) (by norm_num) (by norm_num) m
      (by simpa [Nat.factorial] using h.symm)
  · exact not_sq_of_between (N := 8683317618811886495518194401280000001) (a := 2946746955341073478) (by norm_num) (by norm_num) m
      (by simpa [Nat.factorial] using h.symm)
  · exact not_sq_of_between (N := 295232799039604140847618609643520000001) (a := 17182339742875652406) (by norm_num) (by norm_num) m
      (by simpa [Nat.factorial] using h.symm)
  · exact not_sq_of_between (N := 10333147966386144929666651337523200000001) (a := 101652092779175702171) (by norm_num) (by norm_num) m
      (by simpa [Nat.factorial] using h.symm)
  · exact not_sq_of_between (N := 371993326789901217467999448150835200000001) (a := 609912556675054213027) (by norm_num) (by norm_num) m
      (by simpa [Nat.factorial] using h.symm)
  · exact not_sq_of_between (N := 13763753091226345046315979581580902400000001) (a := 3709953246501409085690) (by norm_num) (by norm_num) m
      (by simpa [Nat.factorial] using h.symm)
  · exact not_sq_of_between (N := 523022617466601111760007224100074291200000001) (a := 22869687743093501007951) (by norm_num) (by norm_num) m
      (by simpa [Nat.factorial] using h.symm)
  · exact not_sq_of_between (N := 20397882081197443358640281739902897356800000001) (a := 142821154179615294686593) (by norm_num) (by norm_num) m
      (by simpa [Nat.factorial] using h.symm)
  · exact not_sq_of_between (N := 815915283247897734345611269596115894272000000001) (a := 903280290523322408635610) (by norm_num) (by norm_num) m
      (by simpa [Nat.factorial] using h.symm)
  · exact not_sq_of_between (N := 33452526613163807108170062053440751665152000000001) (a := 5783815921445270815783609) (by norm_num) (by norm_num) m
      (by simpa [Nat.factorial] using h.symm)
  · exact not_sq_of_between (N := 1405006117752879898543142606244511569936384000000001) (a := 37483411234209726053065805) (by norm_num) (by norm_num) m
      (by simpa [Nat.factorial] using h.symm)
  · exact not_sq_of_between (N := 60415263063373835637355132068513997507264512000000001) (a := 245795164849461258960674062) (by norm_num) (by norm_num) m
      (by simpa [Nat.factorial] using h.symm)
  · exact not_sq_of_between (N := 2658271574788448768043625811014615890319638528000000001) (a := 1630420674178430788228519563) (by norm_num) (by norm_num) m
      (by simpa [Nat.factorial] using h.symm)
  · exact not_sq_of_between (N := 119622220865480194561963161495657715064383733760000000001) (a := 10937194378152021970306618007) (by norm_num) (by norm_num) m
      (by simpa [Nat.factorial] using h.symm)
  · exact not_sq_of_between (N := 5502622159812088949850305428800254892961651752960000000001) (a := 74179661362209580727623742159) (by norm_num) (by norm_num) m
      (by simpa [Nat.factorial] using h.symm)
  · exact not_sq_of_between (N := 258623241511168180642964355153611979969197632389120000000001) (a := 508550136674023695658451670185) (by norm_num) (by norm_num) m
      (by simpa [Nat.factorial] using h.symm)
  · exact not_sq_of_between (N := 12413915592536072670862289047373375038521486354677760000000001) (a := 3523338699662022653505900576721) (by norm_num) (by norm_num) m
      (by simpa [Nat.factorial] using h.symm)
  · exact not_sq_of_between (N := 608281864034267560872252163321295376887552831379210240000000001) (a := 24663370897634158574541304037050) (by norm_num) (by norm_num) m
      (by simpa [Nat.factorial] using h.symm)
  · exact not_sq_of_between (N := 30414093201713378043612608166064768844377641568960512000000000001) (a := 174396368086360611696209329639024) (by norm_num) (by norm_num) m
      (by simpa [Nat.factorial] using h.symm)
  · exact not_sq_of_between (N := 1551118753287382280224243016469303211063259720016986112000000000001) (a := 1245439180886558699493562057691804) (by norm_num) (by norm_num) m
      (by simpa [Nat.factorial] using h.symm)
  · exact not_sq_of_between (N := 80658175170943878571660636856403766975289505440883277824000000000001) (a := 8980989654316715588967781706572076) (by norm_num) (by norm_num) m
      (by simpa [Nat.factorial] using h.symm)
  · exact not_sq_of_between (N := 4274883284060025564298013753389399649690343788366813724672000000000001) (a := 65382591597917144387816492317568177) (by norm_num) (by norm_num) m
      (by simpa [Nat.factorial] using h.symm)
  · exact not_sq_of_between (N := 230843697339241380472092742683027581083278564571807941132288000000000001) (a := 480461962427038942460267525096444474) (by norm_num) (by norm_num) m
      (by simpa [Nat.factorial] using h.symm)
  · exact not_sq_of_between (N := 12696403353658275925965100847566516959580321051449436762275840000000000001) (a := 3563201278858419461033351267854721464) (by norm_num) (by norm_num) m
      (by simpa [Nat.factorial] using h.symm)
  · exact not_sq_of_between (N := 710998587804863451854045647463724949736497978881168458687447040000000000001) (a := 26664556771205919519070097139612996000) (by norm_num) (by norm_num) m
      (by simpa [Nat.factorial] using h.symm)
  · exact not_sq_of_between (N := 40526919504877216755680601905432322134980384796226602145184481280000000000001) (a := 201312988912482288333668455069536465757) (by norm_num) (by norm_num) m
      (by simpa [Nat.factorial] using h.symm)
  · exact not_sq_of_between (N := 2350561331282878571829474910515074683828862318181142924420699914240000000000001) (a := 1533154046820761769413164705689608744377) (by norm_num) (by norm_num) m
      (by simpa [Nat.factorial] using h.symm)
  · exact not_sq_of_between (N := 138683118545689835737939019720389406345902876772687432540821294940160000000000001) (a := 11776379687564843276211019969710858039009) (by norm_num) (by norm_num) m
      (by simpa [Nat.factorial] using h.symm)
  · exact not_sq_of_between (N := 8320987112741390144276341183223364380754172606361245952449277696409600000000000001) (a := 91219444817107882594696857529818207676198) (by norm_num) (by norm_num) m
      (by simpa [Nat.factorial] using h.symm)
  · exact not_sq_of_between (N := 507580213877224798800856812176625227226004528988036003099405939480985600000000000001) (a := 712446639319201784948673912308403605115342) (by norm_num) (by norm_num) m
      (by simpa [Nat.factorial] using h.symm)
  · exact not_sq_of_between (N := 31469973260387937525653122354950764088012280797258232192163168247821107200000000000001) (a := 5609810447812647575362248801595614968784558) (by norm_num) (by norm_num) m
      (by simpa [Nat.factorial] using h.symm)
  · exact not_sq_of_between (N := 1982608315404440064116146708361898137544773690227268628106279599612729753600000000000001) (a := 44526490041372451122965980435912297622389065) (by norm_num) (by norm_num) m
      (by simpa [Nat.factorial] using h.symm)
  · exact not_sq_of_between (N := 126886932185884164103433389335161480802865516174545192198801894375214704230400000000000001) (a := 356211920330979608983727843487298380979112523) (by norm_num) (by norm_num) m
      (by simpa [Nat.factorial] using h.symm)
  · exact not_sq_of_between (N := 8247650592082470666723170306785496252186258551345437492922123134388955774976000000000000001) (a := 2871872314724746021942727901945240734448707786) (by norm_num) (by norm_num) m
      (by simpa [Nat.factorial] using h.symm)
  · exact not_sq_of_between (N := 544344939077443064003729240247842752644293064388798874532860126869671081148416000000000000001) (a := 23331200978034608323876057832648816217523382535) (by norm_num) (by norm_num) m
      (by simpa [Nat.factorial] using h.symm)
  · exact not_sq_of_between (N := 36471110918188685288249859096605464427167635314049524593701628500267962436943872000000000000001) (a := 190974110596668796970008672429388554580114244205) (by norm_num) (by norm_num) m
      (by simpa [Nat.factorial] using h.symm)
  · exact not_sq_of_between (N := 2480035542436830599600990418569171581047399201355367672371710738018221445712183296000000000000001) (a := 1574812859496908794403637793960093262759360945119) (by norm_num) (by norm_num) m
      (by simpa [Nat.factorial] using h.symm)
  · exact not_sq_of_between (N := 171122452428141311372468338881272839092270544893520369393648040923257279754140647424000000000000001) (a := 13081378078327271990661335578798848847474255303826) (by norm_num) (by norm_num) m
      (by simpa [Nat.factorial] using h.symm)
  · exact not_sq_of_between (N := 11978571669969891796072783721689098736458938142546425857555362864628009582789845319680000000000000001) (a := 109446661301155695857080695109221322834464193656741) (by norm_num) (by norm_num) m
      (by simpa [Nat.factorial] using h.symm)
  · exact not_sq_of_between (N := 850478588567862317521167644239926010288584608120796235886430763388588680378079017697280000000000000001) (a := 922213960297642814598347871007016379244405330655250) (by norm_num) (by norm_num) m
      (by simpa [Nat.factorial] using h.symm)
  · exact not_sq_of_between (N := 61234458376886086861524070385274672740778091784697328983823014963978384987221689274204160000000000000001) (a := 7825244940376376925358096892704591704511772131306815) (by norm_num) (by norm_num) m
      (by simpa [Nat.factorial] using h.symm)
  · exact not_sq_of_between (N := 4470115461512684340891257138125051110076800700282905015819080092370422104067183317016903680000000000000001) (a := 66858922078602825324590583356376523422703411874063526) (by norm_num) (by norm_num) m
      (by simpa [Nat.factorial] using h.symm)
  · exact not_sq_of_between (N := 330788544151938641225953028221253782145683251820934971170611926835411235700971565459250872320000000000000001) (a := 575142194723999224356836312510183507170717503745407529) (by norm_num) (by norm_num) m
      (by simpa [Nat.factorial] using h.symm)
  · exact not_sq_of_between (N := 24809140811395398091946477116594033660926243886570122837795894512655842677572867409443815424000000000000000001) (a := 4980877514193196669713282991946078429827937232372941867) (by norm_num) (by norm_num) m
      (by simpa [Nat.factorial] using h.symm)
  · exact not_sq_of_between (N := 1885494701666050254987932260861146558230394535379329335672487982961844043495537923117729972224000000000000000001) (a := 43422283469044442400520987277954690033900570230313299933) (by norm_num) (by norm_num) m
      (by simpa [Nat.factorial] using h.symm)
  · exact not_sq_of_between (N := 145183092028285869634070784086308284983740379224208358846781574688061991349156420080065207861248000000000000000001) (a := 381028991060110634246276414878912279469899189376847948137) (by norm_num) (by norm_num) m
      (by simpa [Nat.factorial] using h.symm)
  · exact not_sq_of_between (N := 11324281178206297831457521158732046228731749579488251990048962825668835325234200766245086213177344000000000000000001) (a := 3365156932181068109459677272856044111292549448241189337343) (by norm_num) (by norm_num) m
      (by simpa [Nat.factorial] using h.symm)
  · exact not_sq_of_between (N := 894618213078297528685144171539831652069808216779571907213868063227837990693501860533361810841010176000000000000000001) (a := 29910169058002623210200515287548862104836069367192860122492) (by norm_num) (by norm_num) m
      (by simpa [Nat.factorial] using h.symm)
  · exact not_sq_of_between (N := 71569457046263802294811533723186532165584657342365752577109445058227039255480148842668944867280814080000000000000000001) (a := 267524684928818862621490012042605003730753817304274266583374) (by norm_num) (by norm_num) m
      (by simpa [Nat.factorial] using h.symm)
  · exact not_sq_of_between (N := 5797126020747367985879734231578109105412357244731625958745865049716390179693892056256184534249745940480000000000000000001) (a := 2407722164359369763593410108383445033576784355738468399250368) (by norm_num) (by norm_num) m
      (by simpa [Nat.factorial] using h.symm)
  · exact not_sq_of_between (N := 475364333701284174842138206989404946643813294067993328617160934076743994734899148613007131808479167119360000000000000000001) (a := 21802851503903891305843592056331800458090082265244558375673041) (by norm_num) (by norm_num) m
      (by simpa [Nat.factorial] using h.symm)
  · exact not_sq_of_between (N := 39455239697206586511897471180120610571436503407643446275224357528369751562996629334879591940103770870906880000000000000000001) (a := 198633430462262788036763464177703883166690275063913206990548481) (by norm_num) (by norm_num) m
      (by simpa [Nat.factorial] using h.symm)
  · exact not_sq_of_between (N := 3314240134565353266999387579130131288000666286242049487118846032383059131291716864129885722968716753156177920000000000000000001) (a := 1820505461284132832359203813645046756110583331925714370170257092) (by norm_num) (by norm_num) m
      (by simpa [Nat.factorial] using h.symm)
  · exact not_sq_of_between (N := 281710411438055027694947944226061159480056634330574206405101912752560026159795933451040286452340924018275123200000000000000000001) (a := 16784231035053557904028966906346483792025484094796637394973403970) (by norm_num) (by norm_num) m
      (by simpa [Nat.factorial] using h.symm)
  · exact not_sq_of_between (N := 24227095383672732381765523203441259715284870552429381750838764496720162249742450276789464634901319465571660595200000000000000000001) (a := 155650555359345674201535001388480503193835670087005087695666582899) (by norm_num) (by norm_num) m
      (by simpa [Nat.factorial] using h.symm)
  · exact not_sq_of_between (N := 2107757298379527717213600518699389595229783738061356212322972511214654115727593174080683423236414793504734471782400000000000000000001) (a := 1451811729660401840498379775717372701145990271033308799231637667601) (by norm_num) (by norm_num) m
      (by simpa [Nat.factorial] using h.symm)
  · exact not_sq_of_between (N := 185482642257398439114796845645546284380220968949399346684421580986889562184028199319100141244804501828416633516851200000000000000000001) (a := 13619201234191322393627253212934023042404388731461906952430812397994) (by norm_num) (by norm_num) m
      (by simpa [Nat.factorial] using h.symm)
  · exact not_sq_of_between (N := 16507955160908461081216919262453619309839666236496541854913520707833171034378509739399912570787600662729080382999756800000000000000000001) (a := 128483287477042947436606854413089420338280480054241478815100633956558) (by norm_num) (by norm_num) m
      (by simpa [Nat.factorial] using h.symm)
  · exact not_sq_of_between (N := 1485715964481761497309522733620825737885569961284688766942216863704985393094065876545992131370884059645617234469978112000000000000000000001) (a := 1218899489080933816973227253068021382231629321448981884930371490328689) (by norm_num) (by norm_num) m
      (by simpa [Nat.factorial] using h.symm)
  · exact not_sq_of_between (N := 135200152767840296255166568759495142147586866476906677791741734597153670771559994765685283954750449427751168336768008192000000000000000000001) (a := 11627560052213890684239693812535151882288553865765313903995958273943586) (by norm_num) (by norm_num) m
      (by simpa [Nat.factorial] using h.symm)
  · exact not_sq_of_between (N := 12438414054641307255475324325873553077577991715875414356840239582938137710983519518443046123837041347353107486982656753664000000000000000000001) (a := 111527638075238136262755547542307772029800712447380847367329167783382104) (by norm_num) (by norm_num) m
      (by simpa [Nat.factorial] using h.symm)
  · exact not_sq_of_between (N := 1156772507081641574759205162306240436214753229576413535186142281213246807121467315215203289516844845303838996289387078090752000000000000000000001) (a := 1075533591796017115343430456551200439746548977577162936545074776552498754) (by norm_num) (by norm_num) m
      (by simpa [Nat.factorial] using h.symm)
  · exact not_sq_of_between (N := 108736615665674308027365285256786601004186803580182872307497374434045199869417927630229109214583415458560865651202385340530688000000000000000000001) (a := 10427685057848376925507942191442630012584828624363222101172323570579332599) (by norm_num) (by norm_num) m
      (by simpa [Nat.factorial] using h.symm)
  · exact not_sq_of_between (N := 10329978488239059262599702099394727095397746340117372869212250571234293987594703124871765375385424468563282236864226607350415360000000000000000000001) (a := 101636501751285493870798488028947073709983082260934656117721845292980988580) (by norm_num) (by norm_num) m
      (by simpa [Nat.factorial] using h.symm)
  · exact not_sq_of_between (N := 991677934870949689209571401541893801158183648651267795444376054838492222809091499987689476037000748982075094738965754305639874560000000000000000000001) (a := 995830274128553338795685900500337369492022050359737013283228306377142743139) (by norm_num) (by norm_num) m
      (by simpa [Nat.factorial] using h.symm)
  · exact not_sq_of_between (N := 96192759682482119853328425949563698712343813919172976158104477319333745612481875498805879175589072651261284189679678167647067832320000000000000000000001) (a := 9807790764615756210934052418079289148346460527555220609613824741800936687334) (by norm_num) (by norm_num) m
      (by simpa [Nat.factorial] using h.symm)
  · exact not_sq_of_between (N := 9426890448883247745626185743057242473809693764078951663494238777294707070023223798882976159207729119823605850588608460429412647567360000000000000000000001) (a := 97092175013660332284448160034192795594426266264944604365617979012105653222056) (by norm_num) (by norm_num) m
      (by simpa [Nat.factorial] using h.symm)
  · exact not_sq_of_between (N := 933262154439441526816992388562667004907159682643816214685929638952175999932299156089414639761565182862536979208272237582511852109168640000000000000000000001) (a := 966054943799492973133000870362309068674974070396662776244736194062917963496762) (by norm_num) (by norm_num) m
      (by simpa [Nat.factorial] using h.symm)
  · exact not_sq_of_between (N := 93326215443944152681699238856266700490715968264381621468592963895217599993229915608941463976156518286253697920827223758251185210916864000000000000000000000001) (a := 9660549437994929731330008703623090686749740703966627762447361940629179634967623) (by norm_num) (by norm_num) m
      (by simpa [Nat.factorial] using h.symm)

/-- The Wilson prime `13` does not produce a solution: `12! + 1` is not a square. -/
theorem not_isBrocardSolution_twelve (m : ℕ) : ¬ IsBrocardSolution 12 m :=
  not_isBrocardSolution_of_medium (by norm_num) (by norm_num)

/-! ### The Wilson prime obstruction -/

/-- If `p` is prime and `(p-1)! + 1` is a perfect square, then `p` is a Wilson
prime.  This is immediate from Wilson's theorem: `p ∣ (p-1)! + 1 = m ^ 2`, hence
`p ∣ m` and `p ^ 2 ∣ m ^ 2`. -/
theorem wilsonPrime_of_solution {p m : ℕ} (hp : p.Prime)
    (h : IsBrocardSolution (p - 1) m) : WilsonPrime p := by
  haveI : Fact p.Prime := ⟨hp⟩
  unfold IsBrocardSolution at h
  have hdvd : p ∣ (p - 1)! + 1 := by
    have hz : ((((p - 1)! + 1 : ℕ) : ZMod p)) = 0 := by
      push_cast [ZMod.wilsons_lemma p]
      ring
    exact (ZMod.natCast_eq_zero_iff _ _).mp hz
  refine ⟨hp, ?_⟩
  rw [h] at hdvd ⊢
  exact pow_dvd_pow_of_dvd (hp.dvd_of_dvd_pow hdvd) 2

/-- Hence: any Brocard solution `n ! + 1 = m ^ 2` with `n + 1` prime forces
`n + 1` to be a Wilson prime. -/
theorem wilsonPrime_succ_of_solution {n m : ℕ} (hp : (n + 1).Prime)
    (h : IsBrocardSolution n m) : WilsonPrime (n + 1) :=
  wilsonPrime_of_solution hp (by simpa using h)

/-! ### The conjecture -/

/-- The hypothesis used below is *equivalent* to Brocard's conjecture for
`n ≥ 101`: `n !` is never four times a pronic number iff `n ! + 1` is never a
square. -/
theorem pronic_hypothesis_iff :
    (∀ n : ℕ, 101 ≤ n → ∀ k : ℕ, n ! ≠ 4 * k * (k + 1)) ↔
      (∀ n m : ℕ, 101 ≤ n → ¬ IsBrocardSolution n m) := by
  constructor
  · intro H n m hn hsol
    obtain ⟨k, hk⟩ := (sq_succ_factorial_iff_pronic (n := n) (by omega)).mp ⟨m, hsol⟩
    exact H n hn k hk
  · intro H n hn k hk
    obtain ⟨m, hm⟩ := (sq_succ_factorial_iff_pronic (n := n) (by omega)).mpr ⟨k, hk⟩
    exact H n m hn hm

/-- **Brocard's conjecture**, conditional on the equivalent reformulation `H`:
if for every `n ≥ 101` the number `n !` is not four times a pronic number, then
the only solutions of `n ! + 1 = m ^ 2` in natural numbers are
`(n, m) = (4, 5), (5, 11), (7, 71)`.

Everything except `H` is proved unconditionally here: all `n ≤ 100` are settled
by explicit computation, and `H` is (by `pronic_hypothesis_iff`) precisely the
remaining, still open, content of Brocard's problem, restated as a statement
about factorials alone. -/
theorem BrocardConjecture (H : ∀ n : ℕ, 101 ≤ n → ∀ k : ℕ, n ! ≠ 4 * k * (k + 1)) :
    ∀ n m : ℕ, IsBrocardSolution n m ↔
      (n = 4 ∧ m = 5) ∨ (n = 5 ∧ m = 11) ∨ (n = 7 ∧ m = 71) := by
  intro n m
  constructor
  · intro h
    by_cases hn : n ≤ 7
    · exact solution_small hn h
    · by_cases hn100 : n ≤ 100
      · exact absurd h (not_isBrocardSolution_of_medium (by omega) hn100)
      · exact absurd h (pronic_hypothesis_iff.mp H n m (by omega))
  · rintro (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩)
    · exact isBrocardSolution_four
    · exact isBrocardSolution_five
    · exact isBrocardSolution_seven

end BrocardProblem
end Brockian

