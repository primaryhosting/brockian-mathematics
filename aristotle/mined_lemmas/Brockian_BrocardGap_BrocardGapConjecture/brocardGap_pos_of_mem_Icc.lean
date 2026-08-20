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

import Mathlib

/-!
# Brocard Gap Conjecture
Category: Brockian Conjecture
Target: Brockian.BrocardGap.BrocardGapConjecture
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

/-!
## Overview

Brocard's problem asks for the solutions of `n ! + 1 = m ^ 2`.  The only known
solutions are `n = 4, 5, 7` (with `m = 5, 11, 71`), and it is conjectured that
there are no others; in *gap* form the conjecture states that the distance from
`n ! + 1` to the nearest perfect square is positive (indeed large) for all
`n ≥ 8`.  This is an open problem.

This file contains:

* `Brockian.BrocardGap.brocardGap`, the distance from `n ! + 1` to the nearest
  perfect square, and the characterisation `brocardGap_pos_iff`;
* `Brockian.BrocardGap.ABC`, the `abc` conjecture (in radical form);
* `Brockian.BrocardGap.BrocardGapConjecture`, a Lean-checked **conditional
  reduction**: the `abc` conjecture implies that the Brocard gap is positive for
  all sufficiently large `n` (this is Overholt's argument);
* `Brockian.BrocardGap.brocardGap_pos_of_mem_Icc`, an unconditional verification
  of the gap positivity for `8 ≤ n ≤ 200`;
* `Brockian.BrocardGap.brocard_iff_pronic`, the elementary reformulation of
  Brocard's equation as `n ! = 4 * a * (a + 1)`.
-/

namespace Brockian.BrocardGap

open Nat Finset

/-- The radical of a natural number: the product of its distinct prime factors. -/

theorem brocardGap_pos_of_mem_Icc {n : ℕ} (h8 : 8 ≤ n) (h200 : n ≤ 200) : 0 < brocardGap n := by
  rw [brocardGap_pos_iff]
  intro m
  interval_cases n
  · exact not_sq_of_between (k := 200) (by norm_num [Nat.factorial])
      (by norm_num [Nat.factorial]) m
  · exact not_sq_of_between (k := 602) (by norm_num [Nat.factorial])
      (by norm_num [Nat.factorial]) m
  · exact not_sq_of_between (k := 1904) (by norm_num [Nat.factorial])
      (by norm_num [Nat.factorial]) m
  · exact not_sq_of_between (k := 6317) (by norm_num [Nat.factorial])
      (by norm_num [Nat.factorial]) m
  · exact not_sq_of_between (k := 21886) (by norm_num [Nat.factorial])
      (by norm_num [Nat.factorial]) m
  · exact not_sq_of_between (k := 78911) (by norm_num [Nat.factorial])
      (by norm_num [Nat.factorial]) m
  · exact not_sq_of_between (k := 295259) (by norm_num [Nat.factorial])
      (by norm_num [Nat.factorial]) m
  · exact not_sq_of_between (k := 1143535) (by norm_num [Nat.factorial])
      (by norm_num [Nat.factorial]) m
  · exact not_sq_of_between (k := 4574143) (by norm_num [Nat.factorial])
      (by norm_num [Nat.factorial]) m
  · exact not_sq_of_between (k := 18859677) (by norm_num [Nat.factorial])
      (by norm_num [Nat.factorial]) m
  · exact not_sq_of_between (k := 80014834) (by norm_num [Nat.factorial])
      (by norm_num [Nat.factorial]) m
  · exact not_sq_of_between (k := 348776576) (by norm_num [Nat.factorial])
      (by norm_num [Nat.factorial]) m
  · exact not_sq_of_between (k := 1559776268) (by norm_num [Nat.factorial])
      (by norm_num [Nat.factorial]) m
  · exact not_sq_of_between (k := 7147792818) (by norm_num [Nat.factorial])
      (by norm_num [Nat.factorial]) m
  · exact not_sq_of_between (k := 33526120082) (by norm_num [Nat.factorial])
      (by norm_num [Nat.factorial]) m
  · exact not_sq_of_between (k := 160785623545) (by norm_num [Nat.factorial])
      (by norm_num [Nat.factorial]) m
  · exact not_sq_of_between (k := 787685471322) (by norm_num [Nat.factorial])
      (by norm_num [Nat.factorial]) m
  · exact not_sq_of_between (k := 3938427356614) (by norm_num [Nat.factorial])
      (by norm_num [Nat.factorial]) m
  · exact not_sq_of_between (k := 20082117944245) (by norm_num [Nat.factorial])
      (by norm_num [Nat.factorial]) m
  · exact not_sq_of_between (k := 104349745809073) (by norm_num [Nat.factorial])
      (by norm_num [Nat.factorial]) m
  · exact not_sq_of_between (k := 552166953567228) (by norm_num [Nat.factorial])
      (by norm_num [Nat.factorial]) m
  · exact not_sq_of_between (k := 2973510046012910) (by norm_num [Nat.factorial])
      (by norm_num [Nat.factorial]) m
  · exact not_sq_of_between (k := 16286585271694955) (by norm_num [Nat.factorial])
      (by norm_num [Nat.factorial]) m
  · exact not_sq_of_between (k := 90679869067935485) (by norm_num [Nat.factorial])
      (by norm_num [Nat.factorial]) m
  · exact not_sq_of_between (k := 512962802680363491) (by norm_num [Nat.factorial])
      (by norm_num [Nat.factorial]) m
  · exact not_sq_of_between (k := 2946746955341073478) (by norm_num [Nat.factorial])
      (by norm_num [Nat.factorial]) m
  · exact not_sq_of_between (k := 17182339742875652406) (by norm_num [Nat.factorial])
      (by norm_num [Nat.factorial]) m
  · exact not_sq_of_between (k := 101652092779175702171) (by norm_num [Nat.factorial])
      (by norm_num [Nat.factorial]) m
  · exact not_sq_of_between (k := 609912556675054213027) (by norm_num [Nat.factorial])
      (by norm_num [Nat.factorial]) m
  · exact not_sq_of_between (k := 3709953246501409085690) (by norm_num [Nat.factorial])
      (by norm_num [Nat.factorial]) m
  · exact not_sq_of_between (k := 22869687743093501007951) (by norm_num [Nat.factorial])
      (by norm_num [Nat.factorial]) m
  · exact not_sq_of_between (k := 142821154179615294686593) (by norm_num [Nat.factorial])
      (by norm_num [Nat.factorial]) m
  · exact not_sq_of_between (k := 903280290523322408635610) (by norm_num [Nat.factorial])
      (by norm_num [Nat.factorial]) m
  · exact not_sq_of_between (k := 5783815921445270815783609) (by norm_num [Nat.factorial])
      (by norm_num [Nat.factorial]) m
  · exact not_sq_of_between (k := 37483411234209726053065805) (by norm_num [Nat.factorial])
      (by norm_num [Nat.factorial]) m
  · exact not_sq_of_between (k := 245795164849461258960674062) (by norm_num [Nat.factorial])
      (by norm_num [Nat.factorial]) m
  · exact not_sq_of_between (k := 1630420674178430788228519563) (by norm_num [Nat.factorial])
      (by norm_num [Nat.factorial]) m
  · exact not_sq_of_between (k := 10937194378152021970306618007) (by norm_num [Nat.factorial])
      (by norm_num [Nat.factorial]) m
  · exact not_sq_of_between (k := 74179661362209580727623742159) (by norm_num [Nat.factorial])
      (by norm_num [Nat.factorial]) m
  · exact not_sq_of_between (k := 508550136674023695658451670185) (by norm_num [Nat.factorial])
      (by norm_num [Nat.factorial]) m
  · exact not_sq_of_between (k := 3523338699662022653505900576721) (by norm_num [Nat.factorial])
      (by norm_num [Nat.factorial]) m
  · exact not_sq_of_between (k := 24663370897634158574541304037050) (by norm_num [Nat.factorial])
      (by norm_num [Nat.factorial]) m
  · exact not_sq_of_between (k := 174396368086360611696209329639024) (by norm_num [Nat.factorial])
      (by norm_num [Nat.factorial]) m
  · exact not_sq_of_between (k := 1245439180886558699493562057691804) (by norm_num [Nat.factorial])
      (by norm_num [Nat.factorial]) m
  · exact not_sq_of_between (k := 8980989654316715588967781706572076) (by norm_num [Nat.factorial])
      (by norm_num [Nat.factorial]) m
  · exact not_sq_of_between (k := 65382591597917144387816492317568177) (by norm_num [Nat.factorial])
      (by norm_num [Nat.factorial]) m
  · exact not_sq_of_between (k := 480461962427038942460267525096444474) (by norm_num [Nat.factorial])
      (by norm_num [Nat.factorial]) m
  · exact not_sq_of_between (k := 3563201278858419461033351267854721464) (by norm_num [Nat.factorial])
      (by norm_num [Nat.factorial]) m
  · exact not_sq_of_between (k := 26664556771205919519070097139612996000) (by norm_num [Nat.factorial])
      (by norm_num [Nat.factorial]) m
  · exact not_sq_of_between (k := 201312988912482288333668455069536465757) (by norm_num [Nat.factorial])
      (by norm_num [Nat.factorial]) m
  · exact not_sq_of_between (k := 1533154046820761769413164705689608744377) (by norm_num [Nat.factorial])
      (by norm_num [Nat.factorial]) m
  · exact not_sq_of_between (k := 11776379687564843276211019969710858039009) (by norm_num [Nat.factorial])
      (by norm_num [Nat.factorial]) m
  · exact not_sq_of_between (k := 91219444817107882594696857529818207676198) (by norm_num [Nat.factorial])
      (by norm_num [Nat.factorial]) m
  · exact not_sq_of_between (k := 712446639319201784948673912308403605115342) (by norm_num [Nat.factorial])
      (by norm_num [Nat.factorial]) m
  · exact not_sq_of_between (k := 5609810447812647575362248801595614968784558) (by norm_num [Nat.factorial])
      (by norm_num [Nat.factorial]) m
  · exact not_sq_of_between (k := 44526490041372451122965980435912297622389065) (by norm_num [Nat.factorial])
      (by norm_num [Nat.factorial]) m
  · exact not_sq_of_between (k := 356211920330979608983727843487298380979112523) (by norm_num [Nat.factorial])
      (by norm_num [Nat.factorial]) m
  · exact not_sq_of_between (k := 2871872314724746021942727901945240734448707786) (by norm_num [Nat.factorial])
      (by norm_num [Nat.factorial]) m
  · exact not_sq_of_between (k := 23331200978034608323876057832648816217523382535) (by norm_num [Nat.factorial])
      (by norm_num [Nat.factorial]) m
  · exact not_sq_of_between (k := 190974110596668796970008672429388554580114244205) (by norm_num [Nat.factorial])
      (by norm_num [Nat.factorial]) m
  · exact not_sq_of_between (k := 1574812859496908794403637793960093262759360945119) (by norm_num [Nat.factorial])
      (by norm_num [Nat.factorial]) m
  · exact not_sq_of_between (k := 13081378078327271990661335578798848847474255303826) (by norm_num [Nat.factorial])
      (by norm_num [Nat.factorial]) m
  · exact not_sq_of_between (k := 109446661301155695857080695109221322834464193656741) (by norm_num [Nat.factorial])
      (by norm_num [Nat.factorial]) m
  · exact not_sq_of_between (k := 922213960297642814598347871007016379244405330655250) (by norm_num [Nat.factorial])
      (by norm_num [Nat.factorial]) m
  · exact not_sq_of_between (k := 7825244940376376925358096892704591704511772131306815) (by norm_num [Nat.factorial])
      (by norm_num [Nat.factorial]) m
  · exact not_sq_of_between (k := 66858922078602825324590583356376523422703411874063526) (by norm_num [Nat.factorial])
      (by norm_num [Nat.factorial]) m
  · exact not_sq_of_between (k := 575142194723999224356836312510183507170717503745407529) (by norm_num [Nat.factorial])
      (by norm_num [Nat.factorial]) m
  · exact not_sq_of_between (k := 4980877514193196669713282991946078429827937232372941867) (by norm_num [Nat.factorial])
      (by norm_num [Nat.factorial]) m
  · exact not_sq_of_between (k := 43422283469044442400520987277954690033900570230313299933) (by norm_num [Nat.factorial])
      (by norm_num [Nat.factorial]) m
  · exact not_sq_of_between (k := 381028991060110634246276414878912279469899189376847948137) (by norm_num [Nat.factorial])
      (by norm_num [Nat.factorial]) m
  · exact not_sq_of_between (k := 3365156932181068109459677272856044111292549448241189337343) (by norm_num [Nat.factorial])
      (by norm_num [Nat.factorial]) m
  · exact not_sq_of_between (k := 29910169058002623210200515287548862104836069367192860122492) (by norm_num [Nat.factorial])
      (by norm_num [Nat.factorial]) m
  · exact not_sq_of_between (k := 267524684928818862621490012042605003730753817304274266583374) (by norm_num [Nat.factorial])
      (by norm_num [Nat.factorial]) m
  · exact not_sq_of_between (k := 2407722164359369763593410108383445033576784355738468399250368) (by norm_num [Nat.factorial])
      (by norm_num [Nat.factorial]) m
  · exact not_sq_of_between (k := 21802851503903891305843592056331800458090082265244558375673041) (by norm_num [Nat.factorial])
      (by norm_num [Nat.factorial]) m
  · exact not_sq_of_between (k := 198633430462262788036763464177703883166690275063913206990548481) (by norm_num [Nat.factorial])
      (by norm_num [Nat.factorial]) m
  · exact not_sq_of_between (k := 1820505461284132832359203813645046756110583331925714370170257092) (by norm_num [Nat.factorial])
      (by norm_num [Nat.factorial]) m
  · exact not_sq_of_between (k := 16784231035053557904028966906346483792025484094796637394973403970) (by norm_num [Nat.factorial])
      (by norm_num [Nat.factorial]) m
  · exact not_sq_of_between (k := 155650555359345674201535001388480503193835670087005087695666582899) (by norm_num [Nat.factorial])
      (by norm_num [Nat.factorial]) m
  · exact not_sq_of_between (k := 1451811729660401840498379775717372701145990271033308799231637667601) (by norm_num [Nat.factorial])
      (by norm_num [Nat.factorial]) m
  · exact not_sq_of_between (k := 13619201234191322393627253212934023042404388731461906952430812397994) (by norm_num [Nat.factorial])
      (by norm_num [Nat.factorial]) m
  · exact not_sq_of_between (k := 128483287477042947436606854413089420338280480054241478815100633956558) (by norm_num [Nat.factorial])
      (by norm_num [Nat.factorial]) m
  · exact not_sq_of_between (k := 1218899489080933816973227253068021382231629321448981884930371490328689) (by norm_num [Nat.factorial])
      (by norm_num [Nat.factorial]) m
  · exact not_sq_of_between (k := 11627560052213890684239693812535151882288553865765313903995958273943586) (by norm_num [Nat.factorial])
      (by norm_num [Nat.factorial]) m
  · exact not_sq_of_between (k := 111527638075238136262755547542307772029800712447380847367329167783382104) (by norm_num [Nat.factorial])
      (by norm_num [Nat.factorial]) m
  · exact not_sq_of_between (k := 1075533591796017115343430456551200439746548977577162936545074776552498754) (by norm_num [Nat.factorial])
      (by norm_num [Nat.factorial]) m
  · exact not_sq_of_between (k := 10427685057848376925507942191442630012584828624363222101172323570579332599) (by norm_num [Nat.factorial])
      (by norm_num [Nat.factorial]) m
  · exact not_sq_of_between (k := 101636501751285493870798488028947073709983082260934656117721845292980988580) (by norm_num [Nat.factorial])
      (by norm_num [Nat.factorial]) m
  · exact not_sq_of_between (k := 995830274128553338795685900500337369492022050359737013283228306377142743139) (by norm_num [Nat.factorial])
      (by norm_num [Nat.factorial]) m
  · exact not_sq_of_between (k := 9807790764615756210934052418079289148346460527555220609613824741800936687334) (by norm_num [Nat.factorial])
      (by norm_num [Nat.factorial]) m
  · exact not_sq_of_between (k := 97092175013660332284448160034192795594426266264944604365617979012105653222056) (by norm_num [Nat.factorial])
      (by norm_num [Nat.factorial]) m
  · exact not_sq_of_between (k := 966054943799492973133000870362309068674974070396662776244736194062917963496762) (by norm_num [Nat.factorial])
      (by norm_num [Nat.factorial]) m
  · exact not_sq_of_between (k := 9660549437994929731330008703623090686749740703966627762447361940629179634967623) (by norm_num [Nat.factorial])
      (by norm_num [Nat.factorial]) m
  · exact not_sq_of_between (k := 97087320283538361860527309219842556706614048406497393159303888737041105661341886) (by norm_num [Nat.factorial])
      (by norm_num [Nat.factorial]) m
  · exact not_sq_of_between (k := 980533870655936423948625541326149462775640364901662691744776797397063645922018558) (by norm_num [Nat.factorial])
      (by norm_num [Nat.factorial]) m
  · exact not_sq_of_between (k := 9951331929187258502732236960185323062286269196016882430577798916700031964531492841) (by norm_num [Nat.factorial])
      (by norm_num [Nat.factorial]) m
  · exact not_sq_of_between (k := 101484071386329527885209097242248445236636861390059750092770501250120539741035912275) (by norm_num [Nat.factorial])
      (by norm_num [Nat.factorial]) m
  · exact not_sq_of_between (k := 1039902283024847917130442479668355681880681037149513624575745076720460749316250325718) (by norm_num [Nat.factorial])
      (by norm_num [Nat.factorial]) m
  · exact not_sq_of_between (k := 10706449288791818466268336278478032542357250736600016133856467330324429824323778312632) (by norm_num [Nat.factorial])
      (by norm_num [Nat.factorial]) m
  · exact not_sq_of_between (k := 110748372592834877256996271322478239333596957884433122790811629506376644324689283182593) (by norm_num [Nat.factorial])
      (by norm_num [Nat.factorial]) m
  · exact not_sq_of_between (k := 1150930849118151396203444749571140056142251512738730748889046422484306994948185555067062) (by norm_num [Nat.factorial])
      (by norm_num [Nat.factorial]) m
  · exact not_sq_of_between (k := 12016070835354182374265387937522069627669489723001090285796577272391092565383658077767525) (by norm_num [Nat.factorial])
      (by norm_num [Nat.factorial]) m
  · exact not_sq_of_between (k := 126025614123587707293295876079117512537385342131235696615275004912895251195083773777278713) (by norm_num [Nat.factorial])
      (by norm_num [Nat.factorial]) m
  · exact not_sq_of_between (k := 1327762234396747957102518441431304475318248542810307723245281586507737091174592866966317021) (by norm_num [Nat.factorial])
      (by norm_num [Nat.factorial]) m
  · exact not_sq_of_between (k := 14051714689748984593623962505239079868348052594780832925663847484470244491394851109614402124) (by norm_num [Nat.factorial])
      (by norm_num [Nat.factorial]) m
  · exact not_sq_of_between (k := 149371776070977131787360943527332592927665828376130329195744662120431138890413125151274108025) (by norm_num [Nat.factorial])
      (by norm_num [Nat.factorial]) m
  · exact not_sq_of_between (k := 1594854141754720953366019534553668567051878399708964981408759120209126426332307816057926729278) (by norm_num [Nat.factorial])
      (by norm_num [Nat.factorial]) m
  · exact not_sq_of_between (k := 17102905289724946876810411380732062891250259623212799140339105513258487281478468744088870539836) (by norm_num [Nat.factorial])
      (by norm_num [Nat.factorial]) m
  · exact not_sq_of_between (k := 184203927331962664677022195613714175289873806750604681693578915410549137313659497763356116645156) (by norm_num [Nat.factorial])
      (by norm_num [Nat.factorial]) m
  · exact not_sq_of_between (k := 1992470115411701951733529798121321620988521552635057139913674325787109866466242825099576545023806) (by norm_num [Nat.factorial])
      (by norm_num [Nat.factorial]) m
  · exact not_sq_of_between (k := 21643765498993678240886932377778118080730791109571219221465841941270509626237168436808252299687104) (by norm_num [Nat.factorial])
      (by norm_num [Nat.factorial]) m
  · exact not_sq_of_between (k := 236105606905206846282664890558362403647951978515981481952412322048434952117837438819546766063940584) (by norm_num [Nat.factorial])
      (by norm_num [Nat.factorial]) m
  · exact not_sq_of_between (k := 2586407337108586045310991770677553531245102834944805618026162911581903627374073073000747058630903971) (by norm_num [Nat.factorial])
      (by norm_num [Nat.factorial]) m
  · exact not_sq_of_between (k := 28450480708194446498420909477453088843696131184392861798287792027400939901114803803008217644939943684) (by norm_num [Nat.factorial])
      (by norm_num [Nat.factorial]) m
  · exact not_sq_of_between (k := 314245830534529150853639626024900715446450496615794609384389709639185275103382116559145270275525398121) (by norm_num [Nat.factorial])
      (by norm_num [Nat.factorial]) m
  · exact not_sq_of_between (k := 3485154855530142677187466320446441357981127778882352371947192897165646416292211396888877799429663403919) (by norm_num [Nat.factorial])
      (by norm_num [Nat.factorial]) m
  · exact not_sq_of_between (k := 38809042007129483893781565406865620834798797710240359699213981355783156401686990286633697030906986434922) (by norm_num [Nat.factorial])
      (by norm_num [Nat.factorial]) m
  · exact not_sq_of_between (k := 433898280347932019750481702625682793859075389113838895819077693640544086702009849212692471607705240138022) (by norm_num [Nat.factorial])
      (by norm_num [Nat.factorial]) m
  · exact not_sq_of_between (k := 4870496117317050983460516300138638445936066639921665763111864864036446435669658599725141682550247577916338) (by norm_num [Nat.factorial])
      (by norm_num [Nat.factorial]) m
  · exact not_sq_of_between (k := 54887703709097355030423828870959689537912082325570463956237729988887076289282989288176887203138202686949856) (by norm_num [Nat.factorial])
      (by norm_num [Nat.factorial]) m
  · exact not_sq_of_between (k := 620983479943372102050500882162988260350351194250463657930138001878476335551284905635722956448403671923272107) (by norm_num [Nat.factorial])
      (by norm_num [Nat.factorial]) m
  · exact not_sq_of_between (k := 7053016533709025299147106410823449994087596725083025726973329408654878990302885536026379940569044048063893445) (by norm_num [Nat.factorial])
      (by norm_num [Nat.factorial]) m
  · exact not_sq_of_between (k := 80416761245529365527558583584154874873680620857944080101802405531450793299978593077470566506891983141786013456) (by norm_num [Nat.factorial])
      (by norm_num [Nat.factorial]) m
  · exact not_sq_of_between (k := 920411901861271050295051027235109192713260449490524894719849952957721563028226802209569651348762810430819566655) (by norm_num [Nat.factorial])
      (by norm_num [Nat.factorial]) m
  · exact not_sq_of_between (k := 10574727661722567063350219192305795274610739722873029027064410422448881379480321569656480996441145916379536351532) (by norm_num [Nat.factorial])
      (by norm_num [Nat.factorial]) m
  · exact not_sq_of_between (k := 121953708680412246366972638116354683210692919041731538335203296601774788492007266000185472804948064523527708686363) (by norm_num [Nat.factorial])
      (by norm_num [Nat.factorial]) m
  · exact not_sq_of_between (k := 1411716241374844733261383376026893350927793956180091378216941282577143578644654477019631090239086591879244668169946) (by norm_num [Nat.factorial])
      (by norm_num [Nat.factorial]) m
  · exact not_sq_of_between (k := 16402660477245910742400301105783541143311316441035185234164439875286353894417922378067569712581067640206608755635390) (by norm_num [Nat.factorial])
      (by norm_num [Nat.factorial]) m
  · exact not_sq_of_between (k := 191286248380602327544317614701311153829489188058551938933232891978200393441706467817780853408389322225233074235305621) (by norm_num [Nat.factorial])
      (by norm_num [Nat.factorial]) m
  · exact not_sq_of_between (k := 2238948134342328096314386925093911468024426305814106970632478024237274821221382019803795248797939114480986183789934919) (by norm_num [Nat.factorial])
      (by norm_num [Nat.factorial]) m
  · exact not_sq_of_between (k := 26301685255168514566877540394174280275650359902111021706369915671965828989969065685640608344396557858026843807441046915) (by norm_num [Nat.factorial])
      (by norm_num [Nat.factorial]) m
  · exact not_sq_of_between (k := 310092295888515892103206668865055255699981302077534368600155843030927279835722383750028506599529595435985925743636819744) (by norm_num [Nat.factorial])
      (by norm_num [Nat.factorial]) m
  · exact not_sq_of_between (k := 3669061525201986116986042564043201249662887058951344624741587056124025872191594052231344641973375143704409198931927446625) (by norm_num [Nat.factorial])
      (by norm_num [Nat.factorial]) m
  · exact not_sq_of_between (k := 43567691688637475591797527491957656843625867559506379997327724626650657179733050998683257189962751872145927880822561812860) (by norm_num [Nat.factorial])
      (by norm_num [Nat.factorial]) m
  · exact not_sq_of_between (k := 519168964585534790669805677866941861724525489636345037042525780604373672243586793289412792839959190577891507749791445310426) (by norm_num [Nat.factorial])
      (by norm_num [Nat.factorial]) m
  · exact not_sq_of_between (k := 6208357848239800658568461517030403541540348669723511459510131092377601583132560440574341633889190923631632023573844103401297) (by norm_num [Nat.factorial])
      (by norm_num [Nat.factorial]) m
  · exact not_sq_of_between (k := 74500294178877607902821538204364842498484184036682137514121573108531218997590725286892099606670291083579584282886129240815564) (by norm_num [Nat.factorial])
      (by norm_num [Nat.factorial]) m
  · exact not_sq_of_between (k := 897102338502803811794374820046926007295111348643549607832559709145227808897672222303246240972613115479519100334524335032445013) (by norm_num [Nat.factorial])
      (by norm_num [Nat.factorial]) m
  · exact not_sq_of_between (k := 10839728799148578440176054427271218996191720524198523792538121616345218523611891649234883764651374415242858382120983091362930336) (by norm_num [Nat.factorial])
      (by norm_num [Nat.factorial]) m
  · exact not_sq_of_between (k := 131424727142750382474286269190923203841500326384006987785611252350912451307453702011697956519506894801186429400911741017331695305) (by norm_num [Nat.factorial])
      (by norm_num [Nat.factorial]) m
  · exact not_sq_of_between (k := 1598850811637178857826273172811982862963507742863057186417525409150432264729960649383609813475485299408187547556008689215101638519) (by norm_num [Nat.factorial])
      (by norm_num [Nat.factorial]) m
  · exact not_sq_of_between (k := 19516461353510194489901061367198238556022303763746537281997571445472836477676841916847932010513776105098409331863863764475049181135) (by norm_num [Nat.factorial])
      (by norm_num [Nat.factorial]) m
  · exact not_sq_of_between (k := 239026859504237610909102395888679607568840426470595308508788933821499178187866901887662192081798769842566729270704183990506171508910) (by norm_num [Nat.factorial])
      (by norm_num [Nat.factorial]) m
  · exact not_sq_of_between (k := 2937211223973046244838682756175334448615662796145335651885649320952815581658707155498398803352345084705474891040315166289609998001760) (by norm_num [Nat.factorial])
      (by norm_num [Nat.factorial]) m
  · exact not_sq_of_between (k := 36212371997474185695435042660745506476881293493994481381444228435145747433418137362481670428850427086538861440086979561349683781078032) (by norm_num [Nat.factorial])
      (by norm_num [Nat.factorial]) m
  · exact not_sq_of_between (k := 447922304099235763294320277900590271557394355758549178403300790651278672352622531414876243040586448295734384083122798745658940805213138) (by norm_num [Nat.factorial])
      (by norm_num [Nat.factorial]) m
  · exact not_sq_of_between (k := 5558569612631788285966912369158919837806880181038859968277247105104348374980334837800521280577485470642368466794393677772271641492391532) (by norm_num [Nat.factorial])
      (by norm_num [Nat.factorial]) m
  · exact not_sq_of_between (k := 69203633585696884824637272625402513392874630644936370231273179185942758977213062732693871987407606198315292985131300177063266337892060993) (by norm_num [Nat.factorial])
      (by norm_num [Nat.factorial]) m
  · exact not_sq_of_between (k := 864353106449146421246647564875621885932209128058697353200406994622817018428979186816339028675511266863819570328222119051052393953365605947) (by norm_num [Nat.factorial])
      (by norm_num [Nat.factorial]) m
  · exact not_sq_of_between (k := 10830313381552790636645670561098624720160005216473709632667326245492885470339774387206596072848335819317386351714421258096454094416386080930) (by norm_num [Nat.factorial])
      (by norm_num [Nat.factorial]) m
  · exact not_sq_of_between (k := 136134928269483243465684570758084065663363648273732059723871902964209713421115441816127930767563582313110068231835317485301599339668709734608) (by norm_num [Nat.factorial])
      (by norm_num [Nat.factorial]) m
  · exact not_sq_of_between (k := 1716596129698257919995803329844963543705422147374125234525902127171686190177001850300021916640667903354760498844030070644749843361175005160089) (by norm_num [Nat.factorial])
      (by norm_num [Nat.factorial]) m
  · exact not_sq_of_between (k := 21713414369905211483805099426041855319293309172244568292709871196293633291081389002104345594447893688047337938740007681887745266115773534265786) (by norm_num [Nat.factorial])
      (by norm_num [Nat.factorial]) m
  · exact not_sq_of_between (k := 275512341900453140645224177474357530163091238945368028614199663374232663440231350339138734173462608133623327214613489349651612663387917026274676) (by norm_num [Nat.factorial])
      (by norm_num [Nat.factorial]) m
  · exact not_sq_of_between (k := 3506699614651145784835079183347611725310973269608482393247621075003012275553845214019030558731877494679102065941123955162920117689862555660347744) (by norm_num [Nat.factorial])
      (by norm_num [Nat.factorial]) m
  · exact not_sq_of_between (k := 44770543625751324772126074050193560618338376223204406558958307191363601511377007569789622312342768724127475020433092891846527452368820393001697645) (by norm_num [Nat.factorial])
      (by norm_num [Nat.factorial]) m
  · exact not_sq_of_between (k := 573342706026186071970057748322687838569048868177958833956127174959466308251648266359214123562674844828421194147242737273027004975316586465285522919) (by norm_num [Nat.factorial])
      (by norm_num [Nat.factorial]) m
  · exact not_sq_of_between (k := 7364720406187589125010006555183433705721684063722444511257596158142781114187512798639714528256867186946921501463860281839308981344766641856168151140) (by norm_num [Nat.factorial])
      (by norm_num [Nat.factorial]) m
  · exact not_sq_of_between (k := 94887784808048066090006826441395645761459414945312667389906729959453109157101805918807313352950556445450047615021313211533043768016305915945997261046) (by norm_num [Nat.factorial])
      (by norm_num [Nat.factorial]) m
  · exact not_sq_of_between (k := 1226220418548394194126224994766288531738205575853624240772712304167517925758025610256778559790666484301589703490584366807561876826827526533287464377673) (by norm_num [Nat.factorial])
      (by norm_num [Nat.factorial]) m
  · exact not_sq_of_between (k := 15893633143410597759090144377235304683006224029288507051956327646350084030520598592640114022070838973482610535362790941524531118052024247835096339559916) (by norm_num [Nat.factorial])
      (by norm_num [Nat.factorial]) m
  · exact not_sq_of_between (k := 206617230864337770868171876904058960879080912380750591675432259402551092396767781704321482286920906655273936959716282239818904534676315221856252414278909) (by norm_num [Nat.factorial])
      (by norm_num [Nat.factorial]) m
  · exact not_sq_of_between (k := 2693959096814203481642952328926110336280735408917513770582427906090997631258351335936816295581871606354139230541757250806163673550764852380621692685195257) (by norm_num [Nat.factorial])
      (by norm_num [Nat.factorial]) m
  · exact not_sq_of_between (k := 35228086383135655973928155584877282549111834352747660040119596101914343069798317468255467097390285322507526931261087944011867010920914967175640652931016572) (by norm_num [Nat.factorial])
      (by norm_num [Nat.factorial]) m
  · exact not_sq_of_between (k := 462012021572424958939977707342271428207953534175231687445940165881059776285530033117056713105739006506722295654218700689346055987042055611142710927953446124) (by norm_num [Nat.factorial])
      (by norm_num [Nat.factorial]) m
  · exact not_sq_of_between (k := 6076819373438453926104322336741575209237435813642070994485382669219163305636133875852118907382497065552354584987730461663020001424605286500075636397055149499) (by norm_num [Nat.factorial])
      (by norm_num [Nat.factorial]) m
  · exact not_sq_of_between (k := 80158752880437609345489551512266626875006699401714805242465198406836786164223823165995478160871878658021252691506840823381882187130448146573388082053618273690) (by norm_num [Nat.factorial])
      (by norm_num [Nat.factorial]) m
  · exact not_sq_of_between (k := 1060400627633601661809776953665500467396095454762217763127161303514353969322180815085412861572227003610865152874296779457562971459907175726147086371950901309800) (by norm_num [Nat.factorial])
      (by norm_num [Nat.factorial]) m
  · exact not_sq_of_between (k := 14067804037272114126423458051729070556346415549778313991619185506418448291953371386332344633410997511009513744693583959535416982273348380774692125196119172573435) (by norm_num [Nat.factorial])
      (by norm_num [Nat.factorial]) m
  · exact not_sq_of_between (k := 187159959783878074275664907253097650412623788672348368711555345413941599322478565003995743920927065769990950067494704379111009825549181787379518873671094261200977) (by norm_num [Nat.factorial])
      (by norm_num [Nat.factorial]) m
  · exact not_sq_of_between (k := 2497025309691895922670032230762658108482040015376643456576220128740008099011508507130889445078177417139223544082696882676335019921641097462056181631394407176449588) (by norm_num [Nat.factorial])
      (by norm_num [Nat.factorial]) m
  · exact not_sq_of_between (k := 33407921756767535640181527034166841028349916526386417821347415860897147096489705642470137495253695115658101753553559529337825955866959336388940790308478560643436108) (by norm_num [Nat.factorial])
      (by norm_num [Nat.factorial]) m
  · exact not_sq_of_between (k := 448214304210758427304154289349438467104175126625221949805926263336779326155911230476038183963317562557354163430843982502721423437836237545870613877445493026688260964) (by norm_num [Nat.factorial])
      (by norm_num [Nat.factorial]) m
  · exact not_sq_of_between (k := 6030106741372270952207478205630409695742165778986790280059202508919999729862470764908192624623155055578838568742991367882717409454128437496363693670715801957987935754) (by norm_num [Nat.factorial])
      (by norm_num [Nat.factorial]) m
  · exact not_sq_of_between (k := 81350587526129656707252003438023450028086628146134657595823123854399804911132561993422102531089794318081763159587732267270701123688227059291274929750182270631440692424) (by norm_num [Nat.factorial])
      (by norm_num [Nat.factorial]) m
  · exact not_sq_of_between (k := 1100490350082592148202366690037454308402666122472017556349704894123487870335480106288311375029954371571630177744457827993003270979158335570754180875393235469294441627115) (by norm_num [Nat.factorial])
      (by norm_num [Nat.factorial]) m
  · exact not_sq_of_between (k := 14927777395010375262653279165182950649781322687435461204222647424150144132518334871953167374759669084927302268776670321750869890314697751275936506906993376869798594538874) (by norm_num [Nat.factorial])
      (by norm_num [Nat.factorial]) m
  · exact not_sq_of_between (k := 203039723999201220030240045513462039012980282624467612268520918998418986177384322082205376192115830711911756592544176049073573401925393981891958867517947270462810779846220) (by norm_num [Nat.factorial])
      (by norm_num [Nat.factorial]) m
  · exact not_sq_of_between (k := 2769092647606965906005980118838559591419134276235002459191130634785282457574501786111800552585320552206502489984851665137870430627008145970556300021858468938891865681804378) (by norm_num [Nat.factorial])
      (by norm_num [Nat.factorial]) m
  · exact not_sq_of_between (k := 37866772440000597724066433890380333043369924085733888977558036871013207231228616840258754521797137891428521352764866277497901396602764932606809302223142229654336497611276848) (by norm_num [Nat.factorial])
      (by norm_num [Nat.factorial]) m
  · exact not_sq_of_between (k := 519203025361259136814182783350992047812208924278897481680746889547955218433627690319266899480947926151756647633259198115202347023167723339501256970639048286934099891757633306) (by norm_num [Nat.factorial])
      (by norm_num [Nat.factorial]) m
  · exact not_sq_of_between (k := 7137861494304140138345803754988983333800245993715836487113608150581180947495802984872708941776927808546968319589619021077113029754372607379484512686212069420814881814338723554) (by norm_num [Nat.factorial])
      (by norm_num [Nat.factorial]) m
  · exact not_sq_of_between (k := 98388630823155828465839134955600811242363083889481039315923661254313005803192855884631617055967845805506151607055601754754527955666842180062415293172115111429219757080706996024) (by norm_num [Nat.factorial])
      (by norm_num [Nat.factorial]) m
  · exact not_sq_of_between (k := 1359757931020721271975846196840175397103274466828300240411107590043974403801306518967722164525183067644914539849646187148300104953497887258660521262878258404974125919477561420233) (by norm_num [Nat.factorial])
      (by norm_num [Nat.factorial]) m
  · exact not_sq_of_between (k := 18841358580181008195995031039236132684290288313771993765021970160836461718099196393417912299372807709978075156783335546145871968571586653821929106884568323091582918029251342849248) (by norm_num [Nat.factorial])
      (by norm_num [Nat.factorial]) m
  · exact not_sq_of_between (k := 261752518760304149878770573680263207749919228256610395671433280319266302252124020113761324099928975503598342756011002756561679664940964156881601653375644777421349521581984887631307) (by norm_num [Nat.factorial])
      (by norm_num [Nat.factorial]) m
  · exact not_sq_of_between (k := 3645790713824436594722330653035675299856723081830513881683687027074081480527610715254868493180105267807804276613523377395643937921224789164109260422495293674444583572391644708346741) (by norm_num [Nat.factorial])
      (by norm_num [Nat.factorial]) m
  · exact not_sq_of_between (k := 50910696677188149744576242790933521058075684435229427131887652133816565341280197748948393888302947609852678795210915986885251950174015822901268982650880386995188211557974272972793782) (by norm_num [Nat.factorial])
      (by norm_num [Nat.factorial]) m
  · exact not_sq_of_between (k := 712749753480634096424067399073069294813059582093211979846427129873431914777922768485277514436241266537937503132952823816393527302436221520617765757112325417932634961811639821619112951) (by norm_num [Nat.factorial])
      (by norm_num [Nat.factorial]) m
  · exact not_sq_of_between (k := 10003919511075687439239842079877268407403200530310257500607372769012122211475611469468106961822091119454445526015650216524401341228323481397242553653388962485934463488581214128081549685) (by norm_num [Nat.factorial])
      (by norm_num [Nat.factorial]) m
  · exact not_sq_of_between (k := 140767625204263507181053139308211353416389626451229228229768326058173089941211310619919674616629600017648172502216645201009247056830730026433520743102806916415625352455634714077281801115) (by norm_num [Nat.factorial])
      (by norm_num [Nat.factorial]) m
  · exact not_sq_of_between (k := 1985771723241106210148124831841241194325708743740727557371956368105307468376502902737710723020671618633896882983370244492889499860796022758220260598370946533099864984325241534141671911551) (by norm_num [Nat.factorial])
      (by norm_num [Nat.factorial]) m
  · exact not_sq_of_between (k := 28083053027845645962655542024840215459780668143793671276126114133334476200709161144991477678742178649423370174077063921842590153852083862678565168456160342383791151833029688044250792326939) (by norm_num [Nat.factorial])
      (by norm_num [Nat.factorial]) m

/-- The three known solutions of Brocard's equation. -/
