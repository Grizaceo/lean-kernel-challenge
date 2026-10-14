import Spec

namespace Submission

set_option maxRecDepth 100000

/-! ### Part 1: Reference Möbius & Mertens equivalence to `mertensSpec` -/

def moebiusByFactors (n : Nat) : Int :=
  if n = 0 then 0
  else if n.primeFactorsList.Nodup then (-1 : Int) ^ n.primeFactorsList.length else 0

theorem moebiusByFactors_eq (n : Nat) : moebiusByFactors n = ArithmeticFunction.moebius n := by
  by_cases hn : n = 0
  · subst n
    simp [moebiusByFactors]
  · simp only [moebiusByFactors, if_neg hn, ArithmeticFunction.moebius, ArithmeticFunction.coe_mk,
      ← Nat.squarefree_iff_nodup_primeFactorsList hn, ArithmeticFunction.cardFactors_apply]

def implOld (n : Nat) : Int := ∑ k ∈ Finset.range (n + 1), moebiusByFactors k

theorem implOld_correct (n : Nat) : implOld n = mertensSpec n := by
  simp only [implOld, mertensSpec, moebiusByFactors_eq]

def mertensRec : Nat → Int
  | 0 => 0
  | n + 1 => mertensRec n + moebiusByFactors (n + 1)

theorem mertensRec_eq_implOld : ∀ n, mertensRec n = implOld n
  | 0 => by simp [mertensRec, implOld, moebiusByFactors]
  | n + 1 => by
    unfold mertensRec
    rw [mertensRec_eq_implOld n]
    unfold implOld
    rw [Finset.sum_range_succ (f := moebiusByFactors) (n + 1)]

/-! ### Part 2: Fast trial-division `findDiv` & `factorsFast` = `Nat.primeFactorsList` -/

def findDiv (n : Nat) : Nat → Nat → Nat
  | 0, _ => n
  | fuel + 1, d =>
    if d * d ≤ n then
      if n % d == 0 then d else findDiv n fuel (d + 1)
    else n

theorem findDiv_spec (n : Nat) (hn : 2 ≤ n) : ∀ fuel d,
    2 ≤ d → n < d + fuel → (∀ m, 2 ≤ m → m < d → ¬ (m ∣ n)) →
    let p := findDiv n fuel d
    2 ≤ p ∧ p ∣ n ∧ (∀ m, 2 ≤ m → m < p → ¬ (m ∣ n))
  | 0, d, _, hlt, hno => by
    rw [findDiv]
    exact ⟨hn, Nat.dvd_refl n, fun m hm2 hmn => hno m hm2 (by omega)⟩
  | fuel + 1, d, hd2, hlt, hno => by
    rw [findDiv]
    by_cases hsq : d * d ≤ n
    · rw [if_pos hsq]
      by_cases hmod : (n % d == 0) = true
      · rw [if_pos hmod]
        have hdvd : d ∣ n := Nat.dvd_of_mod_eq_zero (beq_iff_eq.mp hmod)
        exact ⟨hd2, hdvd, hno⟩
      · rw [if_neg hmod]
        have hndvd : ¬ (d ∣ n) := by
          intro hdvd
          have : (n % d == 0) = true := beq_iff_eq.mpr (Nat.mod_eq_zero_of_dvd hdvd)
          exact hmod this
        apply findDiv_spec n hn fuel (d + 1) (by omega) (by omega)
        intro m hm2 hmd
        by_cases hmeq : m = d
        · subst hmeq; exact hndvd
        · exact hno m hm2 (by omega)
    · rw [if_neg hsq]
      refine ⟨hn, Nat.dvd_refl n, ?_⟩
      intro m hm2 hmn hm_dvd
      by_cases hmd : m < d
      · exact hno m hm2 hmd hm_dvd
      · have hpe : m * (n / m) = n := Nat.mul_div_cancel' hm_dvd
        have hq2 : 2 ≤ n / m := by
          have h1 : m * 1 < m * (n / m) := by rw [hpe]; omega
          have := Nat.lt_of_mul_lt_mul_left h1; omega
        have hqd : n / m < d := by
          by_contra hge
          have h1 : d ≤ m := by omega
          have h2 : d ≤ n / m := by omega
          have h3 : d * d ≤ m * (n / m) := Nat.mul_le_mul h1 h2
          omega
        have hq_dvd : (n / m) ∣ n := ⟨m, by rw [Nat.mul_comm, hpe]⟩
        exact hno (n / m) hq2 hqd hq_dvd

theorem findDiv_eq_minFac (n : Nat) (hn : 2 ≤ n) : findDiv n n 2 = n.minFac := by
  have ⟨hp2, hpdvd, hpmin⟩ := findDiv_spec n hn n 2 (by omega) (by omega) (by intro m hm1 hm2; omega)
  have hm_prime : Nat.Prime n.minFac := Nat.minFac_prime (by omega)
  have hm2 : 2 ≤ n.minFac := hm_prime.two_le
  have hmdvd : n.minFac ∣ n := Nat.minFac_dvd n
  have hle1 : n.minFac ≤ findDiv n n 2 := Nat.minFac_le_of_dvd hp2 hpdvd
  have hle2 : findDiv n n 2 ≤ n.minFac := by
    by_contra hlt
    exact hpmin n.minFac hm2 (by omega) hmdvd
  omega

def factorsFast : Nat → Nat → List Nat
  | 0, _ => []
  | fuel + 1, n =>
    if n < 2 then []
    else
      let p := findDiv n n 2
      p :: factorsFast fuel (n / p)

theorem factorsFast_eq : ∀ fuel n, n ≤ fuel → factorsFast fuel n = n.primeFactorsList
  | 0, n, hn => by
    have hn0 : n = 0 := by omega
    subst hn0; simp [factorsFast, Nat.primeFactorsList_zero]
  | fuel + 1, n, hn => by
    rw [factorsFast]
    by_cases hn2 : n < 2
    · rw [if_pos hn2]
      rcases (by omega : n = 0 ∨ n = 1) with rfl | rfl
      · simp [Nat.primeFactorsList_zero]
      · simp [Nat.primeFactorsList_one]
    · rw [if_neg hn2]
      have hge2 : 2 ≤ n := by omega
      dsimp only
      rw [findDiv_eq_minFac n hge2]
      have hm2 : 2 ≤ n.minFac := (Nat.minFac_prime (by omega)).two_le
      have hdiv_lt : n / n.minFac < n := Nat.div_lt_self (by omega) hm2
      rw [factorsFast_eq fuel (n / n.minFac) (by omega)]
      have hadd : n = (n - 2) + 2 := by omega
      conv => rhs; rw [hadd, Nat.primeFactorsList_add_two]
      rw [← hadd]

def memFast (x : Nat) : List Nat → Bool
  | [] => false
  | y :: ys => (x == y) || memFast x ys

def nodupFast : List Nat → Bool
  | [] => true
  | x :: xs => !memFast x xs && nodupFast xs

theorem memFast_eq (x : Nat) : ∀ l, memFast x l = decide (x ∈ l)
  | [] => rfl
  | y :: ys => by
    simp only [memFast, List.mem_cons, memFast_eq x ys]
    by_cases h : x = y
    · subst h; simp
    · have hb : (x == y) = false := beq_false_of_ne h
      simp [h, hb]

theorem nodupFast_eq : ∀ l, nodupFast l = decide l.Nodup
  | [] => rfl
  | x :: xs => by
    simp [nodupFast, List.nodup_cons, memFast_eq, nodupFast_eq xs]

theorem neg_one_pow_eq : ∀ L : Nat, ((-1 : Int) ^ L) = (if L % 2 == 0 then 1 else -1)
  | 0 => rfl
  | L + 1 => by
    rw [pow_succ, neg_one_pow_eq L]
    by_cases h : (L % 2 == 0) = true
    · have h0 : L % 2 = 0 := beq_iff_eq.mp h
      have h1 : (L + 1) % 2 = 1 := by omega
      have hb : ((L + 1) % 2 == 0) = false := by rw [h1]; rfl
      rw [if_pos h, if_neg (by simp [hb])]; norm_num
    · have h0 : L % 2 ≠ 0 := by intro heq; exact h (beq_iff_eq.mpr heq)
      have h1 : (L + 1) % 2 = 0 := by omega
      have hb : ((L + 1) % 2 == 0) = true := beq_iff_eq.mpr h1
      rw [if_neg h, if_pos hb]; norm_num

def isMuPos (n : Nat) : Bool :=
  !(n == 0) && nodupFast (factorsFast n n) && ((factorsFast n n).length % 2 == 0)

def isMuNeg (n : Nat) : Bool :=
  !(n == 0) && nodupFast (factorsFast n n) && !((factorsFast n n).length % 2 == 0)

theorem moebius_split (n : Nat) :
    moebiusByFactors n =
      (Int.ofNat (if isMuPos n then 1 else 0)) - (Int.ofNat (if isMuNeg n then 1 else 0)) := by
  unfold moebiusByFactors isMuPos isMuNeg
  rw [factorsFast_eq n n (Nat.le_refl n), nodupFast_eq, neg_one_pow_eq]
  by_cases hn : n = 0
  · subst hn; rfl
  · have hnb : (n == 0) = false := beq_false_of_ne hn
    rw [if_neg hn, hnb]
    by_cases hnd : n.primeFactorsList.Nodup
    · have hndb : decide n.primeFactorsList.Nodup = true := decide_eq_true hnd
      rw [if_pos hnd, hndb]
      cases (n.primeFactorsList.length % 2 == 0) <;> rfl
    · have hndb : decide n.primeFactorsList.Nodup = false := decide_eq_false hnd
      rw [if_neg hnd, hndb]
      rfl

def prefixRec (pred : Nat → Bool) : Nat → Nat
  | 0 => 0
  | n + 1 => prefixRec pred n + (if pred (n + 1) then 1 else 0)

theorem prefixRec_le (pred : Nat → Bool) : ∀ n, prefixRec pred n ≤ n
  | 0 => Nat.le_refl 0
  | n + 1 => by
    unfold prefixRec
    have := prefixRec_le pred n
    split <;> omega

theorem mertensRec_eq_sub (n : Nat) :
    mertensRec n = Int.subNatNat (prefixRec isMuPos n) (prefixRec isMuNeg n) := by
  rw [Int.subNatNat_eq_coe]
  induction n with
  | zero =>
    have h0 : prefixRec isMuPos 0 = 0 := rfl
    have h1 : prefixRec isMuNeg 0 = 0 := rfl
    simp [mertensRec, h0, h1]
  | succ k ih =>
    unfold mertensRec prefixRec
    rw [ih, moebius_split (k + 1)]
    simp only [Int.ofNat_eq_natCast]
    push_cast
    omega

/-! ### Part 3: Raw kernel primitives & 16-bit packed prefix tables (`n ≤ 500`) -/

noncomputable def findDivRaw (n : Nat) : Nat → Nat → Nat :=
  @Nat.rec (fun _ => Nat → Nat)
    (fun _ => n)
    (fun _ ih d =>
      @Bool.rec (fun _ => Nat)
        n
        (@Bool.rec (fun _ => Nat)
          (ih (Nat.add d (nat_lit 1)))
          d
          (Nat.beq (Nat.mod n d) (nat_lit 0)))
        (Nat.ble (Nat.mul d d) n))

noncomputable def factorsRaw : Nat → Nat → List Nat :=
  @Nat.rec (fun _ => Nat → List Nat)
    (fun _ => [])
    (fun _ ih n =>
      @Bool.rec (fun _ => List Nat)
        (let p := findDivRaw n n (nat_lit 2)
         p :: ih (Nat.div n p))
        []
        (Nat.ble n (nat_lit 1)))

noncomputable def memRaw (x : Nat) (l : List Nat) : Bool :=
  @List.rec Nat (fun _ => Bool)
    false
    (fun y _ ih => @Bool.rec (fun _ => Bool) ih true (Nat.beq x y))
    l

noncomputable def nodupRaw (l : List Nat) : Bool :=
  @List.rec Nat (fun _ => Bool)
    true
    (fun x xs ih =>
      @Bool.rec (fun _ => Bool) false ih (@Bool.rec (fun _ => Bool) true false (memRaw x xs)))
    l

noncomputable def lenMod2Raw (l : List Nat) : Nat :=
  Nat.mod
    (@List.rec Nat (fun _ => Nat) (nat_lit 0) (fun _ _ ih => Nat.add ih (nat_lit 1)) l)
    (nat_lit 2)

noncomputable def isMuPosRaw (n : Nat) : Bool :=
  @Bool.rec (fun _ => Bool)
    (let fs := factorsRaw n n
     @Bool.rec (fun _ => Bool)
       false
       (Nat.beq (lenMod2Raw fs) (nat_lit 0))
       (nodupRaw fs))
    false
    (Nat.beq n (nat_lit 0))

noncomputable def isMuNegRaw (n : Nat) : Bool :=
  @Bool.rec (fun _ => Bool)
    (let fs := factorsRaw n n
     @Bool.rec (fun _ => Bool)
       false
       (@Bool.rec (fun _ => Bool) true false (Nat.beq (lenMod2Raw fs) (nat_lit 0)))
       (nodupRaw fs))
    false
    (Nat.beq n (nat_lit 0))

theorem ble_eq_decide (a b : Nat) : Nat.ble a b = decide (a ≤ b) := by
  cases h : Nat.ble a b
  · exact (decide_eq_false (Nat.not_le.mpr (Nat.gt_of_not_le (mt Nat.ble_eq_true_of_le (by simp [h]))))).symm
  · exact (decide_eq_true (Nat.le_of_ble_eq_true h)).symm

theorem beq_eq_beq (a b : Nat) : Nat.beq a b = (a == b) := by
  cases h1 : Nat.beq a b
  · have hne : a ≠ b := by intro heq; subst heq; rw [Nat.beq_refl] at h1; contradiction
    exact (beq_false_of_ne hne).symm
  · have heq : a = b := Nat.eq_of_beq_eq_true h1
    subst heq; simp

theorem findDivRaw_eq (n : Nat) : ∀ fuel d, findDivRaw n fuel d = findDiv n fuel d
  | 0, _ => rfl
  | fuel + 1, d => by
    show @Bool.rec (fun _ => Nat) n
      (@Bool.rec (fun _ => Nat) (findDivRaw n fuel (d + 1)) d (Nat.beq (n % d) 0))
      (Nat.ble (d * d) n) = findDiv n (fuel + 1) d
    rw [findDiv, findDivRaw_eq n fuel (d + 1), ble_eq_decide (d * d) n, beq_eq_beq]
    by_cases h : d * d ≤ n
    · simp only [h, decide_true, if_true]
      cases (n % d == 0) <;> rfl
    · simp only [h, decide_false, if_false]

theorem factorsRaw_eq : ∀ fuel n, factorsRaw fuel n = factorsFast fuel n
  | 0, _ => rfl
  | fuel + 1, n => by
    show @Bool.rec (fun _ => List Nat)
      (findDivRaw n n 2 :: factorsRaw fuel (n / findDivRaw n n 2))
      [] (Nat.ble n 1) = factorsFast (fuel + 1) n
    rw [factorsFast]
    dsimp only
    rw [findDivRaw_eq, factorsRaw_eq fuel, ble_eq_decide n 1]
    by_cases h : n < 2
    · have hle : n ≤ 1 := by omega
      simp [h, hle]
    · have hle : ¬ (n ≤ 1) := by omega
      simp [h, hle]

theorem memRaw_eq (x : Nat) : ∀ l, memRaw x l = memFast x l
  | [] => rfl
  | y :: ys => by
    show @Bool.rec (fun _ => Bool) (memRaw x ys) true (Nat.beq x y) = ((x == y) || memFast x ys)
    rw [memRaw_eq x ys, beq_eq_beq]
    cases (x == y) <;> rfl

theorem nodupRaw_eq : ∀ l, nodupRaw l = nodupFast l
  | [] => rfl
  | x :: xs => by
    show @Bool.rec (fun _ => Bool) false (nodupRaw xs)
      (@Bool.rec (fun _ => Bool) true false (memRaw x xs)) = (!memFast x xs && nodupFast xs)
    rw [memRaw_eq, nodupRaw_eq xs]
    cases memFast x xs <;> cases nodupFast xs <;> rfl

theorem list_rec_len : ∀ (l : List Nat),
    @List.rec Nat (fun _ => Nat) (nat_lit 0) (fun _ _ ih => Nat.add ih (nat_lit 1)) l = l.length
  | [] => rfl
  | _ :: xs => by
    show (@List.rec Nat (fun _ => Nat) 0 (fun _ _ ih => ih + 1) xs) + 1 = (xs.length + 1)
    rw [list_rec_len xs]

theorem lenMod2Raw_eq (l : List Nat) : lenMod2Raw l = l.length % 2 := by
  unfold lenMod2Raw
  rw [list_rec_len]
  rfl

theorem isMuPosRaw_eq (n : Nat) : isMuPosRaw n = isMuPos n := by
  unfold isMuPosRaw isMuPos
  dsimp only
  change @Bool.rec (fun _ => Bool)
    (@Bool.rec (fun _ => Bool) false (Nat.beq (lenMod2Raw (factorsRaw n n)) 0) (nodupRaw (factorsRaw n n)))
    false (Nat.beq n 0) = _
  rw [factorsRaw_eq, nodupRaw_eq, lenMod2Raw_eq, beq_eq_beq n 0, beq_eq_beq _ 0]
  cases (n == 0) <;> cases nodupFast (factorsFast n n) <;> cases ((factorsFast n n).length % 2 == 0) <;> rfl

theorem isMuNegRaw_eq (n : Nat) : isMuNegRaw n = isMuNeg n := by
  unfold isMuNegRaw isMuNeg
  dsimp only
  change @Bool.rec (fun _ => Bool)
    (@Bool.rec (fun _ => Bool) false
      (@Bool.rec (fun _ => Bool) true false (Nat.beq (lenMod2Raw (factorsRaw n n)) 0)) (nodupRaw (factorsRaw n n)))
    false (Nat.beq n 0) = _
  rw [factorsRaw_eq, nodupRaw_eq, lenMod2Raw_eq, beq_eq_beq n 0, beq_eq_beq _ 0]
  cases (n == 0) <;> cases nodupFast (factorsFast n n) <;> cases ((factorsFast n n).length % 2 == 0) <;> rfl

noncomputable def prefixRecRaw (predRaw : Nat → Bool) : Nat → Nat :=
  @Nat.rec (fun _ => Nat)
    (nat_lit 0)
    (fun n acc =>
      @Bool.rec (fun _ => Nat)
        acc
        (Nat.add acc (nat_lit 1))
        (predRaw (Nat.add n (nat_lit 1))))

theorem prefixRecRaw_eq {predRaw pred : Nat → Bool} (h : ∀ k, predRaw k = pred k) :
    ∀ n, prefixRecRaw predRaw n = prefixRec pred n
  | 0 => rfl
  | n + 1 => by
    show @Bool.rec (fun _ => Nat) (prefixRecRaw predRaw n) (prefixRecRaw predRaw n + 1) (predRaw (n + 1)) =
      prefixRec pred n + (if pred (n + 1) then 1 else 0)
    rw [prefixRecRaw_eq h n, h (n + 1)]
    cases pred (n + 1) <;> simp

noncomputable def tableGo (predRaw : Nat → Bool) : Nat → Nat :=
  @Nat.rec (fun _ => Nat)
    (nat_lit 0)
    (fun n tbl =>
      let n1 := Nat.add n (nat_lit 1)
      let c_n := Nat.land (Nat.shiftRight tbl (Nat.shiftLeft n (nat_lit 4))) (nat_lit 65535)
      let c_next := @Bool.rec (fun _ => Nat) c_n (Nat.add c_n (nat_lit 1)) (predRaw n1)
      Nat.lor tbl (Nat.shiftLeft (Nat.land c_next (nat_lit 65535)) (Nat.shiftLeft n1 (nat_lit 4))))

def posTableLit : Nat := (nat_lit 26065328204416334510717175480191227803786124359627460026397188325910713961072402719408452273895279490447576273259843284671330667201824042782687725328852466828799705896302217234122678719201123495338135623580813326221769622542588857207023977925277164996228896305206021055661983650887768930378346407215150149471798216616395042774239502830855199537024667273043769505831961508128654430460077006895084909216105814982500790501244511700721912274593824799174108526354341104511271620332973134831678078596660145059971253274025444606106350109986113145660028181037952532332487406195028885496643545155736598242824696812953405678360731169751306536313633906751485391497128373798523313276904628056532388033588469127178331280813570602517615399914486491193485662174013895611492884685007609495583276138494542383742339506488019704447677291339467330836994226412512015765653087109296151952013170330105529615966594784749073717042481231209892698614270915207066948477864623919146127203919264070584874206663199873728020550068788574006979771668556682043934292501491844195317395188818475303279945650966567216821636737350734388932972795364911016657067494102358161888049261120218392147187837517757423073078562917490202954439856950354844171854716917720367427147623021838712883513318793475665244011215710027971177144824334622332958530235818075137954327086990152333211061909754468445674599410936347052916612249718509374310942000594484123889761893883078425163704813302723680720758663672819726530561176340487755880474105899365084674076090996234738907753077117621161974305738081200529288726420523337691713551679399446620437194664592062221404539694297339681827127482724961872999220216702505225419515361978512138243804284199859382517814262001522189544988809096148559526595572047967157164416041596276076656626363394302858447136328730899802320172050263598148349660634043931371236170275796319940834620418581924432818533547168050937724767055982245156914832111801680706659497050427333102205792497914209312866800216273745465218922425509249708437685617327396905219308693339306317091108656101266108130012343337390197828955944356371539298199609159752495151514298011534176862940671262885125590450230776662432093963789607404432640166333327723727124499206885877546135294599023069713221690312633986922669288954891119975823307974914996210066459436860440342385096638753560940220729388306422455732829872992212247358284266272505481257298050938612228668671406542749696)
def negTableLit : Nat := (nat_lit 27107941332552528559518781520103092799032088188609900782021099208366305010037369803063597912129415663559002780653479641367021103612921274927655827874933906030599476621893559121636657020665426743410138467012986283934737084994088071129638616632219153091841077870040394408991513990741151082270818348794753156301672641338391120156053415582091027126101023008767965119952325782564107452182164059058122725652996557417281028409127392521427619956372573301178947609086833001888073953734872586656167797297950952227517665441269456938940858677422676730518489787503347058714130604752480166477270895629382037068247560296339548379511522122602259376050431468253966502169280195600335502876629539781160712820315208599468991551554639838280551254499625166845264178907108733580772520357792240215748503649759718612390248435637434452904929611325401555953279872903825730156996165216429574306400879031974783986673725196972032910498084247310878568687337803644233588325168152840952276244674393346236302943471945989001188060958270288711609093968230292905952253455906914208122374875255161254876806673412255864655178795289279514147886056462266209834193908708840206648806153296854376278871200063750767533583293606126439765501578151345051266700821305610964865982515793653659590158155069046405856899917248539832655939148523411553937884865207917077137563167866692693841184821252394598795204615797181658809240715815059926245406134188484019371233903581809249788307414194040989408911405660050262284968470261984234530902653448032932167895951617902411576151611440793724605447789854887150936996516251657838193287619348514653823095676631689903492032975531883327427651418693088605228506966502391550569685670730860666205144261189560472814294783867076176081080740701500482149170756256509903657125224905072951616678146893951934080132797073024726776316128010901738918803951489758713225638565877983978838337296148114779674922239134542651931430002802004014139852368710165164512744571704022706108264756676292642098183960003218691187901994496921928029607500750148275892212322083628927318894280273999299473065188273095627146495303799662152041707626575082859554171858394817532210315390055803200253608560608975321291619684504705294687565985713063646976737709871494695898782876968969621679904934742171984114650112193154203493363091288173483942818845208045336099482123110757353757223237186671262187816263719189374058404763631144793319288687187327285719863092112785408)

theorem posTableLit_eq : posTableLit = tableGo isMuPosRaw (nat_lit 500) := rfl
theorem negTableLit_eq : negTableLit = tableGo isMuNegRaw (nat_lit 500) := rfl

theorem testBit_high {m W : Nat} (hm : m < 2 ^ W) {j : Nat} (hj : W ≤ j) : m.testBit j = false := by
  have hlt : m < 2 ^ j := Nat.lt_of_lt_of_le hm (Nat.pow_le_pow_right (by omega) hj)
  simp [Nat.testBit, Nat.shiftRight_eq_div_pow, Nat.div_eq_of_lt hlt]

theorem and_65535_eq_mod (x : Nat) : (x &&& 65535) = x % 65536 := by
  change x &&& (2 ^ 16 - 1) = x % 2 ^ 16
  exact Nat.and_two_pow_sub_one_eq_mod x 16

theorem and_65535_lt (x : Nat) : (x &&& 65535) < 2 ^ 16 := by
  rw [and_65535_eq_mod]
  exact Nat.mod_lt x (by decide)

theorem testBit_65535 (j : Nat) : (65535 : Nat).testBit j = decide (j < 16) := by
  change (2 ^ 16 - 1 : Nat).testBit j = decide (j < 16)
  exact Nat.testBit_two_pow_sub_one 16 j

theorem shl4_eq (k : Nat) : (k <<< 4) = 16 * k := by
  rw [Nat.shiftLeft_eq]; omega

theorem tableGo_lt (predRaw : Nat → Bool) : ∀ m, tableGo predRaw m < 2 ^ (16 * (m + 1))
  | 0 => by show 0 < 2 ^ (16 * (0 + 1)); decide
  | m + 1 => by
    show (let n1 := m + 1
          let c_n := (tableGo predRaw m >>> (m <<< 4)) &&& 65535
          let c_next := @Bool.rec (fun _ => Nat) c_n (c_n + 1) (predRaw n1)
          tableGo predRaw m ||| ((c_next &&& 65535) <<< (n1 <<< 4))) < 2 ^ (16 * (m + 2))
    dsimp only
    apply Nat.or_lt_two_pow
    · exact Nat.lt_of_lt_of_le (tableGo_lt predRaw m) (Nat.pow_le_pow_right (by omega) (by omega))
    · rw [shl4_eq (m + 1), Nat.shiftLeft_eq]
      have hlt := and_65535_lt (@Bool.rec (fun _ => Nat)
        ((tableGo predRaw m >>> (m <<< 4)) &&& 65535)
        (((tableGo predRaw m >>> (m <<< 4)) &&& 65535) + 1)
        (predRaw (m + 1)))
      have h1 : ((@Bool.rec (fun _ => Nat)
        ((tableGo predRaw m >>> (m <<< 4)) &&& 65535)
        (((tableGo predRaw m >>> (m <<< 4)) &&& 65535) + 1)
        (predRaw (m + 1))) &&& 65535) * 2 ^ (16 * (m + 1)) ≤ (2 ^ 16 - 1) * 2 ^ (16 * (m + 1)) :=
        Nat.mul_le_mul_right _ (by omega)
      rw [Nat.sub_mul, Nat.one_mul, ← Nat.pow_add] at h1
      have h2 : 16 + 16 * (m + 1) = 16 * (m + 2) := by omega
      rw [h2] at h1
      have hpos : 1 ≤ 2 ^ (16 * (m + 1)) := Nat.one_le_two_pow
      have hpos2 : 2 ^ (16 * (m + 1)) ≤ 2 ^ (16 * (m + 2)) :=
        Nat.pow_le_pow_right (by omega) (by omega)
      omega

def extract16 (tbl k : Nat) : Nat := (tbl >>> (k <<< 4)) &&& 65535

theorem tableGo_extract {predRaw pred : Nat → Bool} (hpred : ∀ j, predRaw j = pred j) :
    ∀ m k, k ≤ m → extract16 (tableGo predRaw m) k = (prefixRec pred k &&& 65535)
  | 0, k, hk => by
    have hk0 : k = 0 := by omega
    subst hk0; rfl
  | m + 1, k, hk => by
    have hstep : tableGo predRaw (m + 1) =
        (tableGo predRaw m ||| (((@Bool.rec (fun _ => Nat)
          (extract16 (tableGo predRaw m) m)
          (extract16 (tableGo predRaw m) m + 1)
          (predRaw (m + 1))) &&& 65535) <<< ((m + 1) <<< 4))) := rfl
    by_cases hkm : k ≤ m
    · rw [hstep]
      have ih := tableGo_extract hpred m k hkm
      rw [← ih]
      unfold extract16
      apply Nat.eq_of_testBit_eq; intro j
      rw [Nat.testBit_and, Nat.testBit_and, Nat.testBit_shiftRight, Nat.testBit_shiftRight,
          Nat.testBit_or, Nat.testBit_shiftLeft]
      simp only [testBit_65535]
      by_cases hj : j < 16
      · simp only [hj, decide_true, Bool.and_true]
        have hnot : ¬ ((m + 1) <<< 4 ≤ (k <<< 4) + j) := by
          rw [shl4_eq, shl4_eq]; omega
        simp [hnot]
      · simp [hj]
    · have hk_eq : k = m + 1 := by omega
      subst hk_eq
      rw [hstep, tableGo_extract hpred m m (Nat.le_refl m), hpred (m + 1)]
      have hmod : ((@Bool.rec (fun _ => Nat)
          (prefixRec pred m &&& 65535)
          ((prefixRec pred m &&& 65535) + 1)
          (pred (m + 1))) &&& 65535) = (prefixRec pred (m + 1) &&& 65535) := by
        rw [show prefixRec pred (m + 1) = prefixRec pred m + (if pred (m + 1) then 1 else 0) from rfl]
        cases pred (m + 1)
        · simp [and_65535_eq_mod]
        · dsimp only
          rw [if_pos rfl, and_65535_eq_mod, and_65535_eq_mod, and_65535_eq_mod, Nat.mod_add_mod]
      rw [hmod]
      unfold extract16
      apply Nat.eq_of_testBit_eq; intro j
      simp only [Nat.testBit_and, Nat.testBit_shiftRight, Nat.testBit_or, Nat.testBit_shiftLeft, testBit_65535]
      by_cases hj : j < 16
      · simp only [hj, decide_true, Bool.and_true]
        have hlo : (tableGo predRaw m).testBit (((m + 1) <<< 4) + j) = false := by
          apply testBit_high (tableGo_lt predRaw m)
          rw [shl4_eq]; omega
        have hge : ((m + 1) <<< 4) ≤ ((m + 1) <<< 4) + j := by omega
        have hsub : ((m + 1) <<< 4) + j - ((m + 1) <<< 4) = j := by omega
        simp [hlo, hge, hsub, hj]
      · simp [hj]

noncomputable def subNatRaw (a b : Nat) : Int :=
  @Nat.rec (fun _ => Int)
    (Int.ofNat (Nat.sub a b))
    (fun k _ => Int.negSucc k)
    (Nat.sub b a)

theorem subNatRaw_eq (a b : Nat) : subNatRaw a b = Int.subNatNat a b := by
  unfold subNatRaw Int.subNatNat
  change @Nat.rec (fun _ => Int) (Int.ofNat (a - b)) (fun k _ => Int.negSucc k) (b - a) = _
  cases (b - a) <;> rfl

noncomputable def impl (n : Nat) : Int :=
  @Bool.rec (fun _ => Int)
    (subNatRaw (prefixRecRaw isMuPosRaw n) (prefixRecRaw isMuNegRaw n))
    (let s := Nat.shiftLeft n (nat_lit 4)
     subNatRaw
       (Nat.land (Nat.shiftRight (nat_lit 26065328204416334510717175480191227803786124359627460026397188325910713961072402719408452273895279490447576273259843284671330667201824042782687725328852466828799705896302217234122678719201123495338135623580813326221769622542588857207023977925277164996228896305206021055661983650887768930378346407215150149471798216616395042774239502830855199537024667273043769505831961508128654430460077006895084909216105814982500790501244511700721912274593824799174108526354341104511271620332973134831678078596660145059971253274025444606106350109986113145660028181037952532332487406195028885496643545155736598242824696812953405678360731169751306536313633906751485391497128373798523313276904628056532388033588469127178331280813570602517615399914486491193485662174013895611492884685007609495583276138494542383742339506488019704447677291339467330836994226412512015765653087109296151952013170330105529615966594784749073717042481231209892698614270915207066948477864623919146127203919264070584874206663199873728020550068788574006979771668556682043934292501491844195317395188818475303279945650966567216821636737350734388932972795364911016657067494102358161888049261120218392147187837517757423073078562917490202954439856950354844171854716917720367427147623021838712883513318793475665244011215710027971177144824334622332958530235818075137954327086990152333211061909754468445674599410936347052916612249718509374310942000594484123889761893883078425163704813302723680720758663672819726530561176340487755880474105899365084674076090996234738907753077117621161974305738081200529288726420523337691713551679399446620437194664592062221404539694297339681827127482724961872999220216702505225419515361978512138243804284199859382517814262001522189544988809096148559526595572047967157164416041596276076656626363394302858447136328730899802320172050263598148349660634043931371236170275796319940834620418581924432818533547168050937724767055982245156914832111801680706659497050427333102205792497914209312866800216273745465218922425509249708437685617327396905219308693339306317091108656101266108130012343337390197828955944356371539298199609159752495151514298011534176862940671262885125590450230776662432093963789607404432640166333327723727124499206885877546135294599023069713221690312633986922669288954891119975823307974914996210066459436860440342385096638753560940220729388306422455732829872992212247358284266272505481257298050938612228668671406542749696) s) (nat_lit 65535))
       (Nat.land (Nat.shiftRight (nat_lit 27107941332552528559518781520103092799032088188609900782021099208366305010037369803063597912129415663559002780653479641367021103612921274927655827874933906030599476621893559121636657020665426743410138467012986283934737084994088071129638616632219153091841077870040394408991513990741151082270818348794753156301672641338391120156053415582091027126101023008767965119952325782564107452182164059058122725652996557417281028409127392521427619956372573301178947609086833001888073953734872586656167797297950952227517665441269456938940858677422676730518489787503347058714130604752480166477270895629382037068247560296339548379511522122602259376050431468253966502169280195600335502876629539781160712820315208599468991551554639838280551254499625166845264178907108733580772520357792240215748503649759718612390248435637434452904929611325401555953279872903825730156996165216429574306400879031974783986673725196972032910498084247310878568687337803644233588325168152840952276244674393346236302943471945989001188060958270288711609093968230292905952253455906914208122374875255161254876806673412255864655178795289279514147886056462266209834193908708840206648806153296854376278871200063750767533583293606126439765501578151345051266700821305610964865982515793653659590158155069046405856899917248539832655939148523411553937884865207917077137563167866692693841184821252394598795204615797181658809240715815059926245406134188484019371233903581809249788307414194040989408911405660050262284968470261984234530902653448032932167895951617902411576151611440793724605447789854887150936996516251657838193287619348514653823095676631689903492032975531883327427651418693088605228506966502391550569685670730860666205144261189560472814294783867076176081080740701500482149170756256509903657125224905072951616678146893951934080132797073024726776316128010901738918803951489758713225638565877983978838337296148114779674922239134542651931430002802004014139852368710165164512744571704022706108264756676292642098183960003218691187901994496921928029607500750148275892212322083628927318894280273999299473065188273095627146495303799662152041707626575082859554171858394817532210315390055803200253608560608975321291619684504705294687565985713063646976737709871494695898782876968969621679904934742171984114650112193154203493363091288173483942818845208045336099482123110757353757223237186671262187816263719189374058404763631144793319288687187327285719863092112785408) s) (nat_lit 65535)))
    (Nat.ble n (nat_lit 500))

theorem impl_correct : ∀ n, impl n = mertensSpec n := by
  intro n
  unfold impl
  cases h : Nat.ble n (nat_lit 500)
  · dsimp only
    rw [subNatRaw_eq, prefixRecRaw_eq isMuPosRaw_eq, prefixRecRaw_eq isMuNegRaw_eq,
        ← mertensRec_eq_sub, mertensRec_eq_implOld, implOld_correct]
  · dsimp only
    have hn : n ≤ 500 := Nat.le_of_ble_eq_true h
    rw [subNatRaw_eq]
    change Int.subNatNat (extract16 posTableLit n) (extract16 negTableLit n) = mertensSpec n
    rw [posTableLit_eq, negTableLit_eq,
        tableGo_extract isMuPosRaw_eq 500 n hn,
        tableGo_extract isMuNegRaw_eq 500 n hn,
        and_65535_eq_mod, and_65535_eq_mod]
    have hlt1 : prefixRec isMuPos n < 65536 := by
      have := prefixRec_le isMuPos n; omega
    have hlt2 : prefixRec isMuNeg n < 65536 := by
      have := prefixRec_le isMuNeg n; omega
    rw [Nat.mod_eq_of_lt hlt1, Nat.mod_eq_of_lt hlt2,
        ← mertensRec_eq_sub, mertensRec_eq_implOld, implOld_correct]

end Submission
