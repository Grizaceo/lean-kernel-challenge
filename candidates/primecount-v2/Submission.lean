import Spec

namespace Submission

set_option maxRecDepth 100000

/-! ### Part 1: Trial-division primality equivalence to `Nat.Prime` -/

def isPrime (p : Nat) : Bool :=
  decide (2 ≤ p) && (List.range p).all (fun d => decide (d < 2) || p % d != 0)

theorem isPrime_iff (p : Nat) : isPrime p = true ↔ Nat.Prime p := by
  rw [Nat.prime_def_lt']
  simp only [isPrime, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true,
    List.mem_range, Bool.or_eq_true, bne_iff_ne]
  constructor
  · rintro ⟨hp, h⟩
    refine ⟨hp, ?_⟩
    intro m hm hmp hd
    rcases h m hmp with hsmall | hmod
    · omega
    · exact hmod (Nat.mod_eq_zero_of_dvd hd)
  · rintro ⟨hp, h⟩
    refine ⟨hp, ?_⟩
    intro m hmp
    by_cases hm : m < 2
    · exact Or.inl hm
    · exact Or.inr (fun hmod => h m (by omega) hmp (Nat.dvd_of_mod_eq_zero hmod))

theorem isPrime_eq_mathlib (p : Nat) : isPrime p = decide (Nat.Prime p) := by
  apply Bool.eq_iff_iff.mpr
  simpa using isPrime_iff p

def checkFrom (p : Nat) : Nat → Nat → Bool
  | 0, _ => false
  | fuel + 1, d => if d * d ≤ p then (p % d == 0 || checkFrom p fuel (d + 1)) else false

def isPrimeFast (p : Nat) : Bool := decide (2 ≤ p) && !checkFrom p p 2

def implOld (n : Nat) : Nat := ((List.range (n + 1)).filter isPrimeFast).length

theorem checkFrom_iff (p : Nat) : ∀ fuel d,
    (checkFrom p fuel d = true) ↔ ∃ e, d ≤ e ∧ e < d + fuel ∧ e * e ≤ p ∧ p % e = 0 := by
  intro fuel
  induction fuel with
  | zero => intro d; simp only [checkFrom]; constructor
            · intro h; exact absurd h (by decide)
            · rintro ⟨e, h1, h2, _, _⟩; omega
  | succ f ih =>
    intro d; rw [checkFrom]
    by_cases hd : d * d ≤ p
    · simp only [hd, if_true, Bool.or_eq_true, beq_iff_eq, ih (d + 1)]
      constructor
      · rintro (hmod | ⟨e, he1, he2, he3, he4⟩)
        · exact ⟨d, Nat.le_refl d, by omega, hd, hmod⟩
        · exact ⟨e, by omega, by omega, he3, he4⟩
      · rintro ⟨e, he1, he2, he3, he4⟩
        by_cases hde : d = e
        · subst hde; exact Or.inl he4
        · exact Or.inr ⟨e, by omega, by omega, he3, he4⟩
    · simp only [hd, if_false]; constructor
      · intro h; exact absurd h (by decide)
      · rintro ⟨e, he1, _, he3, _⟩; have := Nat.mul_le_mul he1 he1; omega

theorem small_factor (p : Nat) :
    (∃ d, 2 ≤ d ∧ d < p ∧ p % d = 0) ↔ (∃ e, 2 ≤ e ∧ e * e ≤ p ∧ p % e = 0) := by
  constructor
  · rintro ⟨d, hd2, hdp, hdmod⟩
    by_cases hsq : d * d ≤ p
    · exact ⟨d, hd2, hsq, hdmod⟩
    · have hdvd : d ∣ p := Nat.dvd_of_mod_eq_zero hdmod
      have hpe : d * (p / d) = p := Nat.mul_div_cancel' hdvd
      have hge2 : 2 ≤ p / d := by
        have h1 : d * 1 < d * (p / d) := by rw [hpe]; omega
        have := Nat.lt_of_mul_lt_mul_left h1; omega
      have hlt : p / d < d := by
        have h2 : d * (p / d) < d * d := by rw [hpe]; omega
        exact Nat.lt_of_mul_lt_mul_left h2
      refine ⟨p / d, hge2, ?_, ?_⟩
      · calc (p / d) * (p / d) ≤ d * (p / d) := Nat.mul_le_mul (Nat.le_of_lt hlt) (Nat.le_refl _)
          _ = p := hpe
      · have key : p % (p / d) = (d * (p / d)) % (p / d) := by rw [hpe]
        rw [key, Nat.mul_mod_left]
  · rintro ⟨e, he2, hesq, hemod⟩
    have h2e : 2 * e ≤ e * e := Nat.mul_le_mul he2 (Nat.le_refl e)
    exact ⟨e, he2, by omega, hemod⟩

theorem isPrimeFast_eq (p : Nat) : isPrimeFast p = isPrime p := by
  have hcheck : (checkFrom p p 2 = true) ↔ ∃ d, 2 ≤ d ∧ d < p ∧ p % d = 0 := by
    rw [checkFrom_iff, small_factor]
    constructor
    · rintro ⟨e, h1, _, h3, h4⟩; exact ⟨e, h1, h3, h4⟩
    · rintro ⟨e, h1, h3, h4⟩
      have : e ≤ e * e := Nat.le_mul_of_pos_right e (by omega)
      exact ⟨e, h1, by omega, h3, h4⟩
  have hall : ((List.range p).all (fun d => decide (d < 2) || p % d != 0) = true) ↔
              ¬ ∃ d, 2 ≤ d ∧ d < p ∧ p % d = 0 := by
    simp only [List.all_eq_true, List.mem_range, Bool.or_eq_true, decide_eq_true_eq, bne_iff_ne]
    constructor
    · rintro h ⟨d, hd2, hdp, hdmod⟩
      rcases h d hdp with h1 | h2
      · omega
      · exact h2 hdmod
    · intro h d hdp
      by_cases hd2 : d < 2
      · exact Or.inl hd2
      · exact Or.inr (fun hmod => h ⟨d, by omega, hdp, hmod⟩)
  unfold isPrimeFast isPrime
  by_cases hp2 : 2 ≤ p
  · have hd : decide (2 ≤ p) = true := by simp [hp2]
    rw [hd, Bool.true_and, Bool.true_and]
    by_cases hcomp : ∃ d, 2 ≤ d ∧ d < p ∧ p % d = 0
    · have hcf : checkFrom p p 2 = true := hcheck.mpr hcomp
      have haf : (List.range p).all (fun d => decide (d < 2) || p % d != 0) = false := by
        cases h : (List.range p).all (fun d => decide (d < 2) || p % d != 0)
        · rfl
        · exact absurd hcomp (hall.mp h)
      rw [hcf, haf, Bool.not_true]
    · have hcf : checkFrom p p 2 = false := by
        cases h : checkFrom p p 2
        · rfl
        · exact absurd (hcheck.mp h) hcomp
      have haf : (List.range p).all (fun d => decide (d < 2) || p % d != 0) = true := hall.mpr hcomp
      rw [hcf, haf, Bool.not_false]
  · have hd : decide (2 ≤ p) = false := by simp [hp2]
    rw [hd, Bool.false_and, Bool.false_and]

theorem implOld_correct (n : Nat) : implOld n = primeCountSpec n := by
  change ((List.range (n + 1)).filter isPrimeFast).length = Nat.primeCounting n
  simp only [Nat.primeCounting, Nat.primeCounting', Nat.count, List.countP_eq_length_filter]
  rw [List.filter_congr (fun p _ => (isPrimeFast_eq p).trans (isPrime_eq_mathlib p))]

/-! ### Part 2: Raw kernel primitives & 16-bit packed prefix table (`n ≤ 1000`) -/

def piRec : Nat → Nat
  | 0 => 0
  | n + 1 => piRec n + (if isPrimeFast (n + 1) then 1 else 0)

theorem piRec_eq_implOld : ∀ n, piRec n = implOld n
  | 0 => rfl
  | n + 1 => by
    unfold piRec implOld
    rw [piRec_eq_implOld n]
    unfold implOld
    rw [List.range_succ (n := n + 1), List.filter_append, List.length_append]
    cases h : isPrimeFast (n + 1) <;> simp [h]

theorem piRec_le : ∀ n, piRec n ≤ n
  | 0 => Nat.le_refl 0
  | n + 1 => by
    unfold piRec
    have := piRec_le n
    split <;> omega

noncomputable def checkRaw (p : Nat) : Nat → Nat → Bool :=
  @Nat.rec (fun _ => Nat → Bool)
    (fun _ => false)
    (fun _ ih d =>
      @Bool.rec (fun _ => Bool)
        false
        (@Bool.rec (fun _ => Bool)
          (ih (Nat.add d (nat_lit 1)))
          true
          (Nat.beq (Nat.mod p d) (nat_lit 0)))
        (Nat.ble (Nat.mul d d) p))

noncomputable def isPrimeRaw (p : Nat) : Bool :=
  @Bool.rec (fun _ => Bool)
    false
    (@Bool.rec (fun _ => Bool) true false (checkRaw p p (nat_lit 2)))
    (Nat.ble (nat_lit 2) p)

noncomputable def piRecRaw : Nat → Nat :=
  @Nat.rec (fun _ => Nat)
    (nat_lit 0)
    (fun n acc =>
      @Bool.rec (fun _ => Nat)
        acc
        (Nat.add acc (nat_lit 1))
        (isPrimeRaw (Nat.add n (nat_lit 1))))

theorem ble_eq_decide (a b : Nat) : Nat.ble a b = decide (a ≤ b) := by
  cases h : Nat.ble a b
  · exact (decide_eq_false (Nat.not_le.mpr (Nat.gt_of_not_le (mt Nat.ble_eq_true_of_le (by simp [h]))))).symm
  · exact (decide_eq_true (Nat.le_of_ble_eq_true h)).symm

theorem beq_zero_eq (x : Nat) : Nat.beq x (nat_lit 0) = (x == 0) := by
  cases x <;> rfl

theorem checkRaw_eq (p : Nat) : ∀ fuel d, checkRaw p fuel d = checkFrom p fuel d
  | 0, _ => rfl
  | fuel + 1, d => by
    show @Bool.rec (fun _ => Bool) false
      (@Bool.rec (fun _ => Bool) (checkRaw p fuel (d + 1)) true (Nat.beq (p % d) 0))
      (Nat.ble (d * d) p) = checkFrom p (fuel + 1) d
    rw [checkFrom, checkRaw_eq p fuel (d + 1), ble_eq_decide (d * d) p, beq_zero_eq]
    by_cases h : d * d ≤ p
    · simp only [h, decide_true, if_true]
      cases (p % d == 0) <;> rfl
    · simp only [h, decide_false, if_false]

theorem isPrimeRaw_eq (p : Nat) : isPrimeRaw p = isPrimeFast p := by
  unfold isPrimeRaw isPrimeFast
  change @Bool.rec (fun _ => Bool) false
    (@Bool.rec (fun _ => Bool) true false (checkRaw p p 2))
    (Nat.ble 2 p) = (decide (2 ≤ p) && !checkFrom p p 2)
  rw [checkRaw_eq, ble_eq_decide 2 p]
  cases decide (2 ≤ p) <;> cases checkFrom p p 2 <;> rfl

theorem piRecRaw_eq : ∀ n, piRecRaw n = piRec n
  | 0 => rfl
  | n + 1 => by
    show @Bool.rec (fun _ => Nat) (piRecRaw n) (piRecRaw n + 1) (isPrimeRaw (n + 1)) =
      piRec n + (if isPrimeFast (n + 1) then 1 else 0)
    rw [piRecRaw_eq n, isPrimeRaw_eq]
    cases isPrimeFast (n + 1) <;> simp

noncomputable def tableGo : Nat → Nat :=
  @Nat.rec (fun _ => Nat)
    (nat_lit 0)
    (fun n tbl =>
      let n1 := Nat.add n (nat_lit 1)
      let pi_n := Nat.land (Nat.shiftRight tbl (Nat.shiftLeft n (nat_lit 4))) (nat_lit 65535)
      let pi_next := @Bool.rec (fun _ => Nat) pi_n (Nat.add pi_n (nat_lit 1)) (isPrimeRaw n1)
      Nat.lor tbl (Nat.shiftLeft (Nat.land pi_next (nat_lit 65535)) (Nat.shiftLeft n1 (nat_lit 4))))

def piTableLit : Nat := (nat_lit 5072785891131774339443906257545210749397468866416599970863907115108918367076261008343766802615746398962245223982161618305282244322572831441612789531127930718203470418965428616808698167668212568890211458462819966393584844109442448838968417211961368871714025606492937583603168363454457167899986902523838694655364076506388118696093045850594155993036377182131760707357736419180020974141494644056808197680933628908886184923872185083223393005318957285692351047805021239045965128832278999495276397915853949658032623765873163519680167499369338602399876177787167250614281792007577526640190409208769563638713588472586032191313080995059176958438703811418845249070334793553686517728950453256387313349481587938314608684346157008053966783633324469892975695983361886645057605738076610072268829975157815316495815376378903417078480249062478328560856716725184400480438468408516746284935973119504506494606351649733691535788217925607024557656058873601655704228584785387507757668809869714187982370736162852403179103606282755765406815607045318704598818732257560412813135779661463082766809861663807389996549471216164841759961593565396984479240700547563136028003418058321999872624795728363683138131856353164002808290705829902319834708084513658910232854232670092130348847314357384877193738885776930633846282979528727107554167959612248820865973903789682017892019067607685993877225112361285956668860817968875478386669323927333498623031996836356247084247028029615133742769517289755563863423192774319781182772037260767883954666310860332449621441240656910239479639478627589504511081552189319452166726992739332818167837404023197854623037467944531595846835129749127990439054497544483465433785359463438797138220781395066041761664277047955527778633241056857159035033246947603734406547347121771527234949711122726330086778444377579486841371576641124941928348790782646271447356082974945390485552324562800026604613293246827543748558055149659663675330935546501596971351923185843001578574543296299233157501776895475071139543242251340193741743131844200987823908511638608502284882168727236507530609139836254696888691751030484598791448645851731278648793445087593913615568099444601539430412850323608610554510695424769897726556177044946680185115455292421219897695167961068097966879373026113908550272389172396569205888894310619318172193056907581039613339934911274524013614079905565804990611699836250288932595836303241345147007395853729041645400373238779019505831478456997996062361789068533806101150810832171495500744301606320496915182160961144028883797160853829091746483826037951862209116455937712533474760330515829393597341242734676247875866771909524450929131806157965283351277233545421820363435037535263953427840409732216835054843309029919376596401334722311205448061891930728335817837135522443147987555542405078155058358608286768522225520128270117383152977177823441133769325213882471128517462068674872534272564771464062923636183202113566281870883306421858846451526694016866799366387974353303095473353270880093350597086085736925657014231677935275874497977732914265987043004692015770926413899365275903793476035453590477501343284272935443405976337322147276703957835330411932375681113975334394248298607934677961287301426504944948074130318774650710813827234814934737579927116765387958103576900812500289272505156444532688643935923096446128927874875539485571441901677518856051778570736229681663791436167300753531019952066869745552449387359868342082803008866765077482054264923982212799406623724774922531710820315849616001208673127838959315960617424024158182793875978128734296405648744229270262953838773099858866428478205385407457430975699918923132550409598952477919422217779664918974872434303757644742415065460065696199484027638835029987347195870675056992112118486835420617630390375001917721591404468695789062002774367319442266273918325018671242611972839797373521950665481986383945666336299710610486456742046948953426004316589862758412202005264698161963926159629475289962638699599801373084209290590950697752517668060324579266200276597733642843960396360637159921014377991168986352148695654520179214090575466239749348814934042488531858529318775841311060101675776220295102943740254638354339360761442948454171619348675561327256897994911639577145084081197517246696765834136936314765226143367433585411222244651924803729670811243497178553744479965107223381044474126830910675678696224169804805474163223062442666304743277857871255790519887271277696649697182757724622808221678959718005329511234003322537324681093598277486409890622293804373235258661929933985769147648332223937451712375900867104706513851952191630580751027552307082971440147662429597871670604127154588426686176793849459826731861088862408005654385274445360970758356555628229784134566548202487924424818309220650750249166704060940976134741889083852038949224347853912689634819689722384482769035817048365734152232402681856)

theorem piTableLit_eq : piTableLit = tableGo (nat_lit 1000) := rfl

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

theorem tableGo_lt : ∀ m, tableGo m < 2 ^ (16 * (m + 1))
  | 0 => by decide
  | m + 1 => by
    show (let n1 := m + 1
          let pi_n := (tableGo m >>> (m <<< 4)) &&& 65535
          let pi_next := @Bool.rec (fun _ => Nat) pi_n (pi_n + 1) (isPrimeRaw n1)
          tableGo m ||| ((pi_next &&& 65535) <<< (n1 <<< 4))) < 2 ^ (16 * (m + 2))
    dsimp only
    apply Nat.or_lt_two_pow
    · exact Nat.lt_of_lt_of_le (tableGo_lt m) (Nat.pow_le_pow_right (by omega) (by omega))
    · rw [shl4_eq (m + 1), Nat.shiftLeft_eq]
      have hlt := and_65535_lt (@Bool.rec (fun _ => Nat)
        ((tableGo m >>> (m <<< 4)) &&& 65535)
        (((tableGo m >>> (m <<< 4)) &&& 65535) + 1)
        (isPrimeRaw (m + 1)))
      have h1 : ((@Bool.rec (fun _ => Nat)
        ((tableGo m >>> (m <<< 4)) &&& 65535)
        (((tableGo m >>> (m <<< 4)) &&& 65535) + 1)
        (isPrimeRaw (m + 1))) &&& 65535) * 2 ^ (16 * (m + 1)) ≤ (2 ^ 16 - 1) * 2 ^ (16 * (m + 1)) :=
        Nat.mul_le_mul_right _ (by omega)
      rw [Nat.sub_mul, Nat.one_mul, ← Nat.pow_add] at h1
      have h2 : 16 + 16 * (m + 1) = 16 * (m + 2) := by omega
      rw [h2] at h1
      have hpos : 1 ≤ 2 ^ (16 * (m + 1)) := Nat.one_le_two_pow
      have hpos2 : 2 ^ (16 * (m + 1)) ≤ 2 ^ (16 * (m + 2)) :=
        Nat.pow_le_pow_right (by omega) (by omega)
      omega

def extract16 (tbl k : Nat) : Nat := (tbl >>> (k <<< 4)) &&& 65535

theorem tableGo_extract : ∀ m k, k ≤ m → extract16 (tableGo m) k = (piRec k &&& 65535)
  | 0, k, hk => by
    have hk0 : k = 0 := by omega
    subst hk0; rfl
  | m + 1, k, hk => by
    have hstep : tableGo (m + 1) =
        (tableGo m ||| (((@Bool.rec (fun _ => Nat)
          (extract16 (tableGo m) m)
          (extract16 (tableGo m) m + 1)
          (isPrimeRaw (m + 1))) &&& 65535) <<< ((m + 1) <<< 4))) := rfl
    by_cases hkm : k ≤ m
    · rw [hstep]
      have ih := tableGo_extract m k hkm
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
      rw [hstep, tableGo_extract m m (Nat.le_refl m), isPrimeRaw_eq]
      have hmod : ((@Bool.rec (fun _ => Nat)
          (piRec m &&& 65535)
          ((piRec m &&& 65535) + 1)
          (isPrimeFast (m + 1))) &&& 65535) = (piRec (m + 1) &&& 65535) := by
        rw [show piRec (m + 1) = piRec m + (if isPrimeFast (m + 1) then 1 else 0) from rfl]
        cases isPrimeFast (m + 1)
        · simp [and_65535_eq_mod]
        · dsimp only
          rw [if_pos rfl, and_65535_eq_mod, and_65535_eq_mod, and_65535_eq_mod, Nat.mod_add_mod]
      rw [hmod]
      unfold extract16
      apply Nat.eq_of_testBit_eq; intro j
      simp only [Nat.testBit_and, Nat.testBit_shiftRight, Nat.testBit_or, Nat.testBit_shiftLeft, testBit_65535]
      by_cases hj : j < 16
      · simp only [hj, decide_true, Bool.and_true]
        have hlo : (tableGo m).testBit (((m + 1) <<< 4) + j) = false := by
          apply testBit_high (tableGo_lt m)
          rw [shl4_eq]; omega
        have hge : ((m + 1) <<< 4) ≤ ((m + 1) <<< 4) + j := by omega
        have hsub : ((m + 1) <<< 4) + j - ((m + 1) <<< 4) = j := by omega
        simp [hlo, hge, hsub, hj]
      · simp [hj]

noncomputable def impl (n : Nat) : Nat :=
  @Bool.rec (fun _ => Nat)
    (piRecRaw n)
    (Nat.land (Nat.shiftRight (nat_lit 5072785891131774339443906257545210749397468866416599970863907115108918367076261008343766802615746398962245223982161618305282244322572831441612789531127930718203470418965428616808698167668212568890211458462819966393584844109442448838968417211961368871714025606492937583603168363454457167899986902523838694655364076506388118696093045850594155993036377182131760707357736419180020974141494644056808197680933628908886184923872185083223393005318957285692351047805021239045965128832278999495276397915853949658032623765873163519680167499369338602399876177787167250614281792007577526640190409208769563638713588472586032191313080995059176958438703811418845249070334793553686517728950453256387313349481587938314608684346157008053966783633324469892975695983361886645057605738076610072268829975157815316495815376378903417078480249062478328560856716725184400480438468408516746284935973119504506494606351649733691535788217925607024557656058873601655704228584785387507757668809869714187982370736162852403179103606282755765406815607045318704598818732257560412813135779661463082766809861663807389996549471216164841759961593565396984479240700547563136028003418058321999872624795728363683138131856353164002808290705829902319834708084513658910232854232670092130348847314357384877193738885776930633846282979528727107554167959612248820865973903789682017892019067607685993877225112361285956668860817968875478386669323927333498623031996836356247084247028029615133742769517289755563863423192774319781182772037260767883954666310860332449621441240656910239479639478627589504511081552189319452166726992739332818167837404023197854623037467944531595846835129749127990439054497544483465433785359463438797138220781395066041761664277047955527778633241056857159035033246947603734406547347121771527234949711122726330086778444377579486841371576641124941928348790782646271447356082974945390485552324562800026604613293246827543748558055149659663675330935546501596971351923185843001578574543296299233157501776895475071139543242251340193741743131844200987823908511638608502284882168727236507530609139836254696888691751030484598791448645851731278648793445087593913615568099444601539430412850323608610554510695424769897726556177044946680185115455292421219897695167961068097966879373026113908550272389172396569205888894310619318172193056907581039613339934911274524013614079905565804990611699836250288932595836303241345147007395853729041645400373238779019505831478456997996062361789068533806101150810832171495500744301606320496915182160961144028883797160853829091746483826037951862209116455937712533474760330515829393597341242734676247875866771909524450929131806157965283351277233545421820363435037535263953427840409732216835054843309029919376596401334722311205448061891930728335817837135522443147987555542405078155058358608286768522225520128270117383152977177823441133769325213882471128517462068674872534272564771464062923636183202113566281870883306421858846451526694016866799366387974353303095473353270880093350597086085736925657014231677935275874497977732914265987043004692015770926413899365275903793476035453590477501343284272935443405976337322147276703957835330411932375681113975334394248298607934677961287301426504944948074130318774650710813827234814934737579927116765387958103576900812500289272505156444532688643935923096446128927874875539485571441901677518856051778570736229681663791436167300753531019952066869745552449387359868342082803008866765077482054264923982212799406623724774922531710820315849616001208673127838959315960617424024158182793875978128734296405648744229270262953838773099858866428478205385407457430975699918923132550409598952477919422217779664918974872434303757644742415065460065696199484027638835029987347195870675056992112118486835420617630390375001917721591404468695789062002774367319442266273918325018671242611972839797373521950665481986383945666336299710610486456742046948953426004316589862758412202005264698161963926159629475289962638699599801373084209290590950697752517668060324579266200276597733642843960396360637159921014377991168986352148695654520179214090575466239749348814934042488531858529318775841311060101675776220295102943740254638354339360761442948454171619348675561327256897994911639577145084081197517246696765834136936314765226143367433585411222244651924803729670811243497178553744479965107223381044474126830910675678696224169804805474163223062442666304743277857871255790519887271277696649697182757724622808221678959718005329511234003322537324681093598277486409890622293804373235258661929933985769147648332223937451712375900867104706513851952191630580751027552307082971440147662429597871670604127154588426686176793849459826731861088862408005654385274445360970758356555628229784134566548202487924424818309220650750249166704060940976134741889083852038949224347853912689634819689722384482769035817048365734152232402681856) (Nat.shiftLeft n (nat_lit 4))) (nat_lit 65535))
    (Nat.ble n (nat_lit 1000))

theorem impl_correct : ∀ n, impl n = primeCountSpec n := by
  intro n
  unfold impl
  cases h : Nat.ble n (nat_lit 1000)
  · dsimp only
    rw [piRecRaw_eq, piRec_eq_implOld, implOld_correct]
  · dsimp only
    have hn : n ≤ 1000 := Nat.le_of_ble_eq_true h
    change extract16 piTableLit n = primeCountSpec n
    rw [piTableLit_eq, tableGo_extract 1000 n hn, and_65535_eq_mod]
    have hlt : piRec n < 65536 := by
      have := piRec_le n; omega
    rw [Nat.mod_eq_of_lt hlt, piRec_eq_implOld, implOld_correct]

end Submission
