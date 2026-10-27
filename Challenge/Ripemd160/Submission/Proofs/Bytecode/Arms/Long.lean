import Challenge.Ripemd160.Submission.Proofs.Bytecode.Arms.Each
import Challenge.Ripemd160.Submission.Proofs.Bytecode.Arms.Finish
import Challenge.Ripemd160.Submission.Proofs.Bytecode.Arms.WindowCover
set_option warningAsError true
set_option maxRecDepth 100000
set_option maxHeartbeats 32000000
set_option linter.unusedSimpArgs false

/-!
# The 376- and 1000-byte patterned arms

Both arms store their digest, OR together calldata window differences (one
literal window for 1000 bytes) and enter the shared chain at word 7.  A zero
result pins every byte through `WindowCover`.
-/

namespace Challenge.Ripemd160.Submission.Proofs.Bytecode.Arms.Long
open Challenge.Ripemd160 EvmSemantics EvmSemantics.EVM YulEvmCompiler Challenge.EvmProof
open Challenge.Ripemd160.Submission.Proofs.Bytecode
open StackRoundTrace StackRoundTemplate DirectLiteralRawV4 DirectLiteralModel J2Moves ReverseLiteralRaw
open Arms.Scan
open PatternedInputData

/-! ## Window xs -/

inductive Item where
  | eq (o s : Nat)
  | lit (o : Nat) (c : Nat)
  deriving DecidableEq

def width (v : Nat) : Nat := if v = 0 then 0 else if v < 256 then 1 else 2

theorem width_lt (v : Nat) : width v < 33 := by unfold width; split <;> (try split) <;> decide

def pushNat (v : Nat) : Instr := .push ⟨width v, width_lt v⟩ (UInt256.ofNat v)

def W (input : ByteArray) (o : Nat) : UInt256 := MachineState.readWord input o

def itemVal (input : ByteArray) : Item → UInt256
  | .eq o s => UInt256.xor (W input s) (W input o)
  | .lit o c => UInt256.xor (W input o) (UInt256.ofNat c)

def itemTemplate : Item → List Instr
  | .eq o s => [pushNat o, .op .CALLDATALOAD, pushNat s, .op .CALLDATALOAD, .op .XOR, .op .OR]
  | .lit o c => [.push ⟨32, by decide⟩ (UInt256.ofNat c), pushNat o, .op .CALLDATALOAD, .op .XOR, .op .OR]

def accVal (input : ByteArray) (a : UInt256) : List Item → UInt256
  | [] => a
  | x :: rest => accVal input (UInt256.lor (itemVal input x) a) rest

def itemsTemplate : List Item → List Instr
  | [] => []
  | x :: rest => itemTemplate x ++ itemsTemplate rest

theorem accVal_zero (input : ByteArray) (a : UInt256) (xs : List Item) :
    accVal input a xs = 0 → a = 0 ∧ ∀ x ∈ xs, itemVal input x = 0 := by
  induction xs generalizing a with
  | nil => intro h; exact ⟨h, by simp⟩
  | cons x rest ih =>
    intro h
    obtain ⟨h1, h2⟩ := ih _ h
    rw [KnownInputLogic.wordOr_eq_zero_iff] at h1
    refine ⟨h1.2, ?_⟩
    intro j hj
    rcases List.mem_cons.mp hj with rfl | hj
    · exact h1.1
    · exact h2 j hj

theorem run_item (s : State) (pc : UInt256) (x : Item) (a : UInt256) (rho : List UInt256)
    (hit : match x with | .eq o t => o < 1024 ∧ t < 1024 | .lit o c => o < 1024 ∧ c < 2^256)
    (hs : rho.length ≤ 990) (hrun : s.halt = .Running) :
    runInstrSeq (itemTemplate x) {s with pc := pc, stack := a :: rho} =
      some {s with pc := pcAfter pc (itemTemplate x), stack := UInt256.lor (itemVal s.executionEnv.calldata x) a :: rho} := by
  have hcap (n : Nat) (hn : n ≤ 20) : rho.length + n < 1024 := by omega
  cases x with
  | eq o t =>
    obtain ⟨ho, ht⟩ := hit
    have hoN : (UInt256.ofNat o).toNat = o := by
      rw [Word.word_toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
    have htN : (UInt256.ofNat t).toNat = t := by
      rw [Word.word_toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
    by_cases h0 : o = 0 <;> by_cases h1 : o < 256 <;> by_cases g0 : t = 0 <;> by_cases g1 : t < 256
    all_goals first
      | (exfalso; omega)
      | (simp (discharger := omega) [itemTemplate, pushNat, width, h0, h1, g0, g1, itemVal, W,
          runInstrSeq, DataStepper.runInstr, pcAfter, hrun, show rho.length < 1024 by omega, hcap,
          UInt256.succ, Instr.size, Nat.add_assoc, hoN, htN, Word.literal_eq_ofNat,
          List.getElem?_cons_zero, List.exchange]
         repeat first | apply And.intro | rfl)
  | lit o c =>
    obtain ⟨ho, hc⟩ := hit
    have hoN : (UInt256.ofNat o).toNat = o := by
      rw [Word.word_toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
    by_cases h0 : o = 0 <;> by_cases h1 : o < 256
    all_goals first
      | (exfalso; omega)
      | (simp (discharger := omega) [itemTemplate, pushNat, width, h0, h1, itemVal, W,
          runInstrSeq, DataStepper.runInstr, pcAfter, hrun, show rho.length < 1024 by omega, hcap,
          UInt256.succ, Instr.size, Nat.add_assoc, hoN, Word.literal_eq_ofNat,
          List.getElem?_cons_zero, List.exchange]
         repeat first | apply And.intro | rfl)

def ItemsOk : List Item → Prop
  | [] => True
  | x :: rest => (match x with | .eq o t => o < 1024 ∧ t < 1024 | .lit o c => o < 1024 ∧ c < 2^256) ∧ ItemsOk rest

theorem run_items (s : State) (pc : UInt256) (xs : List Item) (hok : ItemsOk xs)
    (a : UInt256) (rho : List UInt256)
    (hs : rho.length ≤ 990) (hrun : s.halt = .Running) :
    runInstrSeq (itemsTemplate xs) {s with pc := pc, stack := a :: rho} =
      some {s with pc := pcAfter pc (itemsTemplate xs), stack := accVal s.executionEnv.calldata a xs :: rho} := by
  induction xs generalizing pc a with
  | nil => simp [itemsTemplate, accVal, runInstrSeq, pcAfter]
  | cons x rest ih =>
    have h1 := run_item s pc x a rho hok.1 hs hrun
    have h2 := ih (pc := pcAfter pc (itemTemplate x)) (a := UInt256.lor (itemVal s.executionEnv.calldata x) a) (hok := hok.2)
    have hall := DenseScheduleTrace.runInstrSeq_append_running h1 hrun h2
    simpa only [itemsTemplate, accVal, DenseScheduleTrace.pcAfter_append] using hall


theorem itemsOk_of_check (xs : List Item) (h : xs.all (fun x => match x with
    | .eq o t => decide (o < 1024) && decide (t < 1024)
    | .lit o c => decide (o < 1024) && decide (c < 2^256)) = true) : ItemsOk xs := by
  induction xs with
  | nil => trivial
  | cons x rest ih =>
    simp only [List.all_cons, Bool.and_eq_true] at h
    refine ⟨?_, ih h.2⟩
    cases x <;> simpa using h.1

/-! ## Concrete arms -/

def items376 : List Item := [.eq 288 143, .eq 320 175, .eq 344 199]

def items1000 : List Item :=
  [.eq 256 111, .eq 288 143, .eq 320 175, .eq 352 207, .eq 433 32, .eq 465 64, .eq 502 212,
   .eq 546 0, .eq 578 32, .eq 610 64, .eq 642 96, .eq 674 128, .eq 706 160, .eq 753 62,
   .eq 785 94, .eq 817 126, .eq 849 158, .eq 881 190, .eq 947 0, .eq 910 219, .eq 968 21,
   .eq 721 175, .eq 364 219, .eq 509 219, .eq 470 69,
   .lit 369 46836809398124041301509275424151671459047373308733951134252891636751576645090,
   .eq 514 369, .eq 915 369]

def head376 : List Instr :=
  [pushNat 256, .op .CALLDATALOAD, pushNat 111, .op .CALLDATALOAD, .op .XOR]

def head1000 : List Instr := [pushNat 401, .op .CALLDATALOAD, .op .XOR]

def a376Template : List Instr :=
  DirectDigestRaw.storeTemplate (RecognitionDigest.paddedDigestWord 376) ++ head376 ++
    itemsTemplate items376 ++ jumpTemplate 8446

def a1000Template : List Instr :=
  DirectDigestRaw.storeTemplate (RecognitionDigest.paddedDigestWord 1000) ++ head1000 ++
    itemsTemplate items1000 ++ jumpTemplate 8446

theorem run_head376 (s : State) (pc : UInt256) (rho : List UInt256)
    (hs : rho.length ≤ 990) (hrun : s.halt = .Running) :
    runInstrSeq head376 {s with pc := pc, stack := rho} =
      some {s with pc := pcAfter pc head376, stack := itemVal s.executionEnv.calldata (.eq 256 111) :: rho} := by
  have hcap (n : Nat) (hn : n ≤ 20) : rho.length + n < 1024 := by omega
  simp (discharger := omega) [head376, pushNat, width, itemVal, W,
    runInstrSeq, DataStepper.runInstr, pcAfter, hrun, show rho.length < 1024 by omega, hcap,
    UInt256.succ, Instr.size, Nat.add_assoc, Word.word_toNat_ofNat, Word.literal_eq_ofNat,
    List.getElem?_cons_zero, List.exchange]
  repeat first | apply And.intro | rfl

theorem run_head1000 (s : State) (pc : UInt256) (rho : List UInt256)
    (hs : rho.length ≤ 990) (hrun : s.halt = .Running) :
    runInstrSeq head1000 {s with pc := pc, stack := W s.executionEnv.calldata 0 :: rho} =
      some {s with pc := pcAfter pc head1000, stack := itemVal s.executionEnv.calldata (.eq 0 401) :: rho} := by
  have hcap (n : Nat) (hn : n ≤ 20) : rho.length + n < 1024 := by omega
  simp (discharger := omega) [head1000, pushNat, width, itemVal, W,
    runInstrSeq, DataStepper.runInstr, pcAfter, hrun, show rho.length < 1024 by omega, hcap,
    UInt256.succ, Instr.size, Nat.add_assoc, Word.word_toNat_ofNat, Word.literal_eq_ofNat,
    List.getElem?_cons_zero, List.exchange]
  repeat first | apply And.intro | rfl

/-- Digest store from the zero-memory frame, keeping one stack word. -/
theorem run_store1 (input : ByteArray) (pc : UInt256) (n : Nat) (w : UInt256) :
    runInstrSeq (DirectDigestRaw.storeTemplate (RecognitionDigest.paddedDigestWord n))
      {base input with pc := pc, stack := [w]} =
      some {prepared input n with pc := UInt256.add (UInt256.ofNat 24) pc, stack := [w]} := by
  have hac : (base input).activeWordsAfterUInt256 0 32 = UInt256.ofNat 1 := by
    simp [State.activeWordsAfterUInt256,base,initialState,Word.word_toNat_ofNat]
    rfl
  have hr := DirectDigestRaw.run_store (base input) pc
    (RecognitionDigest.paddedDigestWord n) [w] (by simp) rfl
  rw [hr]
  simp only [DirectDigestRaw.stored, hac, DirectDigestRaw.store_pc, prepared, base, digestMemory]
  rfl

def a376Site : GenericRoundSite HoistedInherited.Artifact.submissionArtifact .Osaka a376Template :=
  StackSiteBuilder.ofSlice a376Template 6508 (by rfl)
    (by change 6508 + a376Template.length ≤ HoistedInherited.Artifact.submissionInstructions.length
        rw [HoistedInherited.Artifact.referenceInstructions_count]; decide)
    HoistedInherited.StackRoundData.artifact_code_bound
    (HoistedInherited.StackRoundData.templateWellFormed_mem (instructions := a376Template) (by decide)) (by decide)
theorem a376_pc : a376Site.startPC = UInt256.ofNat 9331 := by
  change UInt256.ofNat (HoistedInherited.Artifact.submissionArtifact.instructionPC 6508) = _
  rw [ArtifactByteLength.instructionPC_eq_byteLength]; decide

def a1000Site : GenericRoundSite HoistedInherited.Artifact.submissionArtifact .Osaka a1000Template :=
  StackSiteBuilder.ofSlice a1000Template 6537 (by rfl)
    (by change 6537 + a1000Template.length ≤ HoistedInherited.Artifact.submissionInstructions.length
        rw [HoistedInherited.Artifact.referenceInstructions_count]; decide)
    HoistedInherited.StackRoundData.artifact_code_bound
    (HoistedInherited.StackRoundData.templateWellFormed_mem (instructions := a1000Template) (by decide)) (by decide)
theorem a1000_pc : a1000Site.startPC = UInt256.ofNat 9394 := by
  change UInt256.ofNat (HoistedInherited.Artifact.submissionArtifact.instructionPC 6537) = _
  rw [ArtifactByteLength.instructionPC_eq_byteLength]; decide

def val376 (input : ByteArray) : UInt256 := accVal input (itemVal input (.eq 256 111)) items376
def val1000 (input : ByteArray) : UInt256 := accVal input (itemVal input (.eq 0 401)) items1000

def gasSteps_a376_entry (input : ByteArray) :
    GasSteps (atState (base input) 9331 []) (atState (prepared input 376) 8446 [val376 input]) := by
  have h1 := Scan.run_store input (UInt256.ofNat 9331) 376
  have h2 := run_head376 (prepared input 376) (UInt256.add (UInt256.ofNat 24) (UInt256.ofNat 9331))
    [] (by simp) rfl
  have h12 := DenseScheduleTrace.runInstrSeq_append_running h1 rfl h2
  have h3 := run_items (prepared input 376)
    (pcAfter (UInt256.add (UInt256.ofNat 24) (UInt256.ofNat 9331)) head376) items376
    (itemsOk_of_check _ (by decide)) (itemVal input (.eq 256 111)) [] (by simp) rfl
  have h123 := DenseScheduleTrace.runInstrSeq_append_running h12 rfl h3
  have h4 := run_jump (prepared input 376)
    (pcAfter (pcAfter (UInt256.add (UInt256.ofNat 24) (UInt256.ofNat 9331)) head376) (itemsTemplate items376))
    8446 [val376 input] (by simp) rfl (by
      change Decode.isValidJumpDest HoistedInherited.Artifact.submissionArtifact.code (UInt256.ofNat 8446).toNat = true
      exact Each.valid_chain8)
  have hall := DenseScheduleTrace.runInstrSeq_append_running h123 rfl h4
  have h' : runInstrSeq a376Template (atState (base input) 9331 []) =
      some (atState (prepared input 376) 8446 [val376 input]) := by
    simpa only [a376Template, atState, List.append_assoc, prepared_calldata, val376] using hall
  exact RecognitionLift.gasSteps_of_raw a376Site _ _ rfl rfl rfl deployAddress_not_precompile
    (by simpa [atState] using a376_pc.symm) (RecognitionLift.advancesAll_sound _ (by decide)) h'

def gasSteps_a1000_entry (input : ByteArray) :
    GasSteps (atState (base input) 9394 [W input 0]) (atState (prepared input 1000) 8446 [val1000 input]) := by
  have h1 := run_store1 input (UInt256.ofNat 9394) 1000 (W input 0)
  have h2 := run_head1000 (prepared input 1000) (UInt256.add (UInt256.ofNat 24) (UInt256.ofNat 9394))
    [] (by simp) rfl
  have h12 := DenseScheduleTrace.runInstrSeq_append_running h1 rfl h2
  have h3 := run_items (prepared input 1000)
    (pcAfter (UInt256.add (UInt256.ofNat 24) (UInt256.ofNat 9394)) head1000) items1000
    (itemsOk_of_check _ (by decide)) (itemVal input (.eq 0 401)) [] (by simp) rfl
  have h123 := DenseScheduleTrace.runInstrSeq_append_running h12 rfl h3
  have h4 := run_jump (prepared input 1000)
    (pcAfter (pcAfter (UInt256.add (UInt256.ofNat 24) (UInt256.ofNat 9394)) head1000) (itemsTemplate items1000))
    8446 [val1000 input] (by simp) rfl (by
      change Decode.isValidJumpDest HoistedInherited.Artifact.submissionArtifact.code (UInt256.ofNat 8446).toNat = true
      exact Each.valid_chain8)
  have hall := DenseScheduleTrace.runInstrSeq_append_running h123 rfl h4
  have h' : runInstrSeq a1000Template (atState (base input) 9394 [W input 0]) =
      some (atState (prepared input 1000) 8446 [val1000 input]) := by
    simpa only [a1000Template, atState, List.append_assoc, prepared_calldata, val1000] using hall
  exact RecognitionLift.gasSteps_of_raw a1000Site _ _ rfl rfl rfl deployAddress_not_precompile
    (by simpa [atState] using a1000_pc.symm) (RecognitionLift.advancesAll_sound _ (by decide)) h'

/-! ## Zero results pin the input -/

theorem chain_words (input : ByteArray) (a : UInt256) (h : (rev input a 8).toNat = 0) :
    a = 0 ∧ ∀ k, k < 8 → MachineState.readWord input (32 * k) =
      MachineState.readWord patternedInput (32 * k) := by
  have h0 : rev input a 8 = 0 := Word.word_ext h
  obtain ⟨ha, hd⟩ := (ZeroTailModel.rev_zero_iff input a 8).mp h0
  refine ⟨ha, fun k hk => ?_⟩
  have := hd k hk
  rw [diff, KnownInputLogic.wordXor_eq_zero_iff] at this
  rw [this, PatternedWordLogic.readWord_patterned]

theorem item_eq (input : ByteArray) (o t : Nat) (h : itemVal input (.eq o t) = 0) :
    MachineState.readWord input o = MachineState.readWord input t := by
  simp only [itemVal, W] at h
  exact ((KnownInputLogic.wordXor_eq_zero_iff _ _).mp h).symm

theorem result376 (input : ByteArray) (hsize : input.size = 376)
    (h : (rev input (val376 input) 8).toNat = 0) : input = RecognitionAccumulator.reference 376 := by
  obtain ⟨ha, h0⟩ := chain_words input _ h
  obtain ⟨hh, hi⟩ := accVal_zero input _ items376 ha
  apply WindowCover.eq_reference input 376 WindowCover.plan376 [] WindowCover.cover376 hsize h0
  · intro p hp
    simp only [WindowCover.plan376, List.mem_cons, List.not_mem_nil, or_false] at hp
    rcases hp with rfl | rfl | rfl | rfl
    · exact item_eq input _ _ hh
    all_goals exact item_eq input _ _ (hi _ (by decide))
  · simp

theorem plan1000_mem : ∀ p ∈ WindowCover.plan1000, p = (401, 0) ∨ Item.eq p.1 p.2 ∈ items1000 := by
  decide

theorem result1000 (input : ByteArray) (hsize : input.size = 1000)
    (h : (rev input (val1000 input) 8).toNat = 0) : input = RecognitionAccumulator.reference 1000 := by
  obtain ⟨ha, h0⟩ := chain_words input _ h
  obtain ⟨hh, hi⟩ := accVal_zero input _ items1000 ha
  apply WindowCover.eq_reference input 1000 WindowCover.plan1000 WindowCover.anchors1000
    WindowCover.cover1000 hsize h0
  · intro p hp
    rcases plan1000_mem p hp with rfl | hm
    · exact (item_eq input _ _ hh).symm
    · exact item_eq input _ _ (hi _ hm)
  · intro a ha'
    simp only [WindowCover.anchors1000, List.mem_cons, List.not_mem_nil, or_false] at ha'
    subst ha'
    have hl := hi (.lit 369 46836809398124041301509275424151671459047373308733951134252891636751576645090) (by decide)
    simp only [itemVal, W, KnownInputLogic.wordXor_eq_zero_iff] at hl
    rw [hl]
    apply Word.word_ext
    rw [Bytes.readWord_toNat, Word.word_toNat_ofNat,
      ← RecognitionAccumulator.bytesToNatPadded_reference 1000 369 32 (by norm_num) (by norm_num),
      ZeroTailModel.bytesToNatPadded_reference_formula 1000 369 32 (by norm_num)]
    decide

/-! ## Outcomes -/

theorem long_correct (input : ByteArray) (hfit : CalldataFits input) (n : Nat)
    (hn : RecognitionAccumulator.Allowed n) (hsize : input.size = n) (v : UInt256)
    (hv : v.toNat = 0 → input = RecognitionAccumulator.reference n)
    (hpre : GasSteps (initialState HoistedInherited.submissionBytecode input 0)
      {prepared input n with
        pc := if v.toNat = 0 then UInt256.ofNat 8758 else UInt256.ofNat 8078, stack := []}) :
    ∃ g₀ : Nat, ∀ gas : Nat, g₀ ≤ gas →
      Eval (initialState HoistedInherited.submissionBytecode input gas) (.returned (spec input)) := by
  have hpos : 0 < input.size := by
    have := RecognitionAccumulator.allowed_bounds n hn
    omega
  by_cases hz : v.toNat = 0
  · rw [if_pos hz] at hpre
    obtain ⟨t, ⟨gt⟩, h1, h2, h3⟩ := Finish.finish_gasSteps input n 8758 Finish.finishSite2 Finish.finishSite2_pc
    apply Finish.of_returned input t (hpre.trans gt) h1 h2
    rw [h3]
    exact Finish.output_spec input n hn (hv hz)
  · rw [if_neg hz] at hpre
    have gf := HoistedInherited.EarlySerializeFallback.gasSteps_of_eq input hfit hpos
      {prepared input n with pc := UInt256.ofNat 8078, stack := []} (digestMemory n)
      (digestMemory_size n) [] (by simp) rfl
    exact HoistedInherited.GenericFramedCorrect.correct input hfit hpos [] (by simp) (hpre.trans gf)

theorem correct376 (input : ByteArray) (hfit : CalldataFits input) (hsize : input.size = 376)
    (g : GasSteps (initialState HoistedInherited.submissionBytecode input 0) (atState (base input) 9331 [])) :
    ∃ g₀ : Nat, ∀ gas : Nat, g₀ ≤ gas →
      Eval (initialState HoistedInherited.submissionBytecode input gas) (.returned (spec input)) :=
  long_correct input hfit 376 (by unfold RecognitionAccumulator.Allowed; omega) hsize _
    (result376 input hsize)
    (g.trans ((gasSteps_a376_entry input).trans (Each.gasSteps_chain8 input 376 (val376 input))))

theorem correct1000 (input : ByteArray) (hfit : CalldataFits input) (hsize : input.size = 1000)
    (g : GasSteps (initialState HoistedInherited.submissionBytecode input 0) (atState (base input) 9394 [W input 0])) :
    ∃ g₀ : Nat, ∀ gas : Nat, g₀ ≤ gas →
      Eval (initialState HoistedInherited.submissionBytecode input gas) (.returned (spec input)) :=
  long_correct input hfit 1000 (by unfold RecognitionAccumulator.Allowed; omega) hsize _
    (result1000 input hsize)
    (g.trans ((gasSteps_a1000_entry input).trans (Each.gasSteps_chain8 input 1000 (val1000 input))))

end Challenge.Ripemd160.Submission.Proofs.Bytecode.Arms.Long
