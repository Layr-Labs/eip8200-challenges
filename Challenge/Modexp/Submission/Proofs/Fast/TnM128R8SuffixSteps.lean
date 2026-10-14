import Challenge.Modexp.Submission.Proofs.Fast.TnM128CandidateBlocks

set_option warningAsError true
set_option linter.unusedSimpArgs false
set_option maxRecDepth 40000
set_option maxHeartbeats 8000000

/-!
# Row 0 reduction copy `R_0`

Row 0 of the eight-limb square runs its own copy of the reduction row at pc 5080. The
first-row block falls into it; it has no JUMPDEST and no loop test, and it falls into the
row-1 diagonal at 5320 with the frame the shared row's taken `JUMPI` would leave.
-/

namespace Challenge.Modexp.Submission.Proofs.Fast.TnM128R8SuffixSteps

open EvmSemantics EvmSemantics.EVM YulEvmCompiler
open Challenge.Modexp.Submission.Proofs.Bytecode WindowNibbleKernel
open Challenge.Modexp.Submission.Proofs.Fast Monpro CiosCached CiosCachedMacCore
open CiosReadonly CiosCachedMidMemory WindowTwentyOneBinding TnCacheReductionTrace
open Challenge.EvmProof

/-- `TnMod128Chain.prefixProgram` without its entry JUMPDEST. -/
def prefixBody : List Instr :=
  ((TnCacheL2Trace.l2ProgramFrame 2304 2336 ++ TnMod128Trace.program160) ++
    TnMod128Trace.program) ++ TnCacheExtraTrace.extraProgramZeroNarrow 2208 2240

/-- `TnMod128Chain.suffix` without its entry JUMPDEST. -/
def suffixBody : List Instr :=
  (TnMod128Trace.program64 ++ TnMod128Trace.program32) ++
    CiosCachedLast.l2LastProgram 0 0 2112 2144

def body : List Instr := prefixBody ++ suffixBody

/-- `TnCacheFrameOps.advance` without the loop test `DUP1 DUP3 JUMPI`. -/
def advanceFall : List Instr := [.push 1 32, .op .ADD]

/-- `TnCacheRowTrace.tail` without the loop test. -/
def tailFall : List Instr := TnCacheStoreAt.tail16 ++ advanceFall

theorem run_prefixBody (s : State) (pc : Nat) (mem : ByteArray) (bi mu c0 : UInt256)
    (pbi hd pb ent tn m128 tl inv m0 aEnd m96 m64 m32 dst ret : UInt256)
    (rest : List UInt256) (hcap : rest.length ≤ 998)
    (hact : 88 ≤ s.activeWords.toNat)
    (hc : TnCacheExtraTrace.ExtraCache mem m96 m64 m32)
    (hcache : m128 = MachineState.readWord mem 128)
    (hm0 : m0 = MachineState.readWord mem 160)
    (hpb : pb = MachineState.readWord mem 192) :
    runInstructions prefixBody
      (TnCacheL2Trace.state s (UInt256.ofNat pc) mem bi mu c0 8 0
        pbi hd pb ent m32 m128 m64 (m0 :: tl :: m96 :: inv :: tn :: aEnd :: dst :: ret :: rest)) =
    some (TnCacheL2Trace.state s (UInt256.ofNat (pc+128)) mem bi mu c0 8 4
      pbi hd pb ent m32 m128 m64 (m0 :: tl :: m96 :: inv :: tn :: aEnd :: dst :: ret :: rest)) := by
  have hrest : (m0 :: tl :: m96 :: inv :: tn :: aEnd :: dst :: ret :: rest).length ≤ 1006 := by
    simp only [List.length_cons]; omega
  have h1 := TnCacheL2Trace.run_stepFrame s (UInt256.ofNat pc) mem bi mu c0 8 0
    2304 2336 (by decide) (by decide)
    pbi hd pb ent m32 m128 m64 (m0 :: tl :: m96 :: inv :: tn :: aEnd :: dst :: ret :: rest)
    hrest hact (by decide) (by decide) hpb
  have h2 := TnMod128Trace.run_step160 s (UInt256.ofNat (pc+32)) mem bi mu c0
    pbi hd pb ent m32 m128 m64 m0 (tl :: m96 :: inv :: tn :: aEnd :: dst :: ret :: rest)
    (by simp only [List.length_cons]; omega) hact hm0
  have h3 := TnMod128Trace.run_step s (UInt256.ofNat (pc+64)) mem bi mu c0
    pbi hd pb ent m32 m128 m64 (m0 :: tl :: m96 :: inv :: tn :: aEnd :: dst :: ret :: rest)
    hrest hact hcache
  have h4 := TnCacheExtraTrace.run_extraStepZeroNarrow s (UInt256.ofNat (pc+96)) mem bi mu c0 8 3
    96 2208 2240 (by decide) (by decide) (by decide) (by decide)
    pbi hd pb ent m32 m128 tl m64 m0 aEnd m96 inv tn dst ret rest hcap hact (by decide) (by decide) hc
  simp only [Challenge.EvmProof.Word.ofNat_add_mod, Nat.add_assoc, Nat.reduceAdd, Fin.val_ofNat] at h1 h2 h3 h4
  have h12 := runInstructions_append_some _ _ _ _ _ h1 h2
  have h123 := runInstructions_append_some _ _ _ _ _ h12 h3
  exact runInstructions_append_some _ _ _ _ _ h123 h4

theorem run_suffixBody (s : State) (pc : Nat) (mem : ByteArray) (bi mu c0 : UInt256)
    (pbi hd pb ent tn target tl inv m0 aEnd m96 m64 m32 dst ret : UInt256)
    (rest : List UInt256) (hcap : rest.length ≤ 998)
    (hact : 88 ≤ s.activeWords.toNat)
    (hc : TnCacheExtraTrace.ExtraCache mem m96 m64 m32) :
    runInstructions suffixBody
      (TnCacheL2Trace.state s (UInt256.ofNat pc) mem bi mu c0 8 4
        pbi hd pb ent m32 target m64 (m0 :: tl :: m96 :: inv :: tn :: aEnd :: dst :: ret :: rest)) =
    some (TnCacheLastTrace.lastState s (UInt256.ofNat (pc+97)) mem bi mu c0 8 7
      pbi hd pb ent m32 target m64 (m0 :: tl :: m96 :: inv :: tn :: aEnd :: dst :: ret :: rest)) := by
  have hrest : (m0 :: tl :: m96 :: inv :: tn :: aEnd :: dst :: ret :: rest).length ≤ 1006 := by
    simp only [List.length_cons]; omega
  have h1 := TnMod128Trace.run_step64 s (UInt256.ofNat pc) mem bi mu c0 8 4
    pbi hd pb ent m32 target m64 (m0 :: tl :: m96 :: inv :: tn :: aEnd :: dst :: ret :: rest)
    hrest hact (by decide) (by decide) hc.word64
  have h2 := TnMod128Trace.run_step32 s (UInt256.ofNat (pc+32)) mem bi mu c0 8 5
    pbi hd pb ent m32 target m64 (m0 :: tl :: m96 :: inv :: tn :: aEnd :: dst :: ret :: rest)
    hrest hact (by decide) (by decide) hc.word32
  have h3 := TnCacheLastTrace.run_stepLast 0 s (UInt256.ofNat (pc+64)) mem bi mu c0 8 6
    0 2112 2144 (by change 0 = _; omega) (by change 2112 = _; omega) (by change 2144 = _; omega)
    pbi hd pb ent m32 target m64 (m0 :: tl :: m96 :: inv :: tn :: aEnd :: dst :: ret :: rest)
    (by simp only [List.length_cons]; omega) hact (by decide) (by decide) (by intro _; rfl)
  simp only [Challenge.EvmProof.Word.ofNat_add_mod, Nat.add_assoc, Nat.reduceAdd] at h1 h2 h3
  have h12 := runInstructions_append_some _ _ _ _ _ h1 h2
  exact runInstructions_append_some _ _ _ _ _ h12 h3

theorem run_body (s : State) (pc : Nat) (mem : ByteArray) (bi mu c0 : UInt256)
    (pbi hd pb ent tn m128 tl inv m0 aEnd m96 m64 m32 dst ret : UInt256)
    (rest : List UInt256) (hcap : rest.length ≤ 998)
    (hact : 88 ≤ s.activeWords.toNat)
    (hc : TnCacheExtraTrace.ExtraCache mem m96 m64 m32)
    (hcache : m128 = MachineState.readWord mem 128)
    (hm0 : m0 = MachineState.readWord mem 160)
    (hpb : pb = MachineState.readWord mem 192) :
    runInstructions body
      (TnCacheL2Trace.state s (UInt256.ofNat pc) mem bi mu c0 8 0
        pbi hd pb ent m32 m128 m64 (m0 :: tl :: m96 :: inv :: tn :: aEnd :: dst :: ret :: rest)) =
    some (TnCacheLastTrace.lastState s (UInt256.ofNat (pc+225)) mem bi mu c0 8 (8-1)
      pbi hd pb ent m32 m128 m64 (m0 :: tl :: m96 :: inv :: tn :: aEnd :: dst :: ret :: rest)) := by
  have hp := run_prefixBody s pc mem bi mu c0 pbi hd pb ent tn m128 tl inv m0 aEnd m96 m64 m32 dst ret
    rest hcap hact hc hcache hm0 hpb
  have hs := run_suffixBody s (pc+128) mem bi mu c0 pbi hd pb ent tn m128 tl inv m0 aEnd m96 m64 m32
    dst ret rest hcap hact hc
  have both := runInstructions_append_some _ _ _ _ _ hp hs
  simpa [body, Nat.add_assoc] using both

theorem run_advanceFall (pc0 : Nat) (s : State) (pbi hd pb ent tn target inv : UInt256)
    (rest : List UInt256) (hcap : rest.length ≤ 1006) :
    runInstructions advanceFall
      (framed s (UInt256.ofNat pc0) (TnCacheFrameOps.frame pbi hd pb ent tn target inv rest)) =
    some (framed s (UInt256.ofNat (pc0+3))
      (TnCacheFrameOps.frame (UInt256.ofNat 32+pbi) hd pb ent tn target inv rest)) := by
  have hc8 : rest.length+8 < 1024 := by omega
  have hc9 : rest.length < 1015 := by omega
  simp [advanceFall, TnCacheFrameOps.frame, runInstructions, framed, Challenge.EvmProof.Stepper.runInstr,
    hc8, hc9, Nat.add_assoc,
    Challenge.EvmProof.Word.literal_eq_ofNat, Challenge.EvmProof.Word.word_toNat_ofNat,
    Challenge.EvmProof.Word.succ_ofNat_mod, Challenge.EvmProof.Word.ofNat_add_mod]

theorem run_tailFall (pc0 : Nat) (s : State)
    (c f pbi hd pb ent w5 target w8 r0 r1 r2 r3 tn : UInt256)
    (rest : List UInt256) (hcap : rest.length ≤ 1001) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions tailFall
      (framed s (UInt256.ofNat pc0)
        ([c,f,pbi,hd,pb,ent,w5,allOnes,target,w8,r0,r1,r2,r3,tn] ++ rest)) =
    some (framed {s with memory := TnCacheMemory.put s.memory (tn+c) 2112}
      (UInt256.ofNat (pc0+15))
      (TnCacheFrameOps.frame (UInt256.ofNat 32+pbi) hd pb ent w5 target w8
        (r0 :: r1 :: r2 :: r3 :: (UInt256.lt (tn+c) c+f) :: rest))) := by
  have hs := TnCacheStoreAt.run_tail16 pc0 s c f pbi hd pb ent w5 target w8 r0 r1 r2 r3 tn rest hcap hact
  have ha := run_advanceFall (pc0+12)
    {s with memory := TnCacheMemory.put s.memory (tn+c) 2112}
    pbi hd pb ent w5 target w8 (r0 :: r1 :: r2 :: r3 :: (UInt256.lt (tn+c) c+f) :: rest)
    (by simp only [List.length_cons]; omega)
  have both := runInstructions_append_some _ _ _ _ _ hs ha
  simpa only [tailFall, TnCacheMemory.put, TnCacheFrameOps.frame, List.cons_append, List.nil_append,
    Nat.add_zero, Nat.add_assoc, Nat.reduceAdd] using both

/-- `R_0`'s reduction cells: 197 instructions from index 4035 (pc 5080). -/
def bodyBlock : Block TnM128CandidateArtifact.submissionArtifact .Osaka 5053 body :=
  WindowTwentyOneSlice.block TnM128CandidateArtifact.allWellFormed 4009 197 5053 body
    (by decide) (by rfl) (by rfl) (by decide)

/-- `R_0`'s tail: 12 instructions from index 4232 (pc 5305), falling into the diagonal at 5320. -/
def tailBlock : Block TnM128CandidateArtifact.submissionArtifact .Osaka 5278 tailFall :=
  WindowTwentyOneSlice.block TnM128CandidateArtifact.allWellFormed 4206 12 5278 tailFall
    (by decide) (by rfl) (by rfl) (by decide)

/-- Row 0's reduction: the shared row's carry-cache model, ending at the row-1 diagonal 5320. -/
noncomputable def suffix_steps (s : State)
    (env : Environment TnM128CandidateArtifact.submissionArtifact .Osaka s)
    (q : MacState) (tn : UInt256)
    (pbi hd pb ent m128 tl inv m0 aEnd m96 m64 m32 dst ret : UInt256)
    (rest : List UInt256) (hcap : rest.length ≤ 998)
    (hact : 88 ≤ s.activeWords.toNat)
    (he : TnCacheExtraTrace.ExtraCache q.memory m96 m64 m32)
    (hcache : m128 = MachineState.readWord q.memory 128)
    (hm0 : m0 = MachineState.readWord q.memory 160)
    (hpb : pb = MachineState.readWord q.memory 192) :
    GasSteps
      (TnCacheL2Trace.state {s with memory := q.memory} (UInt256.ofNat 5053)
        q.memory (UInt256.lt (tn+q.carry) q.carry) (rowMu q.memory 8) (rowC0 q.memory 8)
        8 0 pbi hd pb ent m32 m128 m64
        (m0 :: tl :: m96 :: inv :: (tn+q.carry) :: aEnd :: dst :: ret :: rest))
      (framed {s with memory := (TnCacheSquareModel.fromL1 q tn 8).memory}
        (UInt256.ofNat 5293)
        (TnCacheFrameOps.frame (UInt256.ofNat 32+pbi) hd pb ent
          m32 m128 m64
          (m0 :: tl :: m96 :: inv :: (TnCacheSquareModel.fromL1 q tn 8).tn :: aEnd :: dst :: ret :: rest))) := by
  let st : State := {s with memory := q.memory}
  let flag := UInt256.lt (tn+q.carry) q.carry
  let mem2 := (l2Step q.memory (rowMu q.memory 8) (rowC0 q.memory 8) 8 (8-1)).memory
  let carry2 := (l2Step q.memory (rowMu q.memory 8) (rowC0 q.memory 8) 8 (8-1)).carry
  let tl4 := aEnd :: dst :: ret :: rest
  have htl4 : tl4.length ≤ 1001 := by simp only [tl4, List.length_cons]; omega
  let tail := m0 :: tl :: m96 :: inv :: (tn+q.carry) :: tl4
  have hreduce := run_body st 5053 q.memory flag (rowMu q.memory 8)
    (rowC0 q.memory 8) pbi hd pb ent (tn+q.carry) m128
    tl inv m0 aEnd m96 m64 m32 dst ret rest hcap hact he hcache hm0 hpb
  have htailrun := run_tailFall (5053+225)
    {s with memory := mem2} carry2 flag pbi hd pb ent m32
    m128 m64 m0 tl m96 inv (tn+q.carry) tl4 htl4 hact
  have hflag : UInt256.lt (tn+q.carry+carry2) carry2+flag =
      flag+UInt256.lt (tn+q.carry+carry2) carry2 := by
    apply Challenge.EvmProof.Word.word_ext
    simp only [Challenge.EvmProof.Word.word_toNat_add, Nat.add_comm]
  rw [hflag] at htailrun
  have hlast : runInstructions tailFall
      (TnCacheLastTrace.lastState st (UInt256.ofNat (5053+225))
        q.memory flag (rowMu q.memory 8) (rowC0 q.memory 8) 8 (8-1)
        pbi hd pb ent m32 m128 m64 tail) =
      some (framed {s with memory := (TnCacheSquareModel.fromL1 q tn 8).memory}
        (UInt256.ofNat 5293)
        (TnCacheFrameOps.frame (UInt256.ofNat 32+pbi) hd pb ent
          m32 m128 m64 (m0 :: tl :: m96 :: inv :: (TnCacheSquareModel.fromL1 q tn 8).tn :: tl4))) := by
    simpa only [TnCacheLastTrace.lastState, tail, tl4, st, framed, mem2, carry2,
      TnCacheSquareModel.fromL1, flag, List.cons_append, List.nil_append, Nat.reduceAdd] using htailrun
  have g1 : GasSteps
      (TnCacheL2Trace.state st (UInt256.ofNat 5053) q.memory flag
        (rowMu q.memory 8) (rowC0 q.memory 8) 8 0 pbi hd pb ent m32
        m128 m64 tail)
      (TnCacheLastTrace.lastState st (UInt256.ofNat (5053+225))
        q.memory flag (rowMu q.memory 8) (rowC0 q.memory 8) 8 (8-1)
        pbi hd pb ent m32 m128 m64 tail) := by
    exact bodyBlock.steps (env.transfer rfl rfl) rfl hreduce
  have hpc : (TnCacheLastTrace.lastState st
      (UInt256.ofNat (5053+225)) q.memory flag
      (rowMu q.memory 8) (rowC0 q.memory 8) 8 (8-1)
      pbi hd pb ent m32 m128 m64 tail).pc =
      UInt256.ofNat 5278 := by
    change UInt256.ofNat (5053+225) = UInt256.ofNat 5278
    rfl
  have g2 := tailBlock.steps
    (s := TnCacheLastTrace.lastState st
      (UInt256.ofNat (5053+225)) q.memory flag
      (rowMu q.memory 8) (rowC0 q.memory 8) 8 (8-1)
      pbi hd pb ent m32 m128 m64 tail)
    (env.transfer rfl rfl) hpc hlast
  simpa only [st, tail, tl4] using g1.trans g2

#print axioms run_body
#print axioms run_tailFall
#print axioms suffix_steps
end Challenge.Modexp.Submission.Proofs.Fast.TnM128R8SuffixSteps
