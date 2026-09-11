import Challenge.Modexp.Submission.Proofs.Fast.CiosReadonlyComponents

set_option warningAsError true
set_option linter.unusedSimpArgs false

namespace Challenge.Modexp.Submission.Proofs.Fast.CiosCarryReadonly
open EvmSemantics EvmSemantics.EVM YulEvmCompiler
open Challenge.Modexp.Submission.Proofs.Bytecode WindowNibbleKernel
open Challenge.Modexp.Submission.Proofs.Fast
open Monpro CiosCached CiosCachedMacCore CiosEndAroundCarry
variable {carrySlot : UInt256}

def cacheStack (bi pbi pa pb flag target2 tl inv m0 aEnd m96 m64 m32 dst ret : UInt256)
    (rest : List UInt256) : List UInt256 :=
  [bi,pbi,pa,pb,flag,carrySlot,allOnes,target2,inv,m0,tl,m96,m64,m32,aEnd,dst,ret] ++ rest

def cachedLoadLow : List Instr := [.op (.Dup ⟨10, by decide⟩), .op .MLOAD]
def cachedMakeMu : List Instr :=
  [.op (.Dup ⟨0, by decide⟩), .op (.Dup ⟨10, by decide⟩), .op .MUL,
   .op (.Swap ⟨0, by decide⟩)]
def cachedLoadMask : List Instr := [.op (.Dup ⟨8, by decide⟩)]

theorem run_cachedLoadLow (s : State) (bi pbi pa pb flag target2 inv m0 aEnd m96 m64 m32 dst ret : UInt256)
    (n : Nat) (rest : List UInt256) (hcap : rest.length ≤ 998) (hn : n ≤ 32)
    (hact : 296 ≤ s.activeWords.toNat) :
    runInstructions cachedLoadLow
      (framed s (UInt256.ofNat 4549)
        (cacheStack (carrySlot := carrySlot) bi pbi pa pb flag target2 (UInt256.ofNat (8224+32*n)) inv m0 aEnd m96 m64 m32 dst ret rest)) =
    some (framed s (UInt256.ofNat 4551)
      ([MachineState.readWord s.memory (8224+32*n)] ++
        cacheStack (carrySlot := carrySlot) bi pbi pa pb flag target2 (UInt256.ofNat (8224+32*n)) inv m0 aEnd m96 m64 m32 dst ret rest)) := by
  have hc17 : rest.length + 17 < 1024 := by omega
  have hc18 : rest.length + 18 < 1024 := by omega
  have hmod : (8224+32*n) %
      115792089237316195423570985008687907853269984665640564039457584007913129639936 =
      8224+32*n := Nat.mod_eq_of_lt (by omega)
  have hactQ := activeWords_fix s (8224+32*n) 32 (by decide) (by omega) hact
  simp [cachedLoadLow, runInstructions, Challenge.EvmProof.Stepper.runInstr,
    framed, cacheStack, Nat.add_assoc, hc17, hc18, State.activeWordsAfterUInt256,
    Challenge.EvmProof.Word.succ_ofNat_mod,
    Challenge.EvmProof.Word.word_toNat_ofNat, hmod, hactQ]

theorem run_cachedMakeMu (s : State) (bi pbi pa pb flag target2 tl inv m0 aEnd m96 m64 m32 dst ret t0 : UInt256)
    (rest : List UInt256) (hcap : rest.length ≤ 998) :
    runInstructions cachedMakeMu
      (framed s (UInt256.ofNat 4551)
        ([t0] ++ cacheStack (carrySlot := carrySlot) bi pbi pa pb flag target2 tl inv m0 aEnd m96 m64 m32 dst ret rest)) =
    some (framed s (UInt256.ofNat 4555)
      ([t0, inv*t0] ++ cacheStack (carrySlot := carrySlot) bi pbi pa pb flag target2 tl inv m0 aEnd m96 m64 m32 dst ret rest)) := by
  have hc18 : rest.length + 18 < 1024 := by omega
  have hc19 : rest.length + 19 < 1024 := by omega
  have hc20 : rest.length + 20 < 1024 := by omega
  simp [cachedMakeMu, runInstructions, Challenge.EvmProof.Stepper.runInstr,
    framed, cacheStack, Nat.add_assoc, hc18, hc19, hc20, List.exchange,
    Challenge.EvmProof.Word.succ_ofNat_mod]

theorem run_cachedLoadMask (s : State) (bi pbi pa pb flag target2 tl inv m0 aEnd m96 m64 m32 dst ret mu t0 : UInt256)
    (rest : List UInt256) (hcap : rest.length ≤ 998) :
    runInstructions cachedLoadMask
      (framed s (UInt256.ofNat 4555)
        ([t0,mu] ++ cacheStack (carrySlot := carrySlot) bi pbi pa pb flag target2 tl inv m0 aEnd m96 m64 m32 dst ret rest)) =
    some (framed s (UInt256.ofNat 4556)
      ([maxWord,t0,mu] ++ cacheStack (carrySlot := carrySlot) bi pbi pa pb flag target2 tl inv m0 aEnd m96 m64 m32 dst ret rest)) := by
  have hc19 : rest.length + 19 < 1024 := by omega
  simp [cachedLoadMask, runInstructions, Challenge.EvmProof.Stepper.runInstr,
    framed, cacheStack, Nat.add_assoc, hc19, allOnes_value, Challenge.EvmProof.Word.succ_ofNat_mod]

def makeModProduct : List Instr :=
  [.op (.Dup ⟨2, by decide⟩), .op (.Dup ⟨13, by decide⟩), .op .MULMOD]

def finishCarry : List Instr :=
  [.op (.Dup ⟨1, by decide⟩), .op .ADD, .op (.Dup ⟨0, by decide⟩),
   .op (.Swap ⟨1, by decide⟩), .op .GT, .op .ADD]

theorem run_cachedMakeModProduct (s : State)
    (bi pbi pa pb flag target2 tl inv m0 aEnd m96 m64 m32 dst ret mu t0 : UInt256)
    (rest : List UInt256) (hcap : rest.length ≤ 998) :
    runInstructions makeModProduct
      (framed s (UInt256.ofNat 4556)
        ([maxWord,t0,mu] ++ cacheStack (carrySlot := carrySlot) bi pbi pa pb flag target2 tl inv m0 aEnd m96 m64 m32 dst ret rest)) =
    some (framed s (UInt256.ofNat 4559)
      ([UInt256.mulMod m0 mu maxWord,t0,mu] ++
        cacheStack (carrySlot := carrySlot) bi pbi pa pb flag target2 tl inv m0 aEnd m96 m64 m32 dst ret rest)) := by
  have hc20 : rest.length + 20 < 1024 := by omega
  have hc21 : rest.length + 21 < 1024 := by omega
  have hc22 : rest.length + 22 < 1024 := by omega
  simp [makeModProduct,
    runInstructions, Challenge.EvmProof.Stepper.runInstr,
    framed, cacheStack, Nat.add_assoc, hc20, hc21, hc22,
    allOnes_value, maxWord, Challenge.EvmProof.Word.succ_ofNat_mod]

theorem run_cachedFinishCarry (s : State)
    (bi pbi pa pb flag target2 tl inv m0 aEnd m96 m64 m32 dst ret mm mu t0 : UInt256)
    (rest : List UInt256) (hcap : rest.length ≤ 998) :
    runInstructions finishCarry
      (framed s (UInt256.ofNat 4559)
        ([mm,t0,mu] ++ cacheStack (carrySlot := carrySlot) bi pbi pa pb flag target2 tl inv m0 aEnd m96 m64 m32 dst ret rest)) =
    some (framed s (UInt256.ofNat 4565)
      ([endCarry t0 mm,mu] ++ cacheStack (carrySlot := carrySlot) bi pbi pa pb flag target2 tl inv m0 aEnd m96 m64 m32 dst ret rest)) := by
  have hc20 : rest.length + 20 < 1024 := by omega
  have hc21 : rest.length + 21 < 1024 := by omega
  simp [finishCarry,
    runInstructions, Challenge.EvmProof.Stepper.runInstr,
    framed, cacheStack, Nat.add_assoc, hc20, hc21, endCarry,
    List.exchange, Challenge.EvmProof.Word.succ_ofNat_mod]

def cachedProduct : List Instr :=
  (((cachedLoadLow ++ cachedMakeMu) ++ cachedLoadMask) ++
    makeModProduct) ++ finishCarry

theorem run_cachedProduct (s : State) (bi pbi pa pb flag target2 inv m0 aEnd m96 m64 m32 dst ret : UInt256)
    (n : Nat) (rest : List UInt256) (hcap : rest.length ≤ 998) (hn : n ≤ 32)
    (hact : 296 ≤ s.activeWords.toNat) :
    let tl := UInt256.ofNat (8224+32*n)
    let t0 := MachineState.readWord s.memory (8224+32*n)
    runInstructions cachedProduct
      (framed s (UInt256.ofNat 4549)
        (cacheStack (carrySlot := carrySlot) bi pbi pa pb flag target2 tl inv m0 aEnd m96 m64 m32 dst ret rest)) =
    some (framed s (UInt256.ofNat 4565)
      ([endCarry t0 (UInt256.mulMod m0 (inv*t0) maxWord),inv*t0] ++
        cacheStack (carrySlot := carrySlot) bi pbi pa pb flag target2 tl inv m0 aEnd m96 m64 m32 dst ret rest)) := by
  let tl := UInt256.ofNat (8224+32*n)
  let t0 := MachineState.readWord s.memory (8224+32*n)
  have h1 := run_cachedLoadLow (carrySlot := carrySlot) s bi pbi pa pb flag target2 inv m0 aEnd m96 m64 m32 dst ret n rest hcap hn hact
  have h2 := run_cachedMakeMu (carrySlot := carrySlot) s bi pbi pa pb flag target2 tl inv m0 aEnd m96 m64 m32 dst ret t0 rest hcap
  have h3 := run_cachedLoadMask (carrySlot := carrySlot) s bi pbi pa pb flag target2 tl inv m0 aEnd m96 m64 m32 dst ret (inv*t0) t0 rest hcap
  have h4 := run_cachedMakeModProduct (carrySlot := carrySlot) s bi pbi pa pb flag target2 tl inv m0 aEnd m96 m64 m32 dst ret (inv*t0) t0 rest hcap
  have h5 := run_cachedFinishCarry (carrySlot := carrySlot) s bi pbi pa pb flag target2 tl inv m0 aEnd m96 m64 m32 dst ret
    (UInt256.mulMod m0 (inv*t0) maxWord) (inv*t0) t0 rest hcap
  have h12 := runInstructions_append_some _ _ _ _ _ h1 h2
  have h123 := runInstructions_append_some _ _ _ _ _ h12 h3
  have h1234 := runInstructions_append_some _ _ _ _ _ h123 h4
  exact runInstructions_append_some _ _ _ _ _ h1234 h5


theorem run_cachedProduct_model (s : State)
    (bi pbi pa pb flag target2 tl inv m0 aEnd m96 m64 m32 dst ret : UInt256)
    (n : Nat) (rest : List UInt256) (hcap : rest.length ≤ 998) (hn : n ≤ 32)
    (hact : 296 ≤ s.activeWords.toNat)
    (hc : CiosReadonly.ReadonlyCache s.memory n tl inv m0)
    (hminv : CiosCachedMidMemory.inverseInvariant s.memory n) :
    runInstructions cachedProduct
      (framed s (UInt256.ofNat 4549)
        (cacheStack (carrySlot := carrySlot) bi pbi pa pb flag target2 tl inv m0 aEnd m96 m64 m32 dst ret rest)) =
    some (framed s (UInt256.ofNat 4565)
      ([rowC0 s.memory n,rowMu s.memory n] ++
        cacheStack (carrySlot := carrySlot) bi pbi pa pb flag target2 tl inv m0 aEnd m96 m64 m32 dst ret rest)) := by
  rw [hc.lowAddress, hc.inverse, hc.modulusLow]
  have hr := run_cachedProduct (carrySlot := carrySlot) s bi pbi pa pb flag target2
    (MachineState.readWord s.memory 9376) (MachineState.readWord s.memory (32*n-32))
    aEnd m96 m64 m32 dst ret n rest hcap hn hact
  have hcarry := row_carry_swapped (MachineState.readWord s.memory (32*n-32))
    (MachineState.readWord s.memory 9376) (MachineState.readWord s.memory (8224+32*n)) hminv
  simpa only [hcarry, rowC0, rowMu] using hr




#print axioms run_cachedProduct
#print axioms run_cachedProduct_model

end Challenge.Modexp.Submission.Proofs.Fast.CiosCarryReadonly
