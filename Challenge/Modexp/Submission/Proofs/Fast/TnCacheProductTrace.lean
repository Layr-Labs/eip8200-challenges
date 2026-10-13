import Challenge.Modexp.Submission.Proofs.Fast.CiosReadonlyComponents
set_option warningAsError true
set_option linter.unusedSimpArgs false
namespace Challenge.Modexp.Submission.Proofs.Fast.TnCacheProductTrace
open EvmSemantics EvmSemantics.EVM YulEvmCompiler
open Challenge.Modexp.Submission.Proofs.Bytecode
open Challenge.Modexp.Submission.Proofs.Fast
open WindowNibbleKernel CiosCachedMacCore CiosCached CiosCachedMidDefs Monpro CiosEndAroundCarry CiosCachedMidMemory CiosReadonly

def cacheStack (bi pbi pa pb flag tn target2 tl inv m0 aEnd m96 m64 m32 dst ret : UInt256)
    (rest : List UInt256) : List UInt256 :=
  [bi,pbi,pa,pb,flag,tn,allOnes,target2,inv,m0,tl,m96,m64,m32,aEnd,dst,ret] ++ rest

def cachedLoadLow : List Instr := [.op (.Dup ⟨10, by decide⟩), .op .MLOAD]
def cachedMakeMu : List Instr :=
  [.op (.Dup ⟨0, by decide⟩), .op (.Dup ⟨10, by decide⟩), .op .MUL,
   .op (.Swap ⟨0, by decide⟩)]
def cachedLoadMask : List Instr := [.op (.Dup ⟨8, by decide⟩)]

theorem run_cachedLoadLow (pc0 : Nat) (s : State) (bi pbi pa pb flag tn target2 inv m0 aEnd m96 m64 m32 dst ret : UInt256)
    (n : Nat) (rest : List UInt256) (hcap : rest.length ≤ 998) (hn : n ≤ 8)
    (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions cachedLoadLow
      (framed s (UInt256.ofNat (pc0 + 0))
        (cacheStack bi pbi pa pb flag tn target2 (UInt256.ofNat (2080+32*n)) inv m0 aEnd m96 m64 m32 dst ret rest)) =
    some (framed s (UInt256.ofNat (pc0 + 2))
      ([MachineState.readWord s.memory (2080+32*n)] ++
        cacheStack bi pbi pa pb flag tn target2 (UInt256.ofNat (2080+32*n)) inv m0 aEnd m96 m64 m32 dst ret rest)) := by
  have hc17 : rest.length + 17 < 1024 := by omega
  have hc18 : rest.length + 18 < 1024 := by omega
  have hmod : (2080+32*n) %
      115792089237316195423570985008687907853269984665640564039457584007913129639936 =
      2080+32*n := Nat.mod_eq_of_lt (by omega)
  have hactQ := activeWords_fix s (2080+32*n) 32 (by decide) (by omega) hact
  simp [cachedLoadLow, runInstructions, Challenge.EvmProof.Stepper.runInstr,
    framed, cacheStack, baseStack, Nat.add_assoc, hc17, hc18, State.activeWordsAfterUInt256,
    Challenge.EvmProof.Word.succ_ofNat_mod,
    Challenge.EvmProof.Word.word_toNat_ofNat, hmod, hactQ]

theorem run_cachedMakeMu (pc0 : Nat) (s : State) (bi pbi pa pb flag tn target2 tl inv m0 aEnd m96 m64 m32 dst ret t0 : UInt256)
    (rest : List UInt256) (hcap : rest.length ≤ 998) :
    runInstructions cachedMakeMu
      (framed s (UInt256.ofNat (pc0 + 2))
        ([t0] ++ cacheStack bi pbi pa pb flag tn target2 tl inv m0 aEnd m96 m64 m32 dst ret rest)) =
    some (framed s (UInt256.ofNat (pc0 + 6))
      ([t0, inv*t0] ++ cacheStack bi pbi pa pb flag tn target2 tl inv m0 aEnd m96 m64 m32 dst ret rest)) := by
  have hc18 : rest.length + 18 < 1024 := by omega
  have hc19 : rest.length + 19 < 1024 := by omega
  have hc20 : rest.length + 20 < 1024 := by omega
  simp [cachedMakeMu, runInstructions, Challenge.EvmProof.Stepper.runInstr,
    framed, cacheStack, baseStack, Nat.add_assoc, hc18, hc19, hc20, List.exchange,
    Challenge.EvmProof.Word.succ_ofNat_mod]

theorem run_cachedLoadMask (pc0 : Nat) (s : State) (bi pbi pa pb flag tn target2 tl inv m0 aEnd m96 m64 m32 dst ret mu t0 : UInt256)
    (rest : List UInt256) (hcap : rest.length ≤ 998) :
    runInstructions cachedLoadMask
      (framed s (UInt256.ofNat (pc0 + 6))
        ([t0,mu] ++ cacheStack bi pbi pa pb flag tn target2 tl inv m0 aEnd m96 m64 m32 dst ret rest)) =
    some (framed s (UInt256.ofNat (pc0 + 7))
      ([maxWord,t0,mu] ++ cacheStack bi pbi pa pb flag tn target2 tl inv m0 aEnd m96 m64 m32 dst ret rest)) := by
  have hc19 : rest.length + 19 < 1024 := by omega
  simp [cachedLoadMask, runInstructions, Challenge.EvmProof.Stepper.runInstr,
    framed, cacheStack, baseStack, Nat.add_assoc, hc19, allOnes_value, Challenge.EvmProof.Word.succ_ofNat_mod]

def makeModProduct : List Instr :=
  [.op (.Dup ⟨2, by decide⟩), .op (.Dup ⟨13, by decide⟩), .op .MULMOD]

def finishCarry : List Instr :=
  [.op (.Dup ⟨9, by decide⟩), .op (.Swap ⟨1, by decide⟩), .op .ADDMOD]

theorem run_cachedMakeModProduct (pc0 : Nat) (s : State)
    (bi pbi pa pb flag tn target2 tl inv m0 aEnd m96 m64 m32 dst ret mu t0 : UInt256)
    (rest : List UInt256) (hcap : rest.length ≤ 998) :
    runInstructions makeModProduct
      (framed s (UInt256.ofNat (pc0 + 7))
        ([maxWord,t0,mu] ++ cacheStack bi pbi pa pb flag tn target2 tl inv m0 aEnd m96 m64 m32 dst ret rest)) =
    some (framed s (UInt256.ofNat (pc0 + 10))
      ([UInt256.mulMod m0 mu maxWord,t0,mu] ++
        cacheStack bi pbi pa pb flag tn target2 tl inv m0 aEnd m96 m64 m32 dst ret rest)) := by
  have hc20 : rest.length + 20 < 1024 := by omega
  have hc21 : rest.length + 21 < 1024 := by omega
  have hc22 : rest.length + 22 < 1024 := by omega
  simp [makeModProduct,
    runInstructions, Challenge.EvmProof.Stepper.runInstr,
    framed, cacheStack, baseStack, Nat.add_assoc, hc20, hc21, hc22,
    allOnes_value, maxWord, Challenge.EvmProof.Word.succ_ofNat_mod]

theorem run_cachedFinishCarry (pc0 : Nat) (s : State)
    (bi pbi pa pb flag tn target2 tl inv m0 aEnd m96 m64 m32 dst ret mm mu t0 : UInt256)
    (rest : List UInt256) (hcap : rest.length ≤ 998) :
    runInstructions finishCarry
      (framed s (UInt256.ofNat (pc0 + 10))
        ([mm,t0,mu] ++ cacheStack bi pbi pa pb flag tn target2 tl inv m0 aEnd m96 m64 m32 dst ret rest)) =
    some (framed s (UInt256.ofNat (pc0 + 13))
      ([UInt256.addMod t0 mm maxWord,mu] ++ cacheStack bi pbi pa pb flag tn target2 tl inv m0 aEnd m96 m64 m32 dst ret rest)) := by
  have hc20 : rest.length + 20 < 1024 := by omega
  have hc21 : rest.length + 21 < 1024 := by omega
  simp [finishCarry,
    runInstructions, Challenge.EvmProof.Stepper.runInstr,
    framed, cacheStack, baseStack, Nat.add_assoc, hc20, hc21, allOnes_value,
    List.exchange, Challenge.EvmProof.Word.succ_ofNat_mod]

def cachedProduct : List Instr :=
  [.op (.Dup ⟨8, by decide⟩), .op (.Dup ⟨11, by decide⟩), .op .MLOAD,
   .op .MUL, .op (.Dup ⟨7, by decide⟩), .op (.Dup ⟨0, by decide⟩),
   .op (.Dup ⟨2, by decide⟩), .op (.Dup ⟨13, by decide⟩), .op .MULMOD,
   .op (.Dup ⟨13, by decide⟩), .op .MLOAD, .op .ADDMOD]

theorem run_cachedProduct (pc0 : Nat) (s : State) (bi pbi pa pb flag tn target2 inv m0 aEnd m96 m64 m32 dst ret : UInt256)
    (n : Nat) (rest : List UInt256) (hcap : rest.length ≤ 998) (hn : n ≤ 8)
    (hact : 88 ≤ s.activeWords.toNat) :
    let tl := UInt256.ofNat (2080+32*n)
    let t0 := MachineState.readWord s.memory (2080+32*n)
    runInstructions cachedProduct
      (framed s (UInt256.ofNat (pc0 + 0))
        (cacheStack bi pbi pa pb flag tn target2 tl inv m0 aEnd m96 m64 m32 dst ret rest)) =
    some (framed s (UInt256.ofNat (pc0 + 12))
      ([UInt256.addMod t0 (UInt256.mulMod m0 (inv*t0) maxWord) maxWord,inv*t0] ++
        cacheStack bi pbi pa pb flag tn target2 tl inv m0 aEnd m96 m64 m32 dst ret rest)) := by
  have hc17 : rest.length + 17 < 1024 := by omega
  have hc18 : rest.length + 18 < 1024 := by omega
  have hc19 : rest.length + 19 < 1024 := by omega
  have hc20 : rest.length + 20 < 1024 := by omega
  have hc21 : rest.length + 21 < 1024 := by omega
  have hc22 : rest.length + 22 < 1024 := by omega
  have hmod : (2080+32*n) % 115792089237316195423570985008687907853269984665640564039457584007913129639936 = 2080+32*n := Nat.mod_eq_of_lt (by omega)
  have hmul : MachineState.readWord s.memory (2080+32*n) * inv = inv * MachineState.readWord s.memory (2080+32*n) := by
    apply Challenge.EvmProof.Word.word_ext
    change ((MachineState.readWord s.memory (2080+32*n)).val * inv.val).val =
      (inv.val * (MachineState.readWord s.memory (2080+32*n)).val).val
    rw [Fin.val_mul, Fin.val_mul, Nat.mul_comm]
  have hactQ := activeWords_fix s (2080+32*n) 32 (by decide) (by omega) hact
  simp (config := { maxSteps := 400000 }) [cachedProduct, runInstructions,
    Challenge.EvmProof.Stepper.runInstr, framed, cacheStack, baseStack,
    Nat.add_assoc, hc17, hc18, hc19, hc20, hc21, hc22, hmul, allOnes_value,
    State.activeWordsAfterUInt256, Challenge.EvmProof.Word.word_toNat_ofNat,
    Challenge.EvmProof.Word.succ_ofNat_mod, hmod, hactQ, List.exchange]

/-- The four-limb multiply head copy (msplit/TL): `t0` is read at its code constant
(`PUSH2 2208 MLOAD`). P1a: the Montgomery inverse is the thirteenth cache word (`DUP13`). -/
def cachedProduct4 : List Instr :=
  [.op (.Dup ⟨12, by decide⟩), .push 2 2208, .op .MLOAD,
   .op .MUL, .op (.Dup ⟨7, by decide⟩), .op (.Dup ⟨0, by decide⟩),
   .op (.Dup ⟨2, by decide⟩), .op (.Dup ⟨13, by decide⟩), .op .MULMOD,
   .push 2 2208, .op .MLOAD, .op .ADDMOD]

theorem run_cachedProduct4 (pc0 : Nat) (s : State) (bi pbi pa pb flag tn target2 tl inv m0 aEnd m96 m64 m32 dst ret : UInt256)
    (rest : List UInt256) (hcap : rest.length ≤ 998)
    (hact : 88 ≤ s.activeWords.toNat) :
    let t0 := MachineState.readWord s.memory (2080+32*4)
    runInstructions cachedProduct4
      (framed s (UInt256.ofNat (pc0 + 0))
        (cacheStack bi pbi pa pb flag tn target2 tl m64 m0 aEnd m96 inv m32 dst ret rest)) =
    some (framed s (UInt256.ofNat (pc0 + 16))
      ([UInt256.addMod t0 (UInt256.mulMod m0 (inv*t0) maxWord) maxWord,inv*t0] ++
        cacheStack bi pbi pa pb flag tn target2 tl m64 m0 aEnd m96 inv m32 dst ret rest)) := by
  have hc17 : rest.length + 17 < 1024 := by omega
  have hc18 : rest.length + 18 < 1024 := by omega
  have hc19 : rest.length + 19 < 1024 := by omega
  have hc20 : rest.length + 20 < 1024 := by omega
  have hc21 : rest.length + 21 < 1024 := by omega
  have hc22 : rest.length + 22 < 1024 := by omega
  have hQ : (2080+32*4 : Nat) = 2208 := by decide
  have hmul : MachineState.readWord s.memory 2208 * inv = inv * MachineState.readWord s.memory 2208 := by
    apply Challenge.EvmProof.Word.word_ext
    change ((MachineState.readWord s.memory 2208).val * inv.val).val =
      (inv.val * (MachineState.readWord s.memory 2208).val).val
    rw [Fin.val_mul, Fin.val_mul, Nat.mul_comm]
  have hactQ := activeWords_fix s 2208 32 (by decide) (by omega) hact
  have h2208 : (2208 : UInt256).toNat = 2208 := by decide
  have h2208' : (UInt256.ofNat 2208).toNat = 2208 := by decide
  rw [hQ]
  simp (config := { maxSteps := 400000 }) [cachedProduct4, runInstructions,
    Challenge.EvmProof.Stepper.runInstr, framed, cacheStack, baseStack,
    Nat.add_assoc, hc17, hc18, hc19, hc20, hc21, hc22, hmul, allOnes_value,
    State.activeWordsAfterUInt256, Challenge.EvmProof.Word.word_toNat_ofNat,
    Challenge.EvmProof.Word.succ_ofNat_mod, Challenge.EvmProof.Word.ofNat_add_mod,
    h2208, h2208', hactQ, List.exchange]

theorem run_cachedProduct4_model (pc0 : Nat) (s : State)
    (bi pbi pa pb flag tn target2 tl inv m0 aEnd m96 m64 m32 dst ret : UInt256)
    (n : Nat) (rest : List UInt256) (hcap : rest.length ≤ 998) (hn : n = 4)
    (hact : 88 ≤ s.activeWords.toNat)
    (hc : ReadonlyCache s.memory n tl inv m0)
    (hm0 : m0 = MachineState.readWord s.memory (32*n-32))
    (hminv : CiosCachedMidMemory.inverseInvariant s.memory n) :
    runInstructions cachedProduct4
      (framed s (UInt256.ofNat (pc0 + 0))
        (cacheStack bi pbi pa pb flag tn target2 tl m64 m0 aEnd m96 inv m32 dst ret rest)) =
    some (framed s (UInt256.ofNat (pc0 + 16))
      ([rowC0 s.memory n,rowMu s.memory n] ++
        cacheStack bi pbi pa pb flag tn target2 tl m64 m0 aEnd m96 inv m32 dst ret rest)) := by
  subst hn
  rw [hc.inverse, hm0]
  have hr := run_cachedProduct4 pc0 s bi pbi pa pb flag tn target2 tl
    (MachineState.readWord s.memory 2720) (MachineState.readWord s.memory (32*4-32))
    aEnd m96 m64 m32 dst ret rest hcap hact
  have hguard : MachineState.readWord s.memory 2720 ≠ UInt256.ofNat 1 := by
    rw [← hc.inverse]
    exact hc.inverseGuard
  have hcarry := N0Carry.addMod_row_carry (MachineState.readWord s.memory (32*4-32))
    (MachineState.readWord s.memory 2720) (MachineState.readWord s.memory (2080+32*4)) hminv hguard
  dsimp only at hr
  rw [N0Carry.addMod_comm] at hr
  simpa only [hcarry, rowC0, rowMu] using hr

/-- TL eight-limb head: `t0` is read at its code constant (`PUSH2 2336 MLOAD`) and the low
modulus word `n0` rides in the frame's `tl` slot (`DUP15`).
P1a: the Montgomery inverse is the thirteenth cache word (`DUP13`). -/
def cachedProduct8 : List Instr :=
  [.op (.Dup ⟨12, by decide⟩), .push 2 2336, .op .MLOAD,
   .op .MUL, .op (.Dup ⟨7, by decide⟩), .op (.Dup ⟨0, by decide⟩),
   .op (.Dup ⟨2, by decide⟩), .op (.Dup ⟨14, by decide⟩), .op .MULMOD,
   .push 2 2336, .op .MLOAD, .op .ADDMOD]

theorem run_cachedProduct8 (pc0 : Nat) (s : State) (bi pbi pa pb flag tn target2 tl inv m0 aEnd m96 m64 m32 dst ret : UInt256)
    (rest : List UInt256) (hcap : rest.length ≤ 998)
    (hact : 88 ≤ s.activeWords.toNat) :
    let t0 := MachineState.readWord s.memory (2080+32*8)
    runInstructions cachedProduct8
      (framed s (UInt256.ofNat (pc0 + 0))
        (cacheStack bi pbi pa pb flag tn target2 tl m64 m0 aEnd m96 inv m32 dst ret rest)) =
    some (framed s (UInt256.ofNat (pc0 + 16))
      ([UInt256.addMod t0 (UInt256.mulMod tl (inv*t0) maxWord) maxWord,inv*t0] ++
        cacheStack bi pbi pa pb flag tn target2 tl m64 m0 aEnd m96 inv m32 dst ret rest)) := by
  have hc17 : rest.length + 17 < 1024 := by omega
  have hc18 : rest.length + 18 < 1024 := by omega
  have hc19 : rest.length + 19 < 1024 := by omega
  have hc20 : rest.length + 20 < 1024 := by omega
  have hc21 : rest.length + 21 < 1024 := by omega
  have hc22 : rest.length + 22 < 1024 := by omega
  have hmul : MachineState.readWord s.memory (2080+32*8) * inv = inv * MachineState.readWord s.memory (2080+32*8) := by
    apply Challenge.EvmProof.Word.word_ext
    change ((MachineState.readWord s.memory (2080+32*8)).val * inv.val).val =
      (inv.val * (MachineState.readWord s.memory (2080+32*8)).val).val
    rw [Fin.val_mul, Fin.val_mul, Nat.mul_comm]
  have hactQ := activeWords_fix s (2080+32*8) 32 (by decide) (by omega) hact
  have h2336 : (2336 : UInt256).toNat = 2336 := by decide
  have h2336' : (UInt256.ofNat 2336).toNat = 2336 := by decide
  have hQ : (2080+32*8 : Nat) = 2336 := by decide
  rw [hQ] at hmul hactQ ⊢
  simp (config := { maxSteps := 400000 }) [cachedProduct8, runInstructions,
    Challenge.EvmProof.Stepper.runInstr, framed, cacheStack, baseStack,
    Nat.add_assoc, hc17, hc18, hc19, hc20, hc21, hc22, hmul, allOnes_value,
    State.activeWordsAfterUInt256, Challenge.EvmProof.Word.word_toNat_ofNat,
    Challenge.EvmProof.Word.succ_ofNat_mod, Challenge.EvmProof.Word.ofNat_add_mod,
    h2336, h2336', hactQ, List.exchange]

theorem run_cachedProduct8_model (pc0 : Nat) (s : State)
    (bi pbi pa pb flag tn target2 tl inv m0 aEnd m96 m64 m32 dst ret : UInt256)
    (rest : List UInt256) (hcap : rest.length ≤ 998)
    (hact : 88 ≤ s.activeWords.toNat)
    (hc : ReadonlyCache s.memory 8 tl inv m0)
    (hminv : CiosCachedMidMemory.inverseInvariant s.memory 8) :
    runInstructions cachedProduct8
      (framed s (UInt256.ofNat (pc0 + 0))
        (cacheStack bi pbi pa pb flag tn target2 tl m64 m0 aEnd m96 inv m32 dst ret rest)) =
    some (framed s (UInt256.ofNat (pc0 + 16))
      ([rowC0 s.memory 8,rowMu s.memory 8] ++
        cacheStack bi pbi pa pb flag tn target2 tl m64 m0 aEnd m96 inv m32 dst ret rest)) := by
  rw [hc.lowAddress, hc.inverse]
  have hr := run_cachedProduct8 pc0 s bi pbi pa pb flag tn target2
    (MachineState.readWord s.memory 224) (MachineState.readWord s.memory 2720) m0
    aEnd m96 m64 m32 dst ret rest hcap hact
  have hguard : MachineState.readWord s.memory 2720 ≠ UInt256.ofNat 1 := by
    rw [← hc.inverse]
    exact hc.inverseGuard
  have hcarry := N0Carry.addMod_row_carry (MachineState.readWord s.memory 224)
    (MachineState.readWord s.memory 2720) (MachineState.readWord s.memory (2080+32*8)) hminv hguard
  dsimp only at hr
  rw [N0Carry.addMod_comm] at hr
  simpa only [hcarry, rowC0, rowMu, Nat.reduceMul, Nat.reduceSub, Nat.reduceAdd] using hr





#print axioms run_cachedProduct8_model
#print axioms run_cachedProduct4_model
end Challenge.Modexp.Submission.Proofs.Fast.TnCacheProductTrace
