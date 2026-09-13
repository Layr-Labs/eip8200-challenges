import Challenge.Modexp.Submission.Proofs.Bytecode.BigCMul
set_option warningAsError true
set_option maxRecDepth 20000
set_option maxHeartbeats 4000000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
/-!
# Compact multi-limb fallback: operand loading

The entry block zero-fills the arena, records the modulus length, and copies
the three operands out of calldata.
-/

namespace Challenge.Modexp.Submission.Proofs.Bytecode.BigC

open EvmSemantics
open EvmSemantics.EVM
open YulEvmCompiler
open Challenge.Modexp.Submission.Proofs.Bytecode

/-- Memory after the entry block. -/
def setupMem (mem cd : ByteArray) (bl el ml : Nat) : ByteArray :=
  let m1 := MachineState.writeBytes mem (MachineState.readPadded cd cd.size 9248) 0
  let m2 := MachineState.writeBytes m1 (Data.Bytes.natToBytesPadded ml 32) 9216
  let m3 := MachineState.writeBytes m2 (MachineState.readPadded cd (96 + (el + bl)) ml) 1024
  let m4 := MachineState.writeBytes m3 (MachineState.readPadded cd 96 bl) 5120
  MachineState.writeBytes m4 (MachineState.readPadded cd (96 + bl) el) 6144

theorem aw_first (aw : UInt256) (haw : aw.toNat ≤ 289) :
    MachineState.activeWordsAfter aw.toNat 0 9248 = 289 := by
  unfold MachineState.activeWordsAfter
  split
  · omega
  · dsimp only
    rw [show Nat.max aw.toNat ((0 + 9248 - 1) / 32 + 1) =
      max aw.toNat ((0 + 9248 - 1) / 32 + 1) from rfl]
    omega

theorem run_setup (s : State) (bl el ml : Nat) (stk : List UInt256) (mem : ByteArray)
    (aw : UInt256) (hcap : stk.length < 1000) (hbl : bl ≤ 1024) (hel : el ≤ 1024)
    (hml : ml ≤ 1024) (haw : aw.toNat ≤ 289)
    (hcds : s.executionEnv.calldata.size < 2 ^ 64)
    (hb : MachineState.readWord s.executionEnv.calldata 0 = UInt256.ofNat bl)
    (he : MachineState.readWord s.executionEnv.calldata 32 = UInt256.ofNat el)
    (hm : MachineState.readWord s.executionEnv.calldata 64 = UInt256.ofNat ml)
    (hcode : s.executionEnv.code = submissionBytecode)
    (hrun : s.halt = .Running) :
    Challenge.EvmProof.Stepper.runLocatedBlock setupPath (st s 258 stk mem aw) =
      some (st s 307 (UInt256.ofNat ml :: UInt256.ofNat 0 :: UInt256.ofNat bl ::
        UInt256.ofNat el :: UInt256.ofNat ml :: stk)
        (setupMem mem s.executionEnv.calldata bl el ml) AW) := by
  have hc := caps _ (by omega : stk.length < 1000)
  have hc0 : stk.length < 1024 := by omega
  have h0 := aw_first aw haw
  have h1 : ml < LIM := by simp only [LIM]; omega
  have h2 : bl < LIM := by simp only [LIM]; omega
  have h3 : el < LIM := by simp only [LIM]; omega
  have h4 : s.executionEnv.calldata.size < LIM := by simp only [LIM]; omega
  have h5 : 96 + (el + bl) < LIM := by simp only [LIM]; omega
  have h6 : 96 + bl < LIM := by simp only [LIM]; omega
  have hadd1 : UInt256.ofNat el + UInt256.ofNat bl = UInt256.ofNat (el + bl) :=
    Challenge.EvmProof.Word.ofNat_add_ofNat (by omega)
  have hadd2 : UInt256.ofNat 96 + UInt256.ofNat (el + bl) = UInt256.ofNat (96 + (el + bl)) :=
    Challenge.EvmProof.Word.ofNat_add_ofNat (by omega)
  have hadd3 : UInt256.ofNat 96 + UInt256.ofNat bl = UInt256.ofNat (96 + bl) :=
    Challenge.EvmProof.Word.ofNat_add_ofNat (by omega)
  have haw1 : MachineState.activeWordsAfter 289 9216 32 = 289 := aw_keep _ _ (by omega)
  have haw2 : MachineState.activeWordsAfter 289 1024 ml = 289 := aw_keep _ _ (by omega)
  have haw3 : MachineState.activeWordsAfter 289 5120 bl = 289 := aw_keep _ _ (by omega)
  have haw4 : MachineState.activeWordsAfter 289 6144 el = 289 := aw_keep _ _ (by omega)
  bigc_run [setupPath, setupMem, hc0, hc, hcode, hrun, zero_lit, h0, h1, h2, h3, h4, h5, h6,
    hb, he, hm, hadd1, hadd2, hadd3, haw1, haw2, haw3, haw4]

end Challenge.Modexp.Submission.Proofs.Bytecode.BigC
