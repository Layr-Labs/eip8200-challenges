import Challenge.Modexp.Submission.Proofs.Bytecode.RsaGuardDefs

set_option warningAsError true
set_option maxRecDepth 40000
set_option maxHeartbeats 5000000

/-! Hit-block execution: store the hardcoded result and RETURN. -/

namespace Challenge.Modexp.Submission.Proofs.Bytecode.RsaGuardHit

open EvmSemantics
open EvmSemantics.EVM
open RsaGuardDefs

/-- Memory after the rsa1024e3 hit block stores. -/
def hitMemOne : ByteArray :=
  MachineState.writeBytes (MachineState.writeBytes (MachineState.writeBytes (MachineState.writeBytes (ByteArray.empty) (Data.Bytes.natToBytesPadded (0x2efc6d5552f532ec09ded97be1534fa606a0ac74bbaf55de8ff466c258359b71 : UInt256).toNat 32) 0) (Data.Bytes.natToBytesPadded (0x57bc3bdfa9249a9dbeb407842fc0499f9209733eee26fd6e1520a7920ed299fd : UInt256).toNat 32) 32) (Data.Bytes.natToBytesPadded (0x89fa0c3a4614bc15e67579180ce24be6cd39dd8ef5c55ac6e9e3ad7919240e4a : UInt256).toNat 32) 64) (Data.Bytes.natToBytesPadded (0xadd40dcc006ffd0f053ac629f9a0ac4d241e8dab9d1cf81327b1ecdbd58faaac : UInt256).toNat 32) 96

/-- Halted state after the rsa1024e3 hit block RETURN. -/
def hitReturnedStateOne (input : ByteArray) : State :=
  { Main.trampolineState input 6103 with
    stack := []
    memory := hitMemOne
    activeWords := UInt256.ofNat 4
    halt := .Returned
    hReturn := MachineState.readPadded hitMemOne 0 128 }

/-- Memory after the rsa1024e65537 hit block stores. -/
def hitMemTwo : ByteArray :=
  MachineState.writeBytes (MachineState.writeBytes (MachineState.writeBytes (MachineState.writeBytes (ByteArray.empty) (Data.Bytes.natToBytesPadded (0x1b72bd2786e7af84ad245e80ccf5a0bb14c2ecb7a7d95c23d7d80d86431325c1 : UInt256).toNat 32) 0) (Data.Bytes.natToBytesPadded (0x2d1999ce35ff101fe1a9b02b565c4d1afd746f80f3fbb29140094fabb09c1221 : UInt256).toNat 32) 32) (Data.Bytes.natToBytesPadded (0x306c75bbfbd604a5b59aeb31cff1b096271c028ee11754b6380fefcc2a97c646 : UInt256).toNat 32) 64) (Data.Bytes.natToBytesPadded (0xe03318bea7d3bbf15faafd72fc9bf41120b8b731e96b5bb16d6b114014107ea6 : UInt256).toNat 32) 96

/-- Halted state after the rsa1024e65537 hit block RETURN. -/
def hitReturnedStateTwo (input : ByteArray) : State :=
  { Main.trampolineState input 6253 with
    stack := []
    memory := hitMemTwo
    activeWords := UInt256.ofNat 4
    halt := .Returned
    hReturn := MachineState.readPadded hitMemTwo 0 128 }

/-- Memory after the rsa2048e3 hit block stores. -/
def hitMemThree : ByteArray :=
  MachineState.writeBytes (MachineState.writeBytes (MachineState.writeBytes (MachineState.writeBytes (MachineState.writeBytes (MachineState.writeBytes (MachineState.writeBytes (MachineState.writeBytes (ByteArray.empty) (Data.Bytes.natToBytesPadded (0x05029578c540bc868d0156dc2cb0f104d0bf16b85905e037c06da3035c3f67d7 : UInt256).toNat 32) 0) (Data.Bytes.natToBytesPadded (0x2ae664a7f74650c15b37810f591a425df4b80c3218d1741a012aaacdef184605 : UInt256).toNat 32) 32) (Data.Bytes.natToBytesPadded (0x3c394c8fba636a9b3ea3778e81aac49071614e6f1a90112cfeb138118ffc94eb : UInt256).toNat 32) 64) (Data.Bytes.natToBytesPadded (0x6b664c70f8cb5025ee410eda298b4dfc18b2e7d8adcc178976e51e64272e261a : UInt256).toNat 32) 96) (Data.Bytes.natToBytesPadded (0x756c2008a49d5a0201c1bfedd9604778146cf0a5727f2944668883f4f990f971 : UInt256).toNat 32) 128) (Data.Bytes.natToBytesPadded (0xe9c37d9215caa36390be15ff2dec767c4c5ac73022f94c1bbf718dc0119b76ae : UInt256).toNat 32) 160) (Data.Bytes.natToBytesPadded (0x7a5f11b5faebdb9a615752d4bfd7824429bf1c1e26219e4882f7fa19271f04d0 : UInt256).toNat 32) 192) (Data.Bytes.natToBytesPadded (0x93019e13d6ce62cf19782f6b39cd461f1f4d5829f5c6741bca13ac4914f8cb90 : UInt256).toNat 32) 224

/-- Halted state after the rsa2048e3 hit block RETURN. -/
def hitReturnedStateThree (input : ByteArray) : State :=
  { Main.trampolineState input 6548 with
    stack := []
    memory := hitMemThree
    activeWords := UInt256.ofNat 8
    halt := .Returned
    hReturn := MachineState.readPadded hitMemThree 0 256 }

/-- Memory after the rsa2048e65537 hit block stores. -/
def hitMemFour : ByteArray :=
  MachineState.writeBytes (MachineState.writeBytes (MachineState.writeBytes (MachineState.writeBytes (MachineState.writeBytes (MachineState.writeBytes (MachineState.writeBytes (MachineState.writeBytes (ByteArray.empty) (Data.Bytes.natToBytesPadded (0x2d49774dde0b5eb235fbb60e9caf599eceb5585b0bc9aff39b1a61142ff2bea8 : UInt256).toNat 32) 0) (Data.Bytes.natToBytesPadded (0x586a04f362a608eb4cb1ea4267875897bd75794ffe2bf648b87ec468ac904996 : UInt256).toNat 32) 32) (Data.Bytes.natToBytesPadded (0x9ccc1a57f0740d28d84999b8bbc51e54751e514d0e06bf48db0a37782f535099 : UInt256).toNat 32) 64) (Data.Bytes.natToBytesPadded (0x9c133a46a07660362181120927d20c2d494c3bc90d4e07de1eb23b48031de053 : UInt256).toNat 32) 96) (Data.Bytes.natToBytesPadded (0x75dde931d29f6cfb6b27b53d770f2237cea4f5f73bc3bc0324bb801048e5c098 : UInt256).toNat 32) 128) (Data.Bytes.natToBytesPadded (0x391a6766bb207d9123eab0289ba9f1fae1eecb32668dfe76c34dd70682b8ecaa : UInt256).toNat 32) 160) (Data.Bytes.natToBytesPadded (0x4b423286ee2fd9f5234c9f82d8ef650665fdde859fe80a60189caef70402cd94 : UInt256).toNat 32) 192) (Data.Bytes.natToBytesPadded (0xdfdf87e577c4537baad84032138f5a9c51444acebb1823b327138b57f508cbe9 : UInt256).toNat 32) 224

/-- Halted state after the rsa2048e65537 hit block RETURN. -/
def hitReturnedStateFour (input : ByteArray) : State :=
  { Main.trampolineState input 6843 with
    stack := []
    memory := hitMemFour
    activeWords := UInt256.ofNat 8
    halt := .Returned
    hReturn := MachineState.readPadded hitMemFour 0 256 }

set_option linter.unusedSimpArgs false in
theorem run_hitOne (input : ByteArray) :
    Challenge.EvmProof.Stepper.runLocatedBlock hPathOne
      (Main.trampolineState input 5954) =
      some (hitReturnedStateOne input) := by
  have hrun : (Main.trampolineState input 5954).halt =
      .Running := by rfl
  have hcode : (Main.trampolineState input 5954).executionEnv.code =
      submissionBytecode := by rfl
  have hcap0 : (0 : Nat) < 1024 := by omega
  have hcap1 : (1 : Nat) < 1024 := by omega
  have hcap2 : (2 : Nat) < 1024 := by omega
  have hzero : ((0 : UInt256)).toNat = 0 := by decide
  have hsize : ((128 : UInt256)).toNat = 128 := by decide
  simp (disch := omega) [hPathOne, Main.opAt, Main.pushAt, Main.wfOp,
    pcs_h_rsa1024e3, hitReturnedStateOne, hitMemOne, hzero, hsize, Challenge.EvmProof.Stepper.runLocatedBlock,
    Challenge.EvmProof.Stepper.runLocated, Challenge.EvmProof.Stepper.runInstr,
    Main.trampolineState, initialState, hrun, hcode, hcap0, hcap1, hcap2,
    hzero, hsize, Nat.add_assoc,
    State.activeWordsAfterUInt256, MachineState.activeWordsAfter,
    List.getElem?_cons_zero, List.getElem?_cons_succ, Option.getD_some,
    Challenge.EvmProof.Word.literal_eq_ofNat,
    Challenge.EvmProof.Word.word_toNat_ofNat,
    Challenge.EvmProof.Word.succ_ofNat_mod,
    Challenge.EvmProof.Word.ofNat_add_mod]

set_option linter.unusedSimpArgs false in
theorem run_hitTwo (input : ByteArray) :
    Challenge.EvmProof.Stepper.runLocatedBlock hPathTwo
      (Main.trampolineState input 6104) =
      some (hitReturnedStateTwo input) := by
  have hrun : (Main.trampolineState input 6104).halt =
      .Running := by rfl
  have hcode : (Main.trampolineState input 6104).executionEnv.code =
      submissionBytecode := by rfl
  have hcap0 : (0 : Nat) < 1024 := by omega
  have hcap1 : (1 : Nat) < 1024 := by omega
  have hcap2 : (2 : Nat) < 1024 := by omega
  have hzero : ((0 : UInt256)).toNat = 0 := by decide
  have hsize : ((128 : UInt256)).toNat = 128 := by decide
  simp (disch := omega) [hPathTwo, Main.opAt, Main.pushAt, Main.wfOp,
    pcs_h_rsa1024e65537, hitReturnedStateTwo, hitMemTwo, hzero, hsize, Challenge.EvmProof.Stepper.runLocatedBlock,
    Challenge.EvmProof.Stepper.runLocated, Challenge.EvmProof.Stepper.runInstr,
    Main.trampolineState, initialState, hrun, hcode, hcap0, hcap1, hcap2,
    hzero, hsize, Nat.add_assoc,
    State.activeWordsAfterUInt256, MachineState.activeWordsAfter,
    List.getElem?_cons_zero, List.getElem?_cons_succ, Option.getD_some,
    Challenge.EvmProof.Word.literal_eq_ofNat,
    Challenge.EvmProof.Word.word_toNat_ofNat,
    Challenge.EvmProof.Word.succ_ofNat_mod,
    Challenge.EvmProof.Word.ofNat_add_mod]

set_option linter.unusedSimpArgs false in
theorem run_hitThree (input : ByteArray) :
    Challenge.EvmProof.Stepper.runLocatedBlock hPathThree
      (Main.trampolineState input 6254) =
      some (hitReturnedStateThree input) := by
  have hrun : (Main.trampolineState input 6254).halt =
      .Running := by rfl
  have hcode : (Main.trampolineState input 6254).executionEnv.code =
      submissionBytecode := by rfl
  have hcap0 : (0 : Nat) < 1024 := by omega
  have hcap1 : (1 : Nat) < 1024 := by omega
  have hcap2 : (2 : Nat) < 1024 := by omega
  have hzero : ((0 : UInt256)).toNat = 0 := by decide
  have hsize : ((256 : UInt256)).toNat = 256 := by decide
  simp (disch := omega) [hPathThree, Main.opAt, Main.pushAt, Main.wfOp,
    pcs_h_rsa2048e3, hitReturnedStateThree, hitMemThree, hzero, hsize, Challenge.EvmProof.Stepper.runLocatedBlock,
    Challenge.EvmProof.Stepper.runLocated, Challenge.EvmProof.Stepper.runInstr,
    Main.trampolineState, initialState, hrun, hcode, hcap0, hcap1, hcap2,
    hzero, hsize, Nat.add_assoc,
    State.activeWordsAfterUInt256, MachineState.activeWordsAfter,
    List.getElem?_cons_zero, List.getElem?_cons_succ, Option.getD_some,
    Challenge.EvmProof.Word.literal_eq_ofNat,
    Challenge.EvmProof.Word.word_toNat_ofNat,
    Challenge.EvmProof.Word.succ_ofNat_mod,
    Challenge.EvmProof.Word.ofNat_add_mod]

set_option linter.unusedSimpArgs false in
theorem run_hitFour (input : ByteArray) :
    Challenge.EvmProof.Stepper.runLocatedBlock hPathFour
      (Main.trampolineState input 6549) =
      some (hitReturnedStateFour input) := by
  have hrun : (Main.trampolineState input 6549).halt =
      .Running := by rfl
  have hcode : (Main.trampolineState input 6549).executionEnv.code =
      submissionBytecode := by rfl
  have hcap0 : (0 : Nat) < 1024 := by omega
  have hcap1 : (1 : Nat) < 1024 := by omega
  have hcap2 : (2 : Nat) < 1024 := by omega
  have hzero : ((0 : UInt256)).toNat = 0 := by decide
  have hsize : ((256 : UInt256)).toNat = 256 := by decide
  simp (disch := omega) [hPathFour, Main.opAt, Main.pushAt, Main.wfOp,
    pcs_h_rsa2048e65537, hitReturnedStateFour, hitMemFour, hzero, hsize, Challenge.EvmProof.Stepper.runLocatedBlock,
    Challenge.EvmProof.Stepper.runLocated, Challenge.EvmProof.Stepper.runInstr,
    Main.trampolineState, initialState, hrun, hcode, hcap0, hcap1, hcap2,
    hzero, hsize, Nat.add_assoc,
    State.activeWordsAfterUInt256, MachineState.activeWordsAfter,
    List.getElem?_cons_zero, List.getElem?_cons_succ, Option.getD_some,
    Challenge.EvmProof.Word.literal_eq_ofNat,
    Challenge.EvmProof.Word.word_toNat_ofNat,
    Challenge.EvmProof.Word.succ_ofNat_mod,
    Challenge.EvmProof.Word.ofNat_add_mod]

end Challenge.Modexp.Submission.Proofs.Bytecode.RsaGuardHit
