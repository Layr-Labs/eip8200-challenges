import Challenge.Modexp.Submission.Proofs.Bytecode.BigExponentGas
import Challenge.Modexp.Submission.Proofs.Bytecode.BigExponentScan
import Challenge.Modexp.Submission.Proofs.Bytecode.WordCorrect
set_option warningAsError true
set_option maxRecDepth 20000
set_option maxHeartbeats 3000000
/-! # Gas-certified composition of the leading-zero scanner -/

namespace Challenge.Modexp.Submission.Proofs.Bytecode.BigExponentScanGas

open EvmSemantics
open EvmSemantics.EVM
open BigExponentScan

def coldScan (s : State) (expOff : Nat) : Nat → Nat → Nat
  | i, 0 => i
  | i, fuel + 1 =>
      if (loadedByte s expOff i).toNat = 0 then
        coldScan s expOff (i + 1) fuel
      else i

def coldByteIndex (s : State) (expOff e : Nat) : Nat :=
  coldScan s expOff 0 e

def coldBitScan (byte : UInt256) : Nat → Nat → Nat
  | j, 0 => j
  | j, fuel + 1 =>
      if (BigExponent.exponentBit byte j).toNat = 0 then
        coldBitScan byte (j + 1) fuel
      else j

def coldBitIndex (byte : UInt256) : Nat := coldBitScan byte 0 8

theorem coldScan_le (s : State) (expOff fuel : Nat) :
    ∀ i, coldScan s expOff i fuel ≤ i + fuel := by
  induction fuel with
  | zero => intro i; simp [coldScan]
  | succ fuel ih =>
      intro i
      by_cases hz : (loadedByte s expOff i).toNat = 0
      · rw [coldScan, if_pos hz]
        have := ih (i + 1)
        omega
      · rw [coldScan, if_neg hz]
        omega

theorem coldScan_zeros (s : State) (expOff fuel : Nat) :
    ∀ i t, i ≤ t → t < coldScan s expOff i fuel →
      (loadedByte s expOff t).toNat = 0 := by
  induction fuel with
  | zero => intro i t _ hhi; rw [coldScan] at hhi; omega
  | succ fuel ih =>
      intro i t hlo hhi
      by_cases hz : (loadedByte s expOff i).toNat = 0
      · rw [coldScan, if_pos hz] at hhi
        rcases Nat.lt_or_ge t (i + 1) with h | h
        · have ht : t = i := by omega
          subst ht
          exact hz
        · exact ih (i + 1) t h hhi
      · rw [coldScan, if_neg hz] at hhi; omega

theorem coldScan_hit (s : State) (expOff fuel : Nat) :
    ∀ i, coldScan s expOff i fuel < i + fuel →
      (loadedByte s expOff (coldScan s expOff i fuel)).toNat ≠ 0 := by
  induction fuel with
  | zero => intro i hlt; rw [coldScan] at hlt; omega
  | succ fuel ih =>
      intro i hlt
      by_cases hz : (loadedByte s expOff i).toNat = 0
      · rw [coldScan, if_pos hz] at hlt ⊢
        exact ih (i + 1) (by omega)
      · rw [coldScan, if_neg hz] at hlt ⊢
        exact hz

theorem coldByteIndex_le (s : State) (expOff e : Nat) :
    coldByteIndex s expOff e ≤ e := by
  simpa [coldByteIndex] using coldScan_le s expOff e 0

theorem coldByteIndex_zeros (s : State) (expOff e t : Nat)
    (ht : t < coldByteIndex s expOff e) :
    (loadedByte s expOff t).toNat = 0 :=
  coldScan_zeros s expOff e 0 t (Nat.zero_le t) ht

theorem coldByteIndex_hit (s : State) (expOff e : Nat)
    (hlt : coldByteIndex s expOff e < e) :
    (loadedByte s expOff (coldByteIndex s expOff e)).toNat ≠ 0 :=
  coldScan_hit s expOff e 0 (by simpa [coldByteIndex] using hlt)

theorem coldBitScan_le (byte : UInt256) (fuel : Nat) :
    ∀ j, coldBitScan byte j fuel ≤ j + fuel := by
  induction fuel with
  | zero => intro j; simp [coldBitScan]
  | succ fuel ih =>
      intro j
      by_cases hz : (BigExponent.exponentBit byte j).toNat = 0
      · rw [coldBitScan, if_pos hz]
        have := ih (j + 1)
        omega
      · rw [coldBitScan, if_neg hz]
        omega

theorem coldBitScan_zeros (byte : UInt256) (fuel : Nat) :
    ∀ j t, j ≤ t → t < coldBitScan byte j fuel →
      (BigExponent.exponentBit byte t).toNat = 0 := by
  induction fuel with
  | zero => intro j t _ hhi; rw [coldBitScan] at hhi; omega
  | succ fuel ih =>
      intro j t hlo hhi
      by_cases hz : (BigExponent.exponentBit byte j).toNat = 0
      · rw [coldBitScan, if_pos hz] at hhi
        rcases Nat.lt_or_ge t (j + 1) with h | h
        · have ht : t = j := by omega
          subst ht
          exact hz
        · exact ih (j + 1) t h hhi
      · rw [coldBitScan, if_neg hz] at hhi; omega

theorem coldBitScan_hit (byte : UInt256) (fuel : Nat) :
    ∀ j, coldBitScan byte j fuel < j + fuel →
      (BigExponent.exponentBit byte (coldBitScan byte j fuel)).toNat ≠ 0 := by
  induction fuel with
  | zero => intro j hlt; rw [coldBitScan] at hlt; omega
  | succ fuel ih =>
      intro j hlt
      by_cases hz : (BigExponent.exponentBit byte j).toNat = 0
      · rw [coldBitScan, if_pos hz] at hlt ⊢
        exact ih (j + 1) (by omega)
      · rw [coldBitScan, if_neg hz] at hlt ⊢
        exact hz

theorem coldBitIndex_le (byte : UInt256) : coldBitIndex byte ≤ 8 := by
  simpa [coldBitIndex] using coldBitScan_le byte 8 0

theorem coldBitIndex_zeros (byte : UInt256) (t : Nat)
    (ht : t < coldBitIndex byte) :
    (BigExponent.exponentBit byte t).toNat = 0 :=
  coldBitScan_zeros byte 8 0 t (Nat.zero_le t) ht

theorem exponentBit_toNat_eq_bitNat (byte : UInt256) (j : Nat) (hj : j < 8) :
    (BigExponent.exponentBit byte j).toNat =
      WordCorrect.exponentBitNat byte j := by
  have h := congrArg UInt256.toNat (WordCorrect.exponentBit_eq byte j hj)
  have hbit := WordCorrect.exponentBitNat_zero_or_one byte j
  rw [Challenge.EvmProof.Word.word_toNat_ofNat,
    Nat.mod_eq_of_lt (by omega : WordCorrect.exponentBitNat byte j < 2 ^ 256)]
    at h
  exact h

theorem bitPrefix_eq_zero (byte : UInt256) (n : Nat)
    (hz : ∀ j, j < n → WordCorrect.exponentBitNat byte j = 0) :
    WordCorrect.bitPrefix byte n = 0 := by
  induction n with
  | zero => rfl
  | succ n ih =>
      rw [WordCorrect.bitPrefix, ih (fun j hj => hz j (by omega)),
        hz n (by omega)]

theorem loadedByte_lt256 (s : State) (expOff i : Nat) :
    (loadedByte s expOff i).toNat < 256 := by
  unfold loadedByte BigExponent.loadedExponentByte UInt256.byteAt
  rw [show (0 : UInt256).toNat = 0 by decide]
  rw [if_neg (by omega)]
  rw [Challenge.EvmProof.Word.word_toNat_ofNat]
  have hand :
      ((MachineState.readWord s.executionEnv.calldata (expOff + i)).toNat >>>
        (8 * (31 - 0))) &&& 255 ≤ 255 := Nat.and_le_right
  have hlt :
      ((MachineState.readWord s.executionEnv.calldata (expOff + i)).toNat >>>
        (8 * (31 - 0))) &&& 255 < 2 ^ 256 := by omega
  rw [Nat.mod_eq_of_lt hlt]
  omega

theorem coldBitIndex_lt (byte : UInt256) (hbyte : byte.toNat < 256)
    (hnz : byte.toNat ≠ 0) : coldBitIndex byte < 8 := by
  rcases Nat.lt_or_ge (coldBitIndex byte) 8 with h | h
  · exact h
  · exfalso
    have h8 : coldBitIndex byte = 8 :=
      Nat.le_antisymm (coldBitIndex_le byte) h
    have hz : ∀ j, j < 8 → WordCorrect.exponentBitNat byte j = 0 := by
      intro j hj
      rw [← exponentBit_toNat_eq_bitNat byte j hj]
      exact coldBitIndex_zeros byte j (by omega)
    have hpre := bitPrefix_eq_zero byte 8 hz
    rw [WordCorrect.bitPrefix_eight byte hbyte] at hpre
    exact hnz hpre

theorem coldBitIndex_hit (byte : UInt256) (h : coldBitIndex byte < 8) :
    (BigExponent.exponentBit byte (coldBitIndex byte)).toNat ≠ 0 :=
  coldBitScan_hit byte 8 0 (by exact h)

private def soundBlock {s t : State}
    (path : List (Challenge.EvmProof.Stepper.Located
      Artifact.submissionArtifact .Osaka))
    (hcode : s.executionEnv.code = submissionBytecode)
    (hfork : s.fork = .Osaka) (hrun : s.halt = .Running)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig
      s.executionEnv.fork s.executionEnv.codeAddr = false)
    (hr : Challenge.EvmProof.Stepper.runLocatedBlock path s = some t) :
    Challenge.EvmProof.GasSteps s t :=
  Challenge.EvmProof.Stepper.runLocatedBlock_sound
    Artifact.submissionArtifact .Osaka path
      (by simpa [Artifact.submissionArtifact] using hcode)
      (by simpa [State.fork] using hfork) hr hrun hnp

def gasSteps_zeroBytes (s : State) (accumulatorWord : UInt256)
    (count b e m baseOff expOff target : Nat) (rest : List UInt256)
    (hcap : rest.length < 968) (htarget : target ≤ e)
    (hexpFit : expOff + e < 2 ^ 256)
    (hzero : ∀ k, k < target → (loadedByte s expOff k).toNat = 0)
    (hcode : s.executionEnv.code = submissionBytecode)
    (hfork : s.fork = .Osaka) (hrun : s.halt = .Running)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig
      s.executionEnv.fork s.executionEnv.codeAddr = false) :
    Challenge.EvmProof.GasSteps
      (byteLoop s accumulatorWord count b e m baseOff expOff rest 0)
      (byteLoop s accumulatorWord count b e m baseOff expOff rest target) := by
  induction target with
  | zero => exact Challenge.EvmProof.GasSteps.refl _
  | succ i ih =>
      have hi : i < e := by omega
      have hoff : expOff + i < 2 ^ 256 := by omega
      have hi256 : i + 1 < 2 ^ 256 := by omega
      have hprefix := ih (by omega) (fun k hk => hzero k (by omega))
      have hguard := soundBlock
        (s := byteLoop s accumulatorWord count b e m baseOff expOff rest i)
        byteGuardPath (by simpa [byteLoop] using hcode)
        (by simpa [byteLoop, State.fork] using hfork)
        (by simpa [byteLoop] using hrun)
        (by simpa [byteLoop, State.fork] using hnp)
        (run_byteGuardContinue s accumulatorWord count b e m baseOff expOff i
          rest (by omega) (by omega) hi hrun)
      have hload := soundBlock
        (s := byteBody s accumulatorWord count b e m baseOff expOff rest i)
        loadBytePath
        (by simpa [byteBody, byteLoop] using hcode)
        (by simpa [byteBody, byteLoop, State.fork] using hfork)
        (by simpa [byteBody, byteLoop] using hrun)
        (by simpa [byteBody, byteLoop, State.fork] using hnp)
        (run_loadByteZero s accumulatorWord count b e m baseOff expOff i rest
          (by omega) hoff hcode hrun (hzero i (by omega)))
      have hnext := soundBlock
        (s := zeroByteEntry s accumulatorWord count b e m baseOff expOff i rest)
        zeroBytePath
        (by simpa [zeroByteEntry, bitStartEntry] using hcode)
        (by simpa [zeroByteEntry, bitStartEntry, State.fork] using hfork)
        (by simpa [zeroByteEntry, bitStartEntry] using hrun)
        (by simpa [zeroByteEntry, bitStartEntry, State.fork] using hnp)
        (run_zeroByte s accumulatorWord count b e m baseOff expOff i rest
          (by omega) hi256 hcode hrun)
      exact hprefix.trans (hguard.trans (hload.trans hnext))

def gasSteps_zeroBits (s : State) (accumulatorWord : UInt256)
    (count b e m baseOff expOff i target : Nat) (rest : List UInt256)
    (hcap : rest.length < 968) (htarget : target ≤ 8)
    (hzero : ∀ k, k < target →
      (BigExponent.exponentBit (loadedByte s expOff i) k).toNat = 0)
    (hcode : s.executionEnv.code = submissionBytecode)
    (hfork : s.fork = .Osaka) (hrun : s.halt = .Running)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig
      s.executionEnv.fork s.executionEnv.codeAddr = false) :
    Challenge.EvmProof.GasSteps
      (bitLoop s accumulatorWord count b e m baseOff expOff i 0 rest)
      (bitLoop s accumulatorWord count b e m baseOff expOff i target rest) := by
  induction target with
  | zero => exact Challenge.EvmProof.GasSteps.refl _
  | succ j ih =>
      have hj : j < 8 := by omega
      have hprefix := ih (by omega) (fun k hk => hzero k (by omega))
      have htest := soundBlock
        (s := bitLoop s accumulatorWord count b e m baseOff expOff i j rest)
        bitTestPath
        (by simpa [BigExponentScan.bitLoop] using hcode)
        (by simpa [BigExponentScan.bitLoop, State.fork] using hfork)
        (by simpa [BigExponentScan.bitLoop] using hrun)
        (by simpa [BigExponentScan.bitLoop, State.fork] using hnp)
        (run_bitTestZero s accumulatorWord count b e m baseOff expOff i j rest
          (by omega) hj hrun (hzero j (by omega)))
      have hadvance := soundBlock
        (s := bitAdvanceEntry s accumulatorWord count b e m baseOff expOff i j
          rest) bitAdvancePath
        (by simpa [bitAdvanceEntry, BigExponentScan.bitLoop] using hcode)
        (by simpa [bitAdvanceEntry, BigExponentScan.bitLoop, State.fork] using hfork)
        (by simpa [bitAdvanceEntry, BigExponentScan.bitLoop] using hrun)
        (by simpa [bitAdvanceEntry, BigExponentScan.bitLoop, State.fork] using hnp)
        (run_bitAdvance s accumulatorWord count b e m baseOff expOff i j rest
          (by omega) (by omega) hcode hrun)
      exact hprefix.trans (htest.trans hadvance)

def gasSteps_scanFound (s : State) (accumulatorWord : UInt256)
    (count b e m baseOff expOff i j : Nat) (rest : List UInt256)
    (hcap : rest.length < 968) (hi : i < e) (hj : j < 8)
    (hexpFit : expOff + e < 2 ^ 256)
    (hzeroBytes : ∀ k, k < i → (loadedByte s expOff k).toNat = 0)
    (hbyte : (loadedByte s expOff i).toNat ≠ 0)
    (hzeroBits : ∀ k, k < j →
      (BigExponent.exponentBit (loadedByte s expOff i) k).toNat = 0)
    (hbit : (BigExponent.exponentBit (loadedByte s expOff i) j).toNat ≠ 0)
    (hcode : s.executionEnv.code = submissionBytecode)
    (hfork : s.fork = .Osaka) (hrun : s.halt = .Running)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig
      s.executionEnv.fork s.executionEnv.codeAddr = false) :
    Challenge.EvmProof.GasSteps
      (scanEntry s accumulatorWord count b e m baseOff expOff rest)
      (BigExponent.innerLoop s accumulatorWord count b e m baseOff expOff i
        (loadedOffset expOff i) (loadedByte s expOff i) rest j) := by
  have hstart := soundBlock
    (s := scanEntry s accumulatorWord count b e m baseOff expOff rest)
    startPath (by simpa [scanEntry] using hcode)
    (by simpa [scanEntry, State.fork] using hfork)
    (by simpa [scanEntry] using hrun)
    (by simpa [scanEntry, State.fork] using hnp)
    (run_start s accumulatorWord count b e m baseOff expOff rest
      (by omega) hrun)
  have hbytes := gasSteps_zeroBytes s accumulatorWord count b e m baseOff
    expOff i rest hcap (by omega) hexpFit hzeroBytes hcode hfork hrun hnp
  have hguard := soundBlock
    (s := byteLoop s accumulatorWord count b e m baseOff expOff rest i)
    byteGuardPath
    (by simpa [byteLoop] using hcode)
    (by simpa [byteLoop, State.fork] using hfork)
    (by simpa [byteLoop] using hrun)
    (by simpa [byteLoop, State.fork] using hnp)
    (run_byteGuardContinue s accumulatorWord count b e m baseOff expOff i
      rest (by omega) (by omega) hi hrun)
  have hload := soundBlock
    (s := byteBody s accumulatorWord count b e m baseOff expOff rest i)
    loadBytePath
    (by simpa [byteBody, byteLoop] using hcode)
    (by simpa [byteBody, byteLoop, State.fork] using hfork)
    (by simpa [byteBody, byteLoop] using hrun)
    (by simpa [byteBody, byteLoop, State.fork] using hnp)
    (run_loadByteNonzero s accumulatorWord count b e m baseOff expOff i rest
      (by omega) (by omega) hrun hbyte)
  have hbitsStart := soundBlock
    (s := bitStartEntry s accumulatorWord count b e m baseOff expOff i rest)
    startBitsPath
    (by simpa [bitStartEntry] using hcode)
    (by simpa [bitStartEntry, State.fork] using hfork)
    (by simpa [bitStartEntry] using hrun)
    (by simpa [bitStartEntry, State.fork] using hnp)
    (run_startBits s accumulatorWord count b e m baseOff expOff i rest
      (by omega) hrun)
  have hbits := gasSteps_zeroBits s accumulatorWord count b e m baseOff expOff
    i j rest hcap (by omega) hzeroBits hcode hfork hrun hnp
  have htest := soundBlock
    (s := bitLoop s accumulatorWord count b e m baseOff expOff i j rest)
    bitTestPath
    (by simpa [BigExponentScan.bitLoop] using hcode)
    (by simpa [BigExponentScan.bitLoop, State.fork] using hfork)
    (by simpa [BigExponentScan.bitLoop] using hrun)
    (by simpa [BigExponentScan.bitLoop, State.fork] using hnp)
    (run_bitTestSet s accumulatorWord count b e m baseOff expOff i j rest
      (by omega) hj hcode hrun hbit)
  have hfound := soundBlock
    (s := bitFoundEntry s accumulatorWord count b e m baseOff expOff i j rest)
    bitFoundPath
    (by simpa [bitFoundEntry, BigExponentScan.bitLoop] using hcode)
    (by simpa [bitFoundEntry, BigExponentScan.bitLoop, State.fork] using hfork)
    (by simpa [bitFoundEntry, BigExponentScan.bitLoop] using hrun)
    (by simpa [bitFoundEntry, BigExponentScan.bitLoop, State.fork] using hnp)
    (run_bitFound s accumulatorWord count b e m baseOff expOff i j rest
      (by omega) hcode hrun)
  exact hstart.trans <| hbytes.trans <| hguard.trans <| hload.trans <|
    hbitsStart.trans <| hbits.trans <| htest.trans hfound

def gasSteps_scanAllZero (s : State) (accumulatorWord : UInt256)
    (count b e m baseOff expOff : Nat) (rest : List UInt256)
    (hcap : rest.length < 968) (he : e < 2 ^ 256)
    (hexpFit : expOff + e < 2 ^ 256)
    (hzero : ∀ k, k < e → (loadedByte s expOff k).toNat = 0)
    (hcode : s.executionEnv.code = submissionBytecode)
    (hfork : s.fork = .Osaka) (hrun : s.halt = .Running)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig
      s.executionEnv.fork s.executionEnv.codeAddr = false) :
    Challenge.EvmProof.GasSteps
      (scanEntry s accumulatorWord count b e m baseOff expOff rest)
      (BigExponent.outerLoop s accumulatorWord count b e m baseOff expOff rest
        e) := by
  have hstart := soundBlock
    (s := scanEntry s accumulatorWord count b e m baseOff expOff rest)
    startPath (by simpa [scanEntry] using hcode)
    (by simpa [scanEntry, State.fork] using hfork)
    (by simpa [scanEntry] using hrun)
    (by simpa [scanEntry, State.fork] using hnp)
    (run_start s accumulatorWord count b e m baseOff expOff rest
      (by omega) hrun)
  have hbytes := gasSteps_zeroBytes s accumulatorWord count b e m baseOff
    expOff e rest hcap (by omega) hexpFit hzero hcode hfork hrun hnp
  have hfinish := soundBlock
    (s := byteLoop s accumulatorWord count b e m baseOff expOff rest e)
    byteGuardPath
    (by simpa [byteLoop] using hcode)
    (by simpa [byteLoop, State.fork] using hfork)
    (by simpa [byteLoop] using hrun)
    (by simpa [byteLoop, State.fork] using hnp)
    (run_byteGuardFinish s accumulatorWord count b e m baseOff expOff rest
      (by omega) he hcode hrun)
  exact hstart.trans (hbytes.trans hfinish)

def exponentBitProgressFrom (s : State) (accumulatorWord : UInt256)
    (count b e m baseOff expOff i start : Nat) (offset byte : UInt256)
    (rest : List UInt256) : Nat → State
  | 0 => s
  | k + 1 =>
      BigExponent.selectProgress
        (exponentBitProgressFrom s accumulatorWord count b e m baseOff expOff
          i start offset byte rest k)
        accumulatorWord count b e m baseOff expOff i (start + k) offset byte
        rest count

@[simp] theorem exponentBitProgressFrom_executionEnv (s : State)
    (accumulatorWord : UInt256) (count b e m baseOff expOff i start k : Nat)
    (offset byte : UInt256) (rest : List UInt256) :
    (exponentBitProgressFrom s accumulatorWord count b e m baseOff expOff i
      start offset byte rest k).executionEnv = s.executionEnv := by
  induction k with
  | zero => rfl
  | succ k ih => simp [exponentBitProgressFrom, ih]

@[simp] theorem exponentBitProgressFrom_halt (s : State)
    (accumulatorWord : UInt256) (count b e m baseOff expOff i start k : Nat)
    (offset byte : UInt256) (rest : List UInt256) :
    (exponentBitProgressFrom s accumulatorWord count b e m baseOff expOff i
      start offset byte rest k).halt = s.halt := by
  induction k with
  | zero => rfl
  | succ k ih => simp [exponentBitProgressFrom, ih]

def bitLoopFromState (s : State) (accumulatorWord : UInt256)
    (count b e m baseOff expOff i start : Nat) (offset byte : UInt256)
    (rest : List UInt256) (k : Nat) : State :=
  BigExponent.innerLoop
    (exponentBitProgressFrom s accumulatorWord count b e m baseOff expOff i
      start offset byte rest k)
    accumulatorWord count b e m baseOff expOff i offset byte rest (start + k)

def gasSteps_exponentBitsFrom (s : State) (accumulatorWord : UInt256)
    (count b e m baseOff expOff i start steps : Nat) (offset byte : UInt256)
    (rest : List UInt256) (hcap : rest.length < 968)
    (hcount : count < 2 ^ 256) (hbound : start + steps ≤ 8)
    (hcode : s.executionEnv.code = submissionBytecode)
    (hfork : s.fork = .Osaka) (hrun : s.halt = .Running)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig
      s.executionEnv.fork s.executionEnv.codeAddr = false) :
    Challenge.EvmProof.GasSteps
      (bitLoopFromState s accumulatorWord count b e m baseOff expOff i start
        offset byte rest 0)
      (bitLoopFromState s accumulatorWord count b e m baseOff expOff i start
        offset byte rest steps) :=
  Challenge.EvmProof.GasSteps.iterateBounded steps fun k hk => by
    let current := exponentBitProgressFrom s accumulatorWord count b e m
      baseOff expOff i start offset byte rest k
    have hstep := BigExponent.gasSteps_exponentBit current accumulatorWord count
      b e m baseOff expOff i (start + k) offset byte rest hcap hcount
      (by omega)
      (by simpa [current] using hcode)
      (by simpa [current, State.fork] using hfork)
      (by simpa [current] using hrun)
      (by simpa [current, State.fork] using hnp)
    simpa [bitLoopFromState, BigExponent.afterSelectedBit,
      exponentBitProgressFrom, current, Nat.add_assoc] using hstep

def firstByteProgress (s : State) (accumulatorWord : UInt256)
    (count b e m baseOff expOff i j : Nat) (rest : List UInt256) : State :=
  exponentBitProgressFrom s accumulatorWord count b e m baseOff expOff i j
    (loadedOffset expOff i) (loadedByte s expOff i) rest (8 - j)

def gasSteps_finishFirstByte (s : State) (accumulatorWord : UInt256)
    (count b e m baseOff expOff i j : Nat) (rest : List UInt256)
    (hcap : rest.length < 968) (hcount : count < 2 ^ 256)
    (hj : j < 8) (hi : i < e) (he : e < 2 ^ 256)
    (hcode : s.executionEnv.code = submissionBytecode)
    (hfork : s.fork = .Osaka) (hrun : s.halt = .Running)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig
      s.executionEnv.fork s.executionEnv.codeAddr = false) :
    Challenge.EvmProof.GasSteps
      (BigExponent.innerLoop s accumulatorWord count b e m baseOff expOff i
        (loadedOffset expOff i) (loadedByte s expOff i) rest j)
      (BigExponent.outerLoop
        (firstByteProgress s accumulatorWord count b e m baseOff expOff i j
          rest)
        accumulatorWord count b e m baseOff expOff rest (i + 1)) := by
  have hbits := gasSteps_exponentBitsFrom s accumulatorWord count b e m baseOff
    expOff i j (8 - j) (loadedOffset expOff i) (loadedByte s expOff i) rest
    hcap hcount (by omega) hcode hfork hrun hnp
  let progress := firstByteProgress s accumulatorWord count b e m baseOff
    expOff i j rest
  have hjSum : j + (8 - j) = 8 := by omega
  have hbits' : Challenge.EvmProof.GasSteps
      (BigExponent.innerLoop s accumulatorWord count b e m baseOff expOff i
        (loadedOffset expOff i) (loadedByte s expOff i) rest j)
      (BigExponent.innerLoop progress accumulatorWord count b e m baseOff
        expOff i (loadedOffset expOff i) (loadedByte s expOff i) rest 8) :=
    Challenge.EvmProof.GasSteps.cast hbits
      (by simp [bitLoopFromState, exponentBitProgressFrom])
      (by simp [bitLoopFromState, progress, firstByteProgress, hjSum])
  have hguard := soundBlock
    (s := BigExponent.innerLoop progress accumulatorWord count b e m baseOff
      expOff i (loadedOffset expOff i) (loadedByte s expOff i) rest 8)
    BigExponent.innerGuardPath
    (by simpa [BigExponent.innerLoop, progress, firstByteProgress] using hcode)
    (by simpa [BigExponent.innerLoop, progress, firstByteProgress, State.fork]
      using hfork)
    (by simpa [BigExponent.innerLoop, progress, firstByteProgress] using hrun)
    (by simpa [BigExponent.innerLoop, progress, firstByteProgress, State.fork]
      using hnp)
    (BigExponent.run_innerFinishGuard progress accumulatorWord count b e m
      baseOff expOff i (loadedOffset expOff i) (loadedByte s expOff i) rest
      (by omega)
      (by simpa [progress, firstByteProgress] using hcode)
      (by simpa [progress, firstByteProgress] using hrun))
  have hfinish := soundBlock
    (s := BigExponent.innerExit progress accumulatorWord count b e m baseOff
      expOff i (loadedOffset expOff i) (loadedByte s expOff i) rest)
    BigExponent.innerFinishPath
    (by simpa [BigExponent.innerExit, BigExponent.innerLoop, progress,
      firstByteProgress] using hcode)
    (by simpa [BigExponent.innerExit, BigExponent.innerLoop, progress,
      firstByteProgress, State.fork] using hfork)
    (by simpa [BigExponent.innerExit, BigExponent.innerLoop, progress,
      firstByteProgress] using hrun)
    (by simpa [BigExponent.innerExit, BigExponent.innerLoop, progress,
      firstByteProgress, State.fork] using hnp)
    (BigExponent.run_innerFinish progress accumulatorWord count b e m baseOff
      expOff i (loadedOffset expOff i) (loadedByte s expOff i) rest
      (by omega) (by omega)
      (by simpa [progress, firstByteProgress] using hcode)
      (by simpa [progress, firstByteProgress] using hrun))
  exact hbits'.trans (hguard.trans hfinish)

def exponentByteProgressFrom (s : State) (accumulatorWord : UInt256)
    (count b e m baseOff expOff start : Nat) (rest : List UInt256) : Nat → State
  | 0 => s
  | k + 1 =>
      let before := exponentByteProgressFrom s accumulatorWord count b e m
        baseOff expOff start rest k
      let i := start + k
      BigExponent.exponentBitProgress before accumulatorWord count b e m baseOff
        expOff i (UInt256.ofNat (expOff + i))
        (BigExponent.loadedExponentByte before expOff i) rest 8

@[simp] theorem exponentByteProgressFrom_executionEnv (s : State)
    (accumulatorWord : UInt256) (count b e m baseOff expOff start k : Nat)
    (rest : List UInt256) :
    (exponentByteProgressFrom s accumulatorWord count b e m baseOff expOff
      start rest k).executionEnv = s.executionEnv := by
  induction k with
  | zero => rfl
  | succ k ih => simp [exponentByteProgressFrom, ih]

@[simp] theorem exponentByteProgressFrom_halt (s : State)
    (accumulatorWord : UInt256) (count b e m baseOff expOff start k : Nat)
    (rest : List UInt256) :
    (exponentByteProgressFrom s accumulatorWord count b e m baseOff expOff
      start rest k).halt = s.halt := by
  induction k with
  | zero => rfl
  | succ k ih => simp [exponentByteProgressFrom, ih]

def outerLoopFromState (s : State) (accumulatorWord : UInt256)
    (count b e m baseOff expOff start : Nat) (rest : List UInt256)
    (k : Nat) : State :=
  BigExponent.outerLoop
    (exponentByteProgressFrom s accumulatorWord count b e m baseOff expOff
      start rest k)
    accumulatorWord count b e m baseOff expOff rest (start + k)

def gasSteps_exponentBytesFrom (s : State) (accumulatorWord : UInt256)
    (count b e m baseOff expOff start steps : Nat) (rest : List UInt256)
    (hcap : rest.length < 968) (hcount : count < 2 ^ 256)
    (he : e < 2 ^ 256) (hbound : start + steps ≤ e)
    (hexpFit : expOff + e < 2 ^ 256)
    (hcode : s.executionEnv.code = submissionBytecode)
    (hfork : s.fork = .Osaka) (hrun : s.halt = .Running)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig
      s.executionEnv.fork s.executionEnv.codeAddr = false) :
    Challenge.EvmProof.GasSteps
      (outerLoopFromState s accumulatorWord count b e m baseOff expOff start
        rest 0)
      (outerLoopFromState s accumulatorWord count b e m baseOff expOff start
        rest steps) :=
  Challenge.EvmProof.GasSteps.iterateBounded steps fun k hk => by
    let current := exponentByteProgressFrom s accumulatorWord count b e m
      baseOff expOff start rest k
    let i := start + k
    have hstep := BigExponent.gasSteps_exponentByte current accumulatorWord count
      b e m baseOff expOff i rest hcap hcount he (by omega) (by omega)
      (by simpa [current] using hcode)
      (by simpa [current, State.fork] using hfork)
      (by simpa [current] using hrun)
      (by simpa [current, State.fork] using hnp)
    simpa [outerLoopFromState, BigExponent.afterExponentByte,
      exponentByteProgressFrom, current, i, Nat.add_assoc] using hstep

def foundProgress (s : State) (accumulatorWord : UInt256)
    (count b e m baseOff expOff i j : Nat) (rest : List UInt256) : State :=
  let first := firstByteProgress s accumulatorWord count b e m baseOff expOff
    i j rest
  exponentByteProgressFrom first accumulatorWord count b e m baseOff expOff
    (i + 1) rest (e - (i + 1))

def gasSteps_finishFound (s : State) (accumulatorWord : UInt256)
    (count b e m baseOff expOff i j : Nat) (rest : List UInt256)
    (hcap : rest.length < 968) (hcount : count < 2 ^ 256)
    (he : e < 2 ^ 256) (hi : i < e) (hj : j < 8)
    (hexpFit : expOff + e < 2 ^ 256)
    (hcode : s.executionEnv.code = submissionBytecode)
    (hfork : s.fork = .Osaka) (hrun : s.halt = .Running)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig
      s.executionEnv.fork s.executionEnv.codeAddr = false) :
    Challenge.EvmProof.GasSteps
      (BigExponent.innerLoop s accumulatorWord count b e m baseOff expOff i
        (loadedOffset expOff i) (loadedByte s expOff i) rest j)
      (BigExponent.outerLoop
        (foundProgress s accumulatorWord count b e m baseOff expOff i j rest)
        accumulatorWord count b e m baseOff expOff rest e) := by
  let first := firstByteProgress s accumulatorWord count b e m baseOff expOff
    i j rest
  have hfirst := gasSteps_finishFirstByte s accumulatorWord count b e m baseOff
    expOff i j rest hcap hcount hj hi he hcode hfork hrun hnp
  have hrest := gasSteps_exponentBytesFrom first accumulatorWord count b e m
    baseOff expOff (i + 1) (e - (i + 1)) rest hcap hcount he
    (by omega) hexpFit
    (by simpa [first, firstByteProgress] using hcode)
    (by simpa [first, firstByteProgress, State.fork] using hfork)
    (by simpa [first, firstByteProgress] using hrun)
    (by simpa [first, firstByteProgress, State.fork] using hnp)
  have hsum : i + 1 + (e - (i + 1)) = e := by omega
  exact Challenge.EvmProof.GasSteps.cast (hfirst.trans hrest) rfl
    (by simp [outerLoopFromState, foundProgress, first, hsum])

def exponentPhaseState (s : State) (accumulatorWord : UInt256)
    (count b e m baseOff expOff : Nat) (rest : List UInt256) : State :=
  let i := coldByteIndex s expOff e
  if i = e then s
  else foundProgress s accumulatorWord count b e m baseOff expOff i
    (coldBitIndex (loadedByte s expOff i)) rest

@[simp] theorem exponentPhaseState_executionEnv (s : State)
    (accumulatorWord : UInt256) (count b e m baseOff expOff : Nat)
    (rest : List UInt256) :
    (exponentPhaseState s accumulatorWord count b e m baseOff expOff
      rest).executionEnv = s.executionEnv := by
  by_cases h : coldByteIndex s expOff e = e <;>
    simp [exponentPhaseState, h, foundProgress, firstByteProgress]

@[simp] theorem exponentPhaseState_halt (s : State)
    (accumulatorWord : UInt256) (count b e m baseOff expOff : Nat)
    (rest : List UInt256) :
    (exponentPhaseState s accumulatorWord count b e m baseOff expOff
      rest).halt = s.halt := by
  by_cases h : coldByteIndex s expOff e = e <;>
    simp [exponentPhaseState, h, foundProgress, firstByteProgress]

def gasSteps_exponentPhase (s : State) (accumulatorWord : UInt256)
    (count b e m baseOff expOff : Nat) (rest : List UInt256)
    (hcap : rest.length < 968) (hcount : count < 2 ^ 256)
    (he : e < 2 ^ 256) (hexpFit : expOff + e < 2 ^ 256)
    (hcode : s.executionEnv.code = submissionBytecode)
    (hfork : s.fork = .Osaka) (hrun : s.halt = .Running)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig
      s.executionEnv.fork s.executionEnv.codeAddr = false) :
    Challenge.EvmProof.GasSteps
      (scanEntry s accumulatorWord count b e m baseOff expOff rest)
      (BigExponent.outerLoop
        (exponentPhaseState s accumulatorWord count b e m baseOff expOff rest)
        accumulatorWord count b e m baseOff expOff rest e) := by
  let i := coldByteIndex s expOff e
  have hiLe : i ≤ e := coldByteIndex_le s expOff e
  by_cases hiEq : i = e
  · have hzero : ∀ k, k < e → (loadedByte s expOff k).toNat = 0 := by
      intro k hk
      exact coldByteIndex_zeros s expOff e k (by simpa [i, hiEq] using hk)
    have hall := gasSteps_scanAllZero s accumulatorWord count b e m baseOff
      expOff rest hcap he hexpFit hzero hcode hfork hrun hnp
    exact Challenge.EvmProof.GasSteps.cast hall rfl
      (by simp [exponentPhaseState, i, hiEq])
  · have hi : i < e := by omega
    let byte := loadedByte s expOff i
    let j := coldBitIndex byte
    have hbyte : byte.toNat ≠ 0 := by
      simpa [byte, i] using coldByteIndex_hit s expOff e hi
    have hbyteLt : byte.toNat < 256 := by
      simpa [byte] using loadedByte_lt256 s expOff i
    have hj : j < 8 := coldBitIndex_lt byte hbyteLt hbyte
    have hscan := gasSteps_scanFound s accumulatorWord count b e m baseOff
      expOff i j rest hcap hi hj hexpFit
      (fun k hk => coldByteIndex_zeros s expOff e k (by simpa [i] using hk))
      (by simpa [byte] using hbyte)
      (fun k hk => by simpa [byte, j] using coldBitIndex_zeros byte k hk)
      (by simpa [byte, j] using coldBitIndex_hit byte hj)
      hcode hfork hrun hnp
    have hfinish := gasSteps_finishFound s accumulatorWord count b e m baseOff
      expOff i j rest hcap hcount he hi hj hexpFit hcode hfork hrun hnp
    exact Challenge.EvmProof.GasSteps.cast (hscan.trans hfinish) rfl
      (by simp [exponentPhaseState, i, hiEq, byte, j])

end Challenge.Modexp.Submission.Proofs.Bytecode.BigExponentScanGas
