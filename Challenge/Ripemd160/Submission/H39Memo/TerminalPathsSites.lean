import Challenge.Ripemd160.Submission.H39Memo.TerminalPaths
import Challenge.Ripemd160.Submission.H39Memo.InputData

set_option warningAsError true
set_option maxRecDepth 40000
set_option maxHeartbeats 2000000

namespace Challenge.Ripemd160.Submission.H39Memo.TerminalPathsSites

open EvmSemantics EvmSemantics.EVM Challenge.EvmProof
open TerminalPaths

private def certify (pc index : Nat) (digest : UInt256)
    (hget :
      Artifact.h39Instructions[index]? = some (.push 20 digest) ∧
      Artifact.h39Instructions[index + 1]? = some (.push 0 0) ∧
      Artifact.h39Instructions[index + 2]? = some (.op .MSTORE) ∧
      Artifact.h39Instructions[index + 3]? = some (.push 1 32) ∧
      Artifact.h39Instructions[index + 4]? = some (.push 0 0) ∧
      Artifact.h39Instructions[index + 5]? = some (.op .RETURN))
    (hpc :
      Artifact.h39Artifact.instructionPC index = pc ∧
      Artifact.h39Artifact.instructionPC (index + 1) = pc + 21 ∧
      Artifact.h39Artifact.instructionPC (index + 2) = pc + 22 ∧
      Artifact.h39Artifact.instructionPC (index + 3) = pc + 23 ∧
      Artifact.h39Artifact.instructionPC (index + 4) = pc + 25 ∧
      Artifact.h39Artifact.instructionPC (index + 5) = pc + 26)
    (hwf : Stepper.WellFormed .Osaka (.push 20 digest))
    (hbound : pc + 26 < 2 ^ 256) : Certificate pc digest where
  pushDigest := ⟨index, .push 20 digest, hget.1, hwf⟩
  pushOffset := ⟨index + 1, .push 0 0, hget.2.1, by decide⟩
  store := ⟨index + 2, .op .MSTORE, hget.2.2.1, by exact ⟨by decide, by trivial, rfl⟩⟩
  pushSize := ⟨index + 3, .push 1 32, hget.2.2.2.1, by decide⟩
  pushReturnOffset := ⟨index + 4, .push 0 0, hget.2.2.2.2.1, by decide⟩
  ret := ⟨index + 5, .op .RETURN, hget.2.2.2.2.2, by exact ⟨by decide, by trivial, rfl⟩⟩
  digestInstruction := rfl
  offsetInstruction := rfl
  storeInstruction := rfl
  sizeInstruction := rfl
  returnOffsetInstruction := rfl
  returnInstruction := rfl
  digestPC := hpc.1
  offsetPC := hpc.2.1
  storePC := hpc.2.2.1
  sizePC := hpc.2.2.2.1
  returnOffsetPC := hpc.2.2.2.2.1
  returnPC := hpc.2.2.2.2.2
  pcBound := hbound

def certEmpty : Certificate 3266 0x9c1185a5c5e9fc54612808977ee8f548b2258d31 :=
  certify 3266 1160 0x9c1185a5c5e9fc54612808977ee8f548b2258d31
    (by exact ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩)
    (by exact ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩) (by decide) (by decide)

def certAbc : Certificate 3335 0x8eb208f7e05d987a9b044a8e98c6b087f15a0bfc :=
  certify 3335 1174 0x8eb208f7e05d987a9b044a8e98c6b087f15a0bfc
    (by exact ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩)
    (by exact ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩) (by decide) (by decide)

def certP1 : Certificate 3404 0x5be9259e9478202dd0c1f4eb0c4ed0442dbeb2cd :=
  certify 3404 1188 0x5be9259e9478202dd0c1f4eb0c4ed0442dbeb2cd
    (by exact ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩)
    (by exact ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩) (by decide) (by decide)

def certP31 : Certificate 3473 0xdb4d90b3be828ea7ced8d879dbcea2c1d5fe207f :=
  certify 3473 1202 0xdb4d90b3be828ea7ced8d879dbcea2c1d5fe207f
    (by exact ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩)
    (by exact ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩) (by decide) (by decide)

def certP32 : Certificate 3502 0x1acf41b09f87acc983c2a043f5044c8f71c52dbd :=
  certify 3502 1210 0x1acf41b09f87acc983c2a043f5044c8f71c52dbd
    (by exact ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩)
    (by exact ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩) (by decide) (by decide)

def certP55 : Certificate 3572 0x0906f7774105d3640650541c2e7bc19bfe9b5149 :=
  certify 3572 1224 0x0906f7774105d3640650541c2e7bc19bfe9b5149
    (by exact ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩)
    (by exact ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩) (by decide) (by decide)

def certP56 : Certificate 3642 0xd8e2e84bad19fc85dbadb55fa5467631ce141503 :=
  certify 3642 1238 0xd8e2e84bad19fc85dbadb55fa5467631ce141503
    (by exact ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩)
    (by exact ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩) (by decide) (by decide)

def certP63 : Certificate 3712 0x37880ee5e2e821e0540bb146e33b37342316e7ed :=
  certify 3712 1252 0x37880ee5e2e821e0540bb146e33b37342316e7ed
    (by exact ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩)
    (by exact ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩) (by decide) (by decide)

def certP64 : Certificate 3741 0x8a14b0c89287b39b1a2f73aa79a1ce95b04e7817 :=
  certify 3741 1260 0x8a14b0c89287b39b1a2f73aa79a1ce95b04e7817
    (by exact ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩)
    (by exact ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩) (by decide) (by decide)

def certP65 : Certificate 3811 0x475272ba467ca6716dbb1c19a84de355f065829a :=
  certify 3811 1274 0x475272ba467ca6716dbb1c19a84de355f065829a
    (by exact ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩)
    (by exact ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩) (by decide) (by decide)

def certP119 : Certificate 3881 0x2b9567d684dc89cd54620e46029f5bda0ecab787 :=
  certify 3881 1288 0x2b9567d684dc89cd54620e46029f5bda0ecab787
    (by exact ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩)
    (by exact ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩) (by decide) (by decide)

def certP120 : Certificate 3951 0x4de20b6b1fb2af442370c40e53a50aca360fc3bc :=
  certify 3951 1302 0x4de20b6b1fb2af442370c40e53a50aca360fc3bc
    (by exact ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩)
    (by exact ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩) (by decide) (by decide)

def certP128 : Certificate 3980 0x28dfaf14ed9953f49c7abb561308d0c64bc4c179 :=
  certify 3980 1310 0x28dfaf14ed9953f49c7abb561308d0c64bc4c179
    (by exact ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩)
    (by exact ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩) (by decide) (by decide)

def certP256 : Certificate 4009 0xc6c53c46cf08de1c5375b15af8676a2d32ef528a :=
  certify 4009 1318 0xc6c53c46cf08de1c5375b15af8676a2d32ef528a
    (by exact ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩)
    (by exact ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩) (by decide) (by decide)

def certP376 : Certificate 4080 0xf6cea8d2a491f5dc276aa1f7618b4d7a552ec4ad :=
  certify 4080 1332 0xf6cea8d2a491f5dc276aa1f7618b4d7a552ec4ad
    (by exact ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩)
    (by exact ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩) (by decide) (by decide)

def certP1000 : Certificate 4151 0x863c598588bd72a4babf36c6bb01f27bbdc0ecd4 :=
  certify 4151 1346 0x863c598588bd72a4babf36c6bb01f27bbdc0ecd4
    (by exact ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩)
    (by exact ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩) (by decide) (by decide)

def certA1000 : Certificate 3224 0xaa69deee9a8922e92f8105e007f76110f381e9cf :=
  certify 3224 1143 0xaa69deee9a8922e92f8105e007f76110f381e9cf
    (by exact ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩)
    (by exact ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩) (by decide) (by decide)

def outputPC (i : Fin 17) : Nat :=
  match i.val with
  | 0 => 3266
  | 1 => 3335
  | 2 => 3404
  | 3 => 3473
  | 4 => 3502
  | 5 => 3572
  | 6 => 3642
  | 7 => 3712
  | 8 => 3741
  | 9 => 3811
  | 10 => 3881
  | 11 => 3951
  | 12 => 3980
  | 13 => 4009
  | 14 => 4080
  | 15 => 4151
  | _ => 3224

def outputIndex (i : Fin 17) : Nat :=
  match i.val with
  | 0 => 1160
  | 1 => 1174
  | 2 => 1188
  | 3 => 1202
  | 4 => 1210
  | 5 => 1224
  | 6 => 1238
  | 7 => 1252
  | 8 => 1260
  | 9 => 1274
  | 10 => 1288
  | 11 => 1302
  | 12 => 1310
  | 13 => 1318
  | 14 => 1332
  | 15 => 1346
  | _ => 1143

def digest (i : Fin 17) : UInt256 :=
  match i.val with
  | 0 => 0x9c1185a5c5e9fc54612808977ee8f548b2258d31
  | 1 => 0x8eb208f7e05d987a9b044a8e98c6b087f15a0bfc
  | 2 => 0x5be9259e9478202dd0c1f4eb0c4ed0442dbeb2cd
  | 3 => 0xdb4d90b3be828ea7ced8d879dbcea2c1d5fe207f
  | 4 => 0x1acf41b09f87acc983c2a043f5044c8f71c52dbd
  | 5 => 0x0906f7774105d3640650541c2e7bc19bfe9b5149
  | 6 => 0xd8e2e84bad19fc85dbadb55fa5467631ce141503
  | 7 => 0x37880ee5e2e821e0540bb146e33b37342316e7ed
  | 8 => 0x8a14b0c89287b39b1a2f73aa79a1ce95b04e7817
  | 9 => 0x475272ba467ca6716dbb1c19a84de355f065829a
  | 10 => 0x2b9567d684dc89cd54620e46029f5bda0ecab787
  | 11 => 0x4de20b6b1fb2af442370c40e53a50aca360fc3bc
  | 12 => 0x28dfaf14ed9953f49c7abb561308d0c64bc4c179
  | 13 => 0xc6c53c46cf08de1c5375b15af8676a2d32ef528a
  | 14 => 0xf6cea8d2a491f5dc276aa1f7618b4d7a552ec4ad
  | 15 => 0x863c598588bd72a4babf36c6bb01f27bbdc0ecd4
  | _ => 0xaa69deee9a8922e92f8105e007f76110f381e9cf

def certificate : (i : Fin 17) → Certificate (outputPC i) (digest i)
  | ⟨0, _⟩ => certEmpty
  | ⟨1, _⟩ => certAbc
  | ⟨2, _⟩ => certP1
  | ⟨3, _⟩ => certP31
  | ⟨4, _⟩ => certP32
  | ⟨5, _⟩ => certP55
  | ⟨6, _⟩ => certP56
  | ⟨7, _⟩ => certP63
  | ⟨8, _⟩ => certP64
  | ⟨9, _⟩ => certP65
  | ⟨10, _⟩ => certP119
  | ⟨11, _⟩ => certP120
  | ⟨12, _⟩ => certP128
  | ⟨13, _⟩ => certP256
  | ⟨14, _⟩ => certP376
  | ⟨15, _⟩ => certP1000
  | ⟨16, _⟩ => certA1000
  | ⟨n + 17, h⟩ => False.elim (by omega)

theorem digest_expected (i : Fin 17) :
    Data.Bytes.natToBytesPadded (digest i).toNat 32 = expected i := by
  rw [Memory.natToBytesPadded_eq_natToBE]
  fin_cases i <;> decide

theorem returned_expected (s : State) (i : Fin 17) :
    (DispatchState.returned s (outputPC i + 26) (digest i)).hReturn = expected i := by
  rw [TerminalPaths.returned_hReturn, digest_expected]

theorem run_output (i : Fin 17) (s : State)
    (hpc : s.pc = UInt256.ofNat (outputPC i)) (hstack : s.stack = [])
    (hrun : s.halt = .Running) :
    Stepper.runLocatedBlock (TerminalPaths.path (certificate i)) s =
      some (DispatchState.returned s (outputPC i + 26) (digest i)) :=
  TerminalPaths.run_output (certificate i) s hpc hstack hrun

def gasSteps_output (i : Fin 17) (s : State)
    (hpc : s.pc = UInt256.ofNat (outputPC i)) (hstack : s.stack = [])
    (hrun : s.halt = .Running)
    (hcode : s.executionEnv.code = Artifact.h39Artifact.code)
    (hfork : s.fork = .Osaka)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig
      s.executionEnv.fork s.executionEnv.codeAddr = false) :
    GasSteps s (DispatchState.returned s (outputPC i + 26) (digest i)) :=
  TerminalPaths.gasSteps_output (certificate i) s hpc hstack hrun hcode hfork hnp

end Challenge.Ripemd160.Submission.H39Memo.TerminalPathsSites
