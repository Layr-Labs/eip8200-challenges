import Challenge.Ripemd160.Submission.Proofs.Bytecode.FullInlineSiteData
set_option warningAsError true
set_option maxRecDepth 100000
set_option maxHeartbeats 16000000
namespace Challenge.Ripemd160.Submission.Proofs.Bytecode.FullInlineSites
open EvmSemantics EvmSemantics.EVM YulEvmCompiler Challenge.EvmProof StackRoundTemplate
def left (k : Fin 20) : GenericRoundSite A .Osaka (CachedMaskQuadGroup.code (FullInlineParams.left k) 0) :=
  match k with
  | ⟨0, _⟩ => left0
  | ⟨1, _⟩ => left1
  | ⟨2, _⟩ => left2
  | ⟨3, _⟩ => left3
  | ⟨4, _⟩ => left4
  | ⟨5, _⟩ => left5
  | ⟨6, _⟩ => left6
  | ⟨7, _⟩ => left7
  | ⟨8, _⟩ => left8
  | ⟨9, _⟩ => left9
  | ⟨10, _⟩ => left10
  | ⟨11, _⟩ => left11
  | ⟨12, _⟩ => left12
  | ⟨13, _⟩ => left13
  | ⟨14, _⟩ => left14
  | ⟨15, _⟩ => left15
  | ⟨16, _⟩ => left16
  | ⟨17, _⟩ => left17
  | ⟨18, _⟩ => left18
  | ⟨19, _⟩ => left19
  | ⟨n + 20, h⟩ => False.elim (by omega)
def leftPC (n : Nat) : UInt256 := match n with
  | 0 => 5234
  | 1 => 5350
  | 2 => 5466
  | 3 => 5582
  | 4 => 5698
  | 5 => 5846
  | 6 => 5994
  | 7 => 6142
  | 8 => 6290
  | 9 => 6434
  | 10 => 6578
  | 11 => 6722
  | 12 => 6866
  | 13 => 7014
  | 14 => 7162
  | 15 => 7310
  | 16 => 7458
  | 17 => 7602
  | 18 => 7746
  | 19 => 7890
  | _ => 8034
theorem left_start (k : Fin 20) : (left k).startPC = leftPC k.val := by
  fin_cases k
  · change UInt256.ofNat (A.instructionPC 3147) = UInt256.ofNat 5234
    rw [ArtifactByteLength.instructionPC_eq_byteLength]
    rfl
  · change UInt256.ofNat (A.instructionPC 3247) = UInt256.ofNat 5350
    rw [ArtifactByteLength.instructionPC_eq_byteLength]
    rfl
  · change UInt256.ofNat (A.instructionPC 3347) = UInt256.ofNat 5466
    rw [ArtifactByteLength.instructionPC_eq_byteLength]
    rfl
  · change UInt256.ofNat (A.instructionPC 3447) = UInt256.ofNat 5582
    rw [ArtifactByteLength.instructionPC_eq_byteLength]
    rfl
  · change UInt256.ofNat (A.instructionPC 3547) = UInt256.ofNat 5698
    rw [ArtifactByteLength.instructionPC_eq_byteLength]
    rfl
  · change UInt256.ofNat (A.instructionPC 3663) = UInt256.ofNat 5846
    rw [ArtifactByteLength.instructionPC_eq_byteLength]
    rfl
  · change UInt256.ofNat (A.instructionPC 3779) = UInt256.ofNat 5994
    rw [ArtifactByteLength.instructionPC_eq_byteLength]
    rfl
  · change UInt256.ofNat (A.instructionPC 3895) = UInt256.ofNat 6142
    rw [ArtifactByteLength.instructionPC_eq_byteLength]
    rfl
  · change UInt256.ofNat (A.instructionPC 4011) = UInt256.ofNat 6290
    rw [ArtifactByteLength.instructionPC_eq_byteLength]
    rfl
  · change UInt256.ofNat (A.instructionPC 4123) = UInt256.ofNat 6434
    rw [ArtifactByteLength.instructionPC_eq_byteLength]
    rfl
  · change UInt256.ofNat (A.instructionPC 4235) = UInt256.ofNat 6578
    rw [ArtifactByteLength.instructionPC_eq_byteLength]
    rfl
  · change UInt256.ofNat (A.instructionPC 4347) = UInt256.ofNat 6722
    rw [ArtifactByteLength.instructionPC_eq_byteLength]
    rfl
  · change UInt256.ofNat (A.instructionPC 4459) = UInt256.ofNat 6866
    rw [ArtifactByteLength.instructionPC_eq_byteLength]
    rfl
  · change UInt256.ofNat (A.instructionPC 4575) = UInt256.ofNat 7014
    rw [ArtifactByteLength.instructionPC_eq_byteLength]
    rfl
  · change UInt256.ofNat (A.instructionPC 4691) = UInt256.ofNat 7162
    rw [ArtifactByteLength.instructionPC_eq_byteLength]
    rfl
  · change UInt256.ofNat (A.instructionPC 4807) = UInt256.ofNat 7310
    rw [ArtifactByteLength.instructionPC_eq_byteLength]
    rfl
  · change UInt256.ofNat (A.instructionPC 4923) = UInt256.ofNat 7458
    rw [ArtifactByteLength.instructionPC_eq_byteLength]
    rfl
  · change UInt256.ofNat (A.instructionPC 5035) = UInt256.ofNat 7602
    rw [ArtifactByteLength.instructionPC_eq_byteLength]
    rfl
  · change UInt256.ofNat (A.instructionPC 5147) = UInt256.ofNat 7746
    rw [ArtifactByteLength.instructionPC_eq_byteLength]
    rfl
  · change UInt256.ofNat (A.instructionPC 5259) = UInt256.ofNat 7890
    rw [ArtifactByteLength.instructionPC_eq_byteLength]
    rfl
theorem left_end (k : Fin 20) : (left k).endPC = leftPC (k.val + 1) := by
  fin_cases k
  · change UInt256.ofNat (A.instructionPC 3247) = UInt256.ofNat 5350
    rw [ArtifactByteLength.instructionPC_eq_byteLength]
    rfl
  · change UInt256.ofNat (A.instructionPC 3347) = UInt256.ofNat 5466
    rw [ArtifactByteLength.instructionPC_eq_byteLength]
    rfl
  · change UInt256.ofNat (A.instructionPC 3447) = UInt256.ofNat 5582
    rw [ArtifactByteLength.instructionPC_eq_byteLength]
    rfl
  · change UInt256.ofNat (A.instructionPC 3547) = UInt256.ofNat 5698
    rw [ArtifactByteLength.instructionPC_eq_byteLength]
    rfl
  · change UInt256.ofNat (A.instructionPC 3663) = UInt256.ofNat 5846
    rw [ArtifactByteLength.instructionPC_eq_byteLength]
    rfl
  · change UInt256.ofNat (A.instructionPC 3779) = UInt256.ofNat 5994
    rw [ArtifactByteLength.instructionPC_eq_byteLength]
    rfl
  · change UInt256.ofNat (A.instructionPC 3895) = UInt256.ofNat 6142
    rw [ArtifactByteLength.instructionPC_eq_byteLength]
    rfl
  · change UInt256.ofNat (A.instructionPC 4011) = UInt256.ofNat 6290
    rw [ArtifactByteLength.instructionPC_eq_byteLength]
    rfl
  · change UInt256.ofNat (A.instructionPC 4123) = UInt256.ofNat 6434
    rw [ArtifactByteLength.instructionPC_eq_byteLength]
    rfl
  · change UInt256.ofNat (A.instructionPC 4235) = UInt256.ofNat 6578
    rw [ArtifactByteLength.instructionPC_eq_byteLength]
    rfl
  · change UInt256.ofNat (A.instructionPC 4347) = UInt256.ofNat 6722
    rw [ArtifactByteLength.instructionPC_eq_byteLength]
    rfl
  · change UInt256.ofNat (A.instructionPC 4459) = UInt256.ofNat 6866
    rw [ArtifactByteLength.instructionPC_eq_byteLength]
    rfl
  · change UInt256.ofNat (A.instructionPC 4575) = UInt256.ofNat 7014
    rw [ArtifactByteLength.instructionPC_eq_byteLength]
    rfl
  · change UInt256.ofNat (A.instructionPC 4691) = UInt256.ofNat 7162
    rw [ArtifactByteLength.instructionPC_eq_byteLength]
    rfl
  · change UInt256.ofNat (A.instructionPC 4807) = UInt256.ofNat 7310
    rw [ArtifactByteLength.instructionPC_eq_byteLength]
    rfl
  · change UInt256.ofNat (A.instructionPC 4923) = UInt256.ofNat 7458
    rw [ArtifactByteLength.instructionPC_eq_byteLength]
    rfl
  · change UInt256.ofNat (A.instructionPC 5035) = UInt256.ofNat 7602
    rw [ArtifactByteLength.instructionPC_eq_byteLength]
    rfl
  · change UInt256.ofNat (A.instructionPC 5147) = UInt256.ofNat 7746
    rw [ArtifactByteLength.instructionPC_eq_byteLength]
    rfl
  · change UInt256.ofNat (A.instructionPC 5259) = UInt256.ofNat 7890
    rw [ArtifactByteLength.instructionPC_eq_byteLength]
    rfl
  · change UInt256.ofNat (A.instructionPC 5371) = UInt256.ofNat 8034
    rw [ArtifactByteLength.instructionPC_eq_byteLength]
    rfl

def right (k : Fin 20) : GenericRoundSite A .Osaka (CachedMaskQuadGroup.code (FullInlineParams.right k) 5) :=
  match k with
  | ⟨0, _⟩ => right0
  | ⟨1, _⟩ => right1
  | ⟨2, _⟩ => right2
  | ⟨3, _⟩ => right3
  | ⟨4, _⟩ => right4
  | ⟨5, _⟩ => right5
  | ⟨6, _⟩ => right6
  | ⟨7, _⟩ => right7
  | ⟨8, _⟩ => right8
  | ⟨9, _⟩ => right9
  | ⟨10, _⟩ => right10
  | ⟨11, _⟩ => right11
  | ⟨12, _⟩ => right12
  | ⟨13, _⟩ => right13
  | ⟨14, _⟩ => right14
  | ⟨15, _⟩ => right15
  | ⟨16, _⟩ => right16
  | ⟨17, _⟩ => right17
  | ⟨18, _⟩ => right18
  | ⟨19, _⟩ => right19
  | ⟨n + 20, h⟩ => False.elim (by omega)
def rightPC (n : Nat) : UInt256 := match n with
  | 0 => 8039
  | 1 => 8183
  | 2 => 8327
  | 3 => 8471
  | 4 => 8615
  | 5 => 8763
  | 6 => 8911
  | 7 => 9059
  | 8 => 9207
  | 9 => 9351
  | 10 => 9495
  | 11 => 9639
  | 12 => 9783
  | 13 => 9931
  | 14 => 10079
  | 15 => 10227
  | 16 => 10375
  | 17 => 10491
  | 18 => 10607
  | 19 => 10723
  | _ => 10839
theorem right_start (k : Fin 20) : (right k).startPC = rightPC k.val := by
  fin_cases k
  · change UInt256.ofNat (A.instructionPC 5374) = UInt256.ofNat 8039
    rw [ArtifactByteLength.instructionPC_eq_byteLength]
    rfl
  · change UInt256.ofNat (A.instructionPC 5486) = UInt256.ofNat 8183
    rw [ArtifactByteLength.instructionPC_eq_byteLength]
    rfl
  · change UInt256.ofNat (A.instructionPC 5598) = UInt256.ofNat 8327
    rw [ArtifactByteLength.instructionPC_eq_byteLength]
    rfl
  · change UInt256.ofNat (A.instructionPC 5710) = UInt256.ofNat 8471
    rw [ArtifactByteLength.instructionPC_eq_byteLength]
    rfl
  · change UInt256.ofNat (A.instructionPC 5822) = UInt256.ofNat 8615
    rw [ArtifactByteLength.instructionPC_eq_byteLength]
    rfl
  · change UInt256.ofNat (A.instructionPC 5938) = UInt256.ofNat 8763
    rw [ArtifactByteLength.instructionPC_eq_byteLength]
    rfl
  · change UInt256.ofNat (A.instructionPC 6054) = UInt256.ofNat 8911
    rw [ArtifactByteLength.instructionPC_eq_byteLength]
    rfl
  · change UInt256.ofNat (A.instructionPC 6170) = UInt256.ofNat 9059
    rw [ArtifactByteLength.instructionPC_eq_byteLength]
    rfl
  · change UInt256.ofNat (A.instructionPC 6286) = UInt256.ofNat 9207
    rw [ArtifactByteLength.instructionPC_eq_byteLength]
    rfl
  · change UInt256.ofNat (A.instructionPC 6398) = UInt256.ofNat 9351
    rw [ArtifactByteLength.instructionPC_eq_byteLength]
    rfl
  · change UInt256.ofNat (A.instructionPC 6510) = UInt256.ofNat 9495
    rw [ArtifactByteLength.instructionPC_eq_byteLength]
    rfl
  · change UInt256.ofNat (A.instructionPC 6622) = UInt256.ofNat 9639
    rw [ArtifactByteLength.instructionPC_eq_byteLength]
    rfl
  · change UInt256.ofNat (A.instructionPC 6734) = UInt256.ofNat 9783
    rw [ArtifactByteLength.instructionPC_eq_byteLength]
    rfl
  · change UInt256.ofNat (A.instructionPC 6850) = UInt256.ofNat 9931
    rw [ArtifactByteLength.instructionPC_eq_byteLength]
    rfl
  · change UInt256.ofNat (A.instructionPC 6966) = UInt256.ofNat 10079
    rw [ArtifactByteLength.instructionPC_eq_byteLength]
    rfl
  · change UInt256.ofNat (A.instructionPC 7082) = UInt256.ofNat 10227
    rw [ArtifactByteLength.instructionPC_eq_byteLength]
    rfl
  · change UInt256.ofNat (A.instructionPC 7198) = UInt256.ofNat 10375
    rw [ArtifactByteLength.instructionPC_eq_byteLength]
    rfl
  · change UInt256.ofNat (A.instructionPC 7298) = UInt256.ofNat 10491
    rw [ArtifactByteLength.instructionPC_eq_byteLength]
    rfl
  · change UInt256.ofNat (A.instructionPC 7398) = UInt256.ofNat 10607
    rw [ArtifactByteLength.instructionPC_eq_byteLength]
    rfl
  · change UInt256.ofNat (A.instructionPC 7498) = UInt256.ofNat 10723
    rw [ArtifactByteLength.instructionPC_eq_byteLength]
    rfl
theorem right_end (k : Fin 20) : (right k).endPC = rightPC (k.val + 1) := by
  fin_cases k
  · change UInt256.ofNat (A.instructionPC 5486) = UInt256.ofNat 8183
    rw [ArtifactByteLength.instructionPC_eq_byteLength]
    rfl
  · change UInt256.ofNat (A.instructionPC 5598) = UInt256.ofNat 8327
    rw [ArtifactByteLength.instructionPC_eq_byteLength]
    rfl
  · change UInt256.ofNat (A.instructionPC 5710) = UInt256.ofNat 8471
    rw [ArtifactByteLength.instructionPC_eq_byteLength]
    rfl
  · change UInt256.ofNat (A.instructionPC 5822) = UInt256.ofNat 8615
    rw [ArtifactByteLength.instructionPC_eq_byteLength]
    rfl
  · change UInt256.ofNat (A.instructionPC 5938) = UInt256.ofNat 8763
    rw [ArtifactByteLength.instructionPC_eq_byteLength]
    rfl
  · change UInt256.ofNat (A.instructionPC 6054) = UInt256.ofNat 8911
    rw [ArtifactByteLength.instructionPC_eq_byteLength]
    rfl
  · change UInt256.ofNat (A.instructionPC 6170) = UInt256.ofNat 9059
    rw [ArtifactByteLength.instructionPC_eq_byteLength]
    rfl
  · change UInt256.ofNat (A.instructionPC 6286) = UInt256.ofNat 9207
    rw [ArtifactByteLength.instructionPC_eq_byteLength]
    rfl
  · change UInt256.ofNat (A.instructionPC 6398) = UInt256.ofNat 9351
    rw [ArtifactByteLength.instructionPC_eq_byteLength]
    rfl
  · change UInt256.ofNat (A.instructionPC 6510) = UInt256.ofNat 9495
    rw [ArtifactByteLength.instructionPC_eq_byteLength]
    rfl
  · change UInt256.ofNat (A.instructionPC 6622) = UInt256.ofNat 9639
    rw [ArtifactByteLength.instructionPC_eq_byteLength]
    rfl
  · change UInt256.ofNat (A.instructionPC 6734) = UInt256.ofNat 9783
    rw [ArtifactByteLength.instructionPC_eq_byteLength]
    rfl
  · change UInt256.ofNat (A.instructionPC 6850) = UInt256.ofNat 9931
    rw [ArtifactByteLength.instructionPC_eq_byteLength]
    rfl
  · change UInt256.ofNat (A.instructionPC 6966) = UInt256.ofNat 10079
    rw [ArtifactByteLength.instructionPC_eq_byteLength]
    rfl
  · change UInt256.ofNat (A.instructionPC 7082) = UInt256.ofNat 10227
    rw [ArtifactByteLength.instructionPC_eq_byteLength]
    rfl
  · change UInt256.ofNat (A.instructionPC 7198) = UInt256.ofNat 10375
    rw [ArtifactByteLength.instructionPC_eq_byteLength]
    rfl
  · change UInt256.ofNat (A.instructionPC 7298) = UInt256.ofNat 10491
    rw [ArtifactByteLength.instructionPC_eq_byteLength]
    rfl
  · change UInt256.ofNat (A.instructionPC 7398) = UInt256.ofNat 10607
    rw [ArtifactByteLength.instructionPC_eq_byteLength]
    rfl
  · change UInt256.ofNat (A.instructionPC 7498) = UInt256.ofNat 10723
    rw [ArtifactByteLength.instructionPC_eq_byteLength]
    rfl
  · change UInt256.ofNat (A.instructionPC 7598) = UInt256.ofNat 10839
    rw [ArtifactByteLength.instructionPC_eq_byteLength]
    rfl

end Challenge.Ripemd160.Submission.Proofs.Bytecode.FullInlineSites
