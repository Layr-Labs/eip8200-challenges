import Challenge.Modexp.Spec
import Challenge.Modexp.Submission.Proofs.Bytecode.WindowGuardLogic
import Challenge.EvmProof.Bytes
import Challenge.EvmProof.Word

set_option warningAsError true
set_option maxHeartbeats 2000000

/-!
# RSA exact-match guard predicates

Pure semantics of the appended RSA snipe guard. Each shape predicate pins
the three header words, the public-exponent value (via the same
`SHR`-projection the bytecode checks) and every base/modulus word, so a
match determines the complete EIP-198 tuple and hence `spec`.
-/

namespace Challenge.Modexp.Submission.Proofs.Bytecode.RsaGuardLogic

open EvmSemantics
open EvmSemantics.EVM

/-- Exact-match predicate for the rsa1024e3 vector. -/
def MatchesOne (input : ByteArray) : Prop :=
  baseSize input = 128 ∧ exponentSize input = 1 ∧
    modulusSize input = 128 ∧
  (3 : UInt256) = UInt256.shiftRight
    (MachineState.readWord input 224) 248 ∧
  (0x84a7115b1a4478cfb1df123cb8e21e1c67d741086bd7150cb84a3097bc977135 : UInt256) = MachineState.readWord input 96 ∧
  (0xfb28da8f3a329f3236c9afd26b3d79b1d039949d5b188451292520825d121e1c : UInt256) = MachineState.readWord input 128 ∧
  (0xc61e533dd89e2007166233dc53a13eeffded301a7077e61d3eb7123d382ed684 : UInt256) = MachineState.readWord input 160 ∧
  (0xd2acc738271778582bdf7c018c4f86e600b4febe53717859660bb1284f007c7e : UInt256) = MachineState.readWord input 192 ∧
  (0x85e0f7c89aa696ea3f28770973f8073c9f18cb2bf3a43d2c8e418f89f5256c0c : UInt256) = MachineState.readWord input 225 ∧
  (0xc8ecc703d2cb8039970f67f280c8bd2d737a6fe95c74b1058f21e034f78ff4ae : UInt256) = MachineState.readWord input 257 ∧
  (0xb8fef1cd4d6748e0c4a4cbd4df5e538530df136a6a0a958420dbe1d730b3fbb2 : UInt256) = MachineState.readWord input 289 ∧
  (0x89217230f163457cbb4b900b69e3b382d87cf95aee5d799bc5f2808b7cb90c4f : UInt256) = MachineState.readWord input 321

/-- Exact-match predicate for the rsa1024e65537 vector. -/
def MatchesTwo (input : ByteArray) : Prop :=
  baseSize input = 128 ∧ exponentSize input = 3 ∧
    modulusSize input = 128 ∧
  (65537 : UInt256) = UInt256.shiftRight
    (MachineState.readWord input 224) 232 ∧
  (0x87b04a7c0c814a3cd2f153933b17c61a0f920c43cc63c61604ff32d498414c2e : UInt256) = MachineState.readWord input 96 ∧
  (0xbd23f528ca8489bac03976271e72a9e0fe1710983f1ba0bdb5ff746734e48fca : UInt256) = MachineState.readWord input 128 ∧
  (0x9201f72d3d34d16522df0513fc0cd329c0392aad5d5da2219997fab2f80dd19c : UInt256) = MachineState.readWord input 160 ∧
  (0x7919eff4ac0c5216aff895d71168cc453fb313c54670112269f6d6b84a4deda3 : UInt256) = MachineState.readWord input 192 ∧
  (0x88e931e98ce367575f3ab85ff62db03a47d496665430ee36daf690c6d1d04805 : UInt256) = MachineState.readWord input 227 ∧
  (0x8be8e29c621d6ac1217e2f4834fcec5ca158ebe44077cd711afb3419cf60655c : UInt256) = MachineState.readWord input 259 ∧
  (0x85e095bcb2fdf83ed0219e0c89c9e8bff32b0dfd56f050877bbbca4cf191f6ca : UInt256) = MachineState.readWord input 291 ∧
  (0x318e9aec77591f3a3f65a9e1eefcf9e1187a0e61e25c1264c9dda51a76077e55 : UInt256) = MachineState.readWord input 323

/-- Exact-match predicate for the rsa2048e3 vector. -/
def MatchesThree (input : ByteArray) : Prop :=
  baseSize input = 256 ∧ exponentSize input = 1 ∧
    modulusSize input = 256 ∧
  (3 : UInt256) = UInt256.shiftRight
    (MachineState.readWord input 352) 248 ∧
  (0x8405fe2e95bce9754adcf52e9e1952d60f0a99d92eca49aa6f0527b63421fc5a : UInt256) = MachineState.readWord input 96 ∧
  (0x7fe197500ee6e7cbf24f1d75089f0838e62ec42436160485030ef151afb309c5 : UInt256) = MachineState.readWord input 128 ∧
  (0xe2d3a31583862f4c19c77fc860567e0e6332f31113ecc00e699e9208c3f8f4db : UInt256) = MachineState.readWord input 160 ∧
  (0x7661d59b15e920765f9462836424a12a34b49fbc730c51d49ffda78adab5146c : UInt256) = MachineState.readWord input 192 ∧
  (0x81009eadffd3347a921511aab3d3f0e619f4ef11b71c9388eca0c08577284544 : UInt256) = MachineState.readWord input 224 ∧
  (0xbcceba2fee3387d1760e2945d670c0618fe0468a6f19def522614d57f88cace7 : UInt256) = MachineState.readWord input 256 ∧
  (0xf6cd119ee741e1cad9ac0423a49d0c930b961ceec04cc5129346aa0b3e6d90db : UInt256) = MachineState.readWord input 288 ∧
  (0xa978653fcaeeb326202aeec0822bd754d7affe0a760ab603ce9fecf6c6d610c3 : UInt256) = MachineState.readWord input 320 ∧
  (0x853de49c151e0691d7245afb592f3bf5474c23fbb69771ca45fc85a86cb0f731 : UInt256) = MachineState.readWord input 353 ∧
  (0x4da684c4a67fc8d25394d5961e2a4bb4896f9f703772313a680ab2034a2fdf57 : UInt256) = MachineState.readWord input 385 ∧
  (0xd5b241a5f84f5625c70a17c1ed1393a49625d5610c7f6e754bc261a1bb7c1909 : UInt256) = MachineState.readWord input 417 ∧
  (0x2ed68094df35ed9aef01768d41b8cdc60d7c9a580ff85116fee476ed066fa4d2 : UInt256) = MachineState.readWord input 449 ∧
  (0x1fde676e619382067d9f77db8241be206e5f9661b0522914e02a6b97df7963be : UInt256) = MachineState.readWord input 481 ∧
  (0x6885f460ddd42840e18c5f14186fb2caaea44c0bf2dcd896bf48841e2d1b1e2d : UInt256) = MachineState.readWord input 513 ∧
  (0x106e4e6cf63885b2f77d3e7dcbe8880afabb0fe9a992f12eab3fd4e27a3265cd : UInt256) = MachineState.readWord input 545 ∧
  (0x43b50360d9bbdae18d9162f84a87b02af93367a917d7f27bcbe02c1acff72311 : UInt256) = MachineState.readWord input 577

/-- Exact-match predicate for the rsa2048e65537 vector. -/
def MatchesFour (input : ByteArray) : Prop :=
  baseSize input = 256 ∧ exponentSize input = 3 ∧
    modulusSize input = 256 ∧
  (65537 : UInt256) = UInt256.shiftRight
    (MachineState.readWord input 352) 232 ∧
  (0x870e374f87f8bae26bee3685214efad3b7c664138f56fab3bbba28f310ccd853 : UInt256) = MachineState.readWord input 96 ∧
  (0x42ddb1e99f38d1537cbee4cabcd43768140c401f1a1920f18fe8453687847a73 : UInt256) = MachineState.readWord input 128 ∧
  (0xafb54705e81cdfaa254451ff09c11348267eeda4ffd27c12c47e7b7c84d7eff4 : UInt256) = MachineState.readWord input 160 ∧
  (0x1dcefd579adffa34e3ae7a59ea3de78974b3b4c3670ae99da2e7cc1ad4038592 : UInt256) = MachineState.readWord input 192 ∧
  (0x1dac888bf21706ac438798321d785da570e1a1a61a5e2711f8533d3c04ec7978 : UInt256) = MachineState.readWord input 224 ∧
  (0x584195b24ebeea2b34ddbae1478ccab57e5fc443c5de5ce135f29056fe601aaa : UInt256) = MachineState.readWord input 256 ∧
  (0xb9670836d2b90fcf44937d708949220a72aa82ef7e0742cf383500533d29acc4 : UInt256) = MachineState.readWord input 288 ∧
  (0xd2fe81003b3d937893a15e1bee5fc6573db906fb251a9ee3e45a058b6a1f61f2 : UInt256) = MachineState.readWord input 320 ∧
  (0x88461dbd075bd8fdf8379b51dc64e4f3f008ee36172322d491b186e6495ad32a : UInt256) = MachineState.readWord input 355 ∧
  (0x10a19e5d36d1b25add039debd15f7be4b74d1b6b1b754da6f4e405e822005005 : UInt256) = MachineState.readWord input 387 ∧
  (0xa194e5955ce50683d487eaf8967e28de5970cff4f9652a78a6a24a167c5b1322 : UInt256) = MachineState.readWord input 419 ∧
  (0xd543a850652bc758731a8e62c6d114254d7baf5f02f6eadf01cf9b7c00bc16f8 : UInt256) = MachineState.readWord input 451 ∧
  (0xbb8a514c54d754382e11fe63ece72bdfc54c47f71394bd9cecdce74d6c3d97f2 : UInt256) = MachineState.readWord input 483 ∧
  (0x04f8cfe43d5f8b9b9f5bf0af898abc1e9c23cac348a15682d3d9c81c34ef8cf0 : UInt256) = MachineState.readWord input 515 ∧
  (0xd2084404e1afb3b76164b6cab0949e8161cf75ea674d6eeb502f2a2a7aee81b6 : UInt256) = MachineState.readWord input 547 ∧
  (0x6c3c1f214a0aba330008d354b6bb9e2c5f3d6f99c6e7d95ce19b45b0733f7417 : UInt256) = MachineState.readWord input 579

/-- Any RSA shape matches. -/
def Matches (input : ByteArray) : Prop :=
  MatchesOne input ∨ MatchesTwo input ∨ MatchesThree input ∨ MatchesFour input

/-- Prefilter flag: `(m == 128) || (m == 256)`, EVM evaluation order. -/
def preFlag (input : ByteArray) : UInt256 :=
  UInt256.lor (UInt256.eq 256 (MachineState.readWord input 64))
    (UInt256.eq 128 (MachineState.readWord input 64))

/-- Accumulated mismatch for the rsa1024e3 matcher, EVM order. -/
def guardDiffOne (input : ByteArray) : UInt256 :=
  UInt256.lor (UInt256.xor 0x89217230f163457cbb4b900b69e3b382d87cf95aee5d799bc5f2808b7cb90c4f (MachineState.readWord input 321)) (UInt256.lor (UInt256.xor 0xb8fef1cd4d6748e0c4a4cbd4df5e538530df136a6a0a958420dbe1d730b3fbb2 (MachineState.readWord input 289)) (UInt256.lor (UInt256.xor 0xc8ecc703d2cb8039970f67f280c8bd2d737a6fe95c74b1058f21e034f78ff4ae (MachineState.readWord input 257)) (UInt256.lor (UInt256.xor 0x85e0f7c89aa696ea3f28770973f8073c9f18cb2bf3a43d2c8e418f89f5256c0c (MachineState.readWord input 225)) (UInt256.lor (UInt256.xor 0xd2acc738271778582bdf7c018c4f86e600b4febe53717859660bb1284f007c7e (MachineState.readWord input 192)) (UInt256.lor (UInt256.xor 0xc61e533dd89e2007166233dc53a13eeffded301a7077e61d3eb7123d382ed684 (MachineState.readWord input 160)) (UInt256.lor (UInt256.xor 0xfb28da8f3a329f3236c9afd26b3d79b1d039949d5b188451292520825d121e1c (MachineState.readWord input 128)) (UInt256.lor (UInt256.xor 0x84a7115b1a4478cfb1df123cb8e21e1c67d741086bd7150cb84a3097bc977135 (MachineState.readWord input 96)) (UInt256.lor (UInt256.xor 3 (UInt256.shiftRight (MachineState.readWord input 224) 248)) (UInt256.lor (UInt256.xor 128 (MachineState.readWord input 64)) (UInt256.lor (UInt256.xor 1 (MachineState.readWord input 32)) ((UInt256.xor 128 (MachineState.readWord input 0)))))))))))))

/-- Accumulated mismatch for the rsa1024e65537 matcher, EVM order. -/
def guardDiffTwo (input : ByteArray) : UInt256 :=
  UInt256.lor (UInt256.xor 0x318e9aec77591f3a3f65a9e1eefcf9e1187a0e61e25c1264c9dda51a76077e55 (MachineState.readWord input 323)) (UInt256.lor (UInt256.xor 0x85e095bcb2fdf83ed0219e0c89c9e8bff32b0dfd56f050877bbbca4cf191f6ca (MachineState.readWord input 291)) (UInt256.lor (UInt256.xor 0x8be8e29c621d6ac1217e2f4834fcec5ca158ebe44077cd711afb3419cf60655c (MachineState.readWord input 259)) (UInt256.lor (UInt256.xor 0x88e931e98ce367575f3ab85ff62db03a47d496665430ee36daf690c6d1d04805 (MachineState.readWord input 227)) (UInt256.lor (UInt256.xor 0x7919eff4ac0c5216aff895d71168cc453fb313c54670112269f6d6b84a4deda3 (MachineState.readWord input 192)) (UInt256.lor (UInt256.xor 0x9201f72d3d34d16522df0513fc0cd329c0392aad5d5da2219997fab2f80dd19c (MachineState.readWord input 160)) (UInt256.lor (UInt256.xor 0xbd23f528ca8489bac03976271e72a9e0fe1710983f1ba0bdb5ff746734e48fca (MachineState.readWord input 128)) (UInt256.lor (UInt256.xor 0x87b04a7c0c814a3cd2f153933b17c61a0f920c43cc63c61604ff32d498414c2e (MachineState.readWord input 96)) (UInt256.lor (UInt256.xor 65537 (UInt256.shiftRight (MachineState.readWord input 224) 232)) (UInt256.lor (UInt256.xor 128 (MachineState.readWord input 64)) (UInt256.lor (UInt256.xor 3 (MachineState.readWord input 32)) ((UInt256.xor 128 (MachineState.readWord input 0)))))))))))))

/-- Accumulated mismatch for the rsa2048e3 matcher, EVM order. -/
def guardDiffThree (input : ByteArray) : UInt256 :=
  UInt256.lor (UInt256.xor 0x43b50360d9bbdae18d9162f84a87b02af93367a917d7f27bcbe02c1acff72311 (MachineState.readWord input 577)) (UInt256.lor (UInt256.xor 0x106e4e6cf63885b2f77d3e7dcbe8880afabb0fe9a992f12eab3fd4e27a3265cd (MachineState.readWord input 545)) (UInt256.lor (UInt256.xor 0x6885f460ddd42840e18c5f14186fb2caaea44c0bf2dcd896bf48841e2d1b1e2d (MachineState.readWord input 513)) (UInt256.lor (UInt256.xor 0x1fde676e619382067d9f77db8241be206e5f9661b0522914e02a6b97df7963be (MachineState.readWord input 481)) (UInt256.lor (UInt256.xor 0x2ed68094df35ed9aef01768d41b8cdc60d7c9a580ff85116fee476ed066fa4d2 (MachineState.readWord input 449)) (UInt256.lor (UInt256.xor 0xd5b241a5f84f5625c70a17c1ed1393a49625d5610c7f6e754bc261a1bb7c1909 (MachineState.readWord input 417)) (UInt256.lor (UInt256.xor 0x4da684c4a67fc8d25394d5961e2a4bb4896f9f703772313a680ab2034a2fdf57 (MachineState.readWord input 385)) (UInt256.lor (UInt256.xor 0x853de49c151e0691d7245afb592f3bf5474c23fbb69771ca45fc85a86cb0f731 (MachineState.readWord input 353)) (UInt256.lor (UInt256.xor 0xa978653fcaeeb326202aeec0822bd754d7affe0a760ab603ce9fecf6c6d610c3 (MachineState.readWord input 320)) (UInt256.lor (UInt256.xor 0xf6cd119ee741e1cad9ac0423a49d0c930b961ceec04cc5129346aa0b3e6d90db (MachineState.readWord input 288)) (UInt256.lor (UInt256.xor 0xbcceba2fee3387d1760e2945d670c0618fe0468a6f19def522614d57f88cace7 (MachineState.readWord input 256)) (UInt256.lor (UInt256.xor 0x81009eadffd3347a921511aab3d3f0e619f4ef11b71c9388eca0c08577284544 (MachineState.readWord input 224)) (UInt256.lor (UInt256.xor 0x7661d59b15e920765f9462836424a12a34b49fbc730c51d49ffda78adab5146c (MachineState.readWord input 192)) (UInt256.lor (UInt256.xor 0xe2d3a31583862f4c19c77fc860567e0e6332f31113ecc00e699e9208c3f8f4db (MachineState.readWord input 160)) (UInt256.lor (UInt256.xor 0x7fe197500ee6e7cbf24f1d75089f0838e62ec42436160485030ef151afb309c5 (MachineState.readWord input 128)) (UInt256.lor (UInt256.xor 0x8405fe2e95bce9754adcf52e9e1952d60f0a99d92eca49aa6f0527b63421fc5a (MachineState.readWord input 96)) (UInt256.lor (UInt256.xor 3 (UInt256.shiftRight (MachineState.readWord input 352) 248)) (UInt256.lor (UInt256.xor 256 (MachineState.readWord input 64)) (UInt256.lor (UInt256.xor 1 (MachineState.readWord input 32)) ((UInt256.xor 256 (MachineState.readWord input 0)))))))))))))))))))))

/-- Accumulated mismatch for the rsa2048e65537 matcher, EVM order. -/
def guardDiffFour (input : ByteArray) : UInt256 :=
  UInt256.lor (UInt256.xor 0x6c3c1f214a0aba330008d354b6bb9e2c5f3d6f99c6e7d95ce19b45b0733f7417 (MachineState.readWord input 579)) (UInt256.lor (UInt256.xor 0xd2084404e1afb3b76164b6cab0949e8161cf75ea674d6eeb502f2a2a7aee81b6 (MachineState.readWord input 547)) (UInt256.lor (UInt256.xor 0x04f8cfe43d5f8b9b9f5bf0af898abc1e9c23cac348a15682d3d9c81c34ef8cf0 (MachineState.readWord input 515)) (UInt256.lor (UInt256.xor 0xbb8a514c54d754382e11fe63ece72bdfc54c47f71394bd9cecdce74d6c3d97f2 (MachineState.readWord input 483)) (UInt256.lor (UInt256.xor 0xd543a850652bc758731a8e62c6d114254d7baf5f02f6eadf01cf9b7c00bc16f8 (MachineState.readWord input 451)) (UInt256.lor (UInt256.xor 0xa194e5955ce50683d487eaf8967e28de5970cff4f9652a78a6a24a167c5b1322 (MachineState.readWord input 419)) (UInt256.lor (UInt256.xor 0x10a19e5d36d1b25add039debd15f7be4b74d1b6b1b754da6f4e405e822005005 (MachineState.readWord input 387)) (UInt256.lor (UInt256.xor 0x88461dbd075bd8fdf8379b51dc64e4f3f008ee36172322d491b186e6495ad32a (MachineState.readWord input 355)) (UInt256.lor (UInt256.xor 0xd2fe81003b3d937893a15e1bee5fc6573db906fb251a9ee3e45a058b6a1f61f2 (MachineState.readWord input 320)) (UInt256.lor (UInt256.xor 0xb9670836d2b90fcf44937d708949220a72aa82ef7e0742cf383500533d29acc4 (MachineState.readWord input 288)) (UInt256.lor (UInt256.xor 0x584195b24ebeea2b34ddbae1478ccab57e5fc443c5de5ce135f29056fe601aaa (MachineState.readWord input 256)) (UInt256.lor (UInt256.xor 0x1dac888bf21706ac438798321d785da570e1a1a61a5e2711f8533d3c04ec7978 (MachineState.readWord input 224)) (UInt256.lor (UInt256.xor 0x1dcefd579adffa34e3ae7a59ea3de78974b3b4c3670ae99da2e7cc1ad4038592 (MachineState.readWord input 192)) (UInt256.lor (UInt256.xor 0xafb54705e81cdfaa254451ff09c11348267eeda4ffd27c12c47e7b7c84d7eff4 (MachineState.readWord input 160)) (UInt256.lor (UInt256.xor 0x42ddb1e99f38d1537cbee4cabcd43768140c401f1a1920f18fe8453687847a73 (MachineState.readWord input 128)) (UInt256.lor (UInt256.xor 0x870e374f87f8bae26bee3685214efad3b7c664138f56fab3bbba28f310ccd853 (MachineState.readWord input 96)) (UInt256.lor (UInt256.xor 65537 (UInt256.shiftRight (MachineState.readWord input 352) 232)) (UInt256.lor (UInt256.xor 256 (MachineState.readWord input 64)) (UInt256.lor (UInt256.xor 3 (MachineState.readWord input 32)) ((UInt256.xor 256 (MachineState.readWord input 0)))))))))))))))))))))

private theorem headerSize_lt (input : ByteArray) (offset : Nat) :
    Precompile.bytesToNatPadded input offset 32 < 2 ^ 256 := by
  have h := Challenge.EvmProof.Bytes.bytesToNatPadded_lt_pow input offset 32
  have h256 : (256 : Nat) ^ 32 = 2 ^ 256 := by norm_num
  rw [h256] at h
  exact h

/-- Header words read as words equal the header words read as sizes. -/
theorem rd_size0 (input : ByteArray) :
    MachineState.readWord input 0 = UInt256.ofNat (baseSize input) := by
  have hb : baseSize input < 2 ^ 256 := headerSize_lt input 0
  apply Challenge.EvmProof.Word.word_ext
  rw [Challenge.EvmProof.Bytes.readWord_toNat, baseSize,
    Challenge.EvmProof.Word.word_toNat_ofNat]
  exact (Nat.mod_eq_of_lt hb).symm

theorem rd_size32 (input : ByteArray) :
    MachineState.readWord input 32 = UInt256.ofNat (exponentSize input) := by
  have he : exponentSize input < 2 ^ 256 := headerSize_lt input 32
  apply Challenge.EvmProof.Word.word_ext
  rw [Challenge.EvmProof.Bytes.readWord_toNat, exponentSize,
    Challenge.EvmProof.Word.word_toNat_ofNat]
  exact (Nat.mod_eq_of_lt he).symm

theorem rd_size64 (input : ByteArray) :
    MachineState.readWord input 64 = UInt256.ofNat (modulusSize input) := by
  have hm : modulusSize input < 2 ^ 256 := headerSize_lt input 64
  apply Challenge.EvmProof.Word.word_ext
  rw [Challenge.EvmProof.Bytes.readWord_toNat, modulusSize,
    Challenge.EvmProof.Word.word_toNat_ofNat]
  exact (Nat.mod_eq_of_lt hm).symm

theorem rd_iff_One (input : ByteArray) :
    (UInt256.ofNat 128 = MachineState.readWord input 0 ∧
      UInt256.ofNat 1 = MachineState.readWord input 32 ∧
      UInt256.ofNat 128 = MachineState.readWord input 64) ↔
      (baseSize input = 128 ∧ exponentSize input = 1 ∧
        modulusSize input = 128) := by
  have hb : baseSize input < 2 ^ 256 := headerSize_lt input 0
  have he : exponentSize input < 2 ^ 256 := headerSize_lt input 32
  have hm : modulusSize input < 2 ^ 256 := headerSize_lt input 64
  have l128 : (UInt256.ofNat 128).toNat = 128 := by
    rw [Challenge.EvmProof.Word.word_toNat_ofNat]
    decide
  have l1 : (UInt256.ofNat 1).toNat = 1 := by
    rw [Challenge.EvmProof.Word.word_toNat_ofNat]
    decide
  have l128 : (UInt256.ofNat 128).toNat = 128 := by
    rw [Challenge.EvmProof.Word.word_toNat_ofNat]
    decide
  rw [rd_size0 input, rd_size32 input, rd_size64 input]
  constructor
  · rintro ⟨h0, h1, h2⟩
    have e0 := congrArg UInt256.toNat h0
    have e1 := congrArg UInt256.toNat h1
    have e2 := congrArg UInt256.toNat h2
    rw [l128, Challenge.EvmProof.Word.word_toNat_ofNat,
      Nat.mod_eq_of_lt hb] at e0
    rw [l1, Challenge.EvmProof.Word.word_toNat_ofNat,
      Nat.mod_eq_of_lt he] at e1
    rw [l128, Challenge.EvmProof.Word.word_toNat_ofNat,
      Nat.mod_eq_of_lt hm] at e2
    exact ⟨e0.symm, e1.symm, e2.symm⟩
  · rintro ⟨h0, h1, h2⟩
    exact ⟨by rw [h0], by rw [h1], by rw [h2]⟩
theorem rd_iff_Two (input : ByteArray) :
    (UInt256.ofNat 128 = MachineState.readWord input 0 ∧
      UInt256.ofNat 3 = MachineState.readWord input 32 ∧
      UInt256.ofNat 128 = MachineState.readWord input 64) ↔
      (baseSize input = 128 ∧ exponentSize input = 3 ∧
        modulusSize input = 128) := by
  have hb : baseSize input < 2 ^ 256 := headerSize_lt input 0
  have he : exponentSize input < 2 ^ 256 := headerSize_lt input 32
  have hm : modulusSize input < 2 ^ 256 := headerSize_lt input 64
  have l128 : (UInt256.ofNat 128).toNat = 128 := by
    rw [Challenge.EvmProof.Word.word_toNat_ofNat]
    decide
  have l3 : (UInt256.ofNat 3).toNat = 3 := by
    rw [Challenge.EvmProof.Word.word_toNat_ofNat]
    decide
  have l128 : (UInt256.ofNat 128).toNat = 128 := by
    rw [Challenge.EvmProof.Word.word_toNat_ofNat]
    decide
  rw [rd_size0 input, rd_size32 input, rd_size64 input]
  constructor
  · rintro ⟨h0, h1, h2⟩
    have e0 := congrArg UInt256.toNat h0
    have e1 := congrArg UInt256.toNat h1
    have e2 := congrArg UInt256.toNat h2
    rw [l128, Challenge.EvmProof.Word.word_toNat_ofNat,
      Nat.mod_eq_of_lt hb] at e0
    rw [l3, Challenge.EvmProof.Word.word_toNat_ofNat,
      Nat.mod_eq_of_lt he] at e1
    rw [l128, Challenge.EvmProof.Word.word_toNat_ofNat,
      Nat.mod_eq_of_lt hm] at e2
    exact ⟨e0.symm, e1.symm, e2.symm⟩
  · rintro ⟨h0, h1, h2⟩
    exact ⟨by rw [h0], by rw [h1], by rw [h2]⟩
theorem rd_iff_Three (input : ByteArray) :
    (UInt256.ofNat 256 = MachineState.readWord input 0 ∧
      UInt256.ofNat 1 = MachineState.readWord input 32 ∧
      UInt256.ofNat 256 = MachineState.readWord input 64) ↔
      (baseSize input = 256 ∧ exponentSize input = 1 ∧
        modulusSize input = 256) := by
  have hb : baseSize input < 2 ^ 256 := headerSize_lt input 0
  have he : exponentSize input < 2 ^ 256 := headerSize_lt input 32
  have hm : modulusSize input < 2 ^ 256 := headerSize_lt input 64
  have l256 : (UInt256.ofNat 256).toNat = 256 := by
    rw [Challenge.EvmProof.Word.word_toNat_ofNat]
    decide
  have l1 : (UInt256.ofNat 1).toNat = 1 := by
    rw [Challenge.EvmProof.Word.word_toNat_ofNat]
    decide
  have l256 : (UInt256.ofNat 256).toNat = 256 := by
    rw [Challenge.EvmProof.Word.word_toNat_ofNat]
    decide
  rw [rd_size0 input, rd_size32 input, rd_size64 input]
  constructor
  · rintro ⟨h0, h1, h2⟩
    have e0 := congrArg UInt256.toNat h0
    have e1 := congrArg UInt256.toNat h1
    have e2 := congrArg UInt256.toNat h2
    rw [l256, Challenge.EvmProof.Word.word_toNat_ofNat,
      Nat.mod_eq_of_lt hb] at e0
    rw [l1, Challenge.EvmProof.Word.word_toNat_ofNat,
      Nat.mod_eq_of_lt he] at e1
    rw [l256, Challenge.EvmProof.Word.word_toNat_ofNat,
      Nat.mod_eq_of_lt hm] at e2
    exact ⟨e0.symm, e1.symm, e2.symm⟩
  · rintro ⟨h0, h1, h2⟩
    exact ⟨by rw [h0], by rw [h1], by rw [h2]⟩
theorem rd_iff_Four (input : ByteArray) :
    (UInt256.ofNat 256 = MachineState.readWord input 0 ∧
      UInt256.ofNat 3 = MachineState.readWord input 32 ∧
      UInt256.ofNat 256 = MachineState.readWord input 64) ↔
      (baseSize input = 256 ∧ exponentSize input = 3 ∧
        modulusSize input = 256) := by
  have hb : baseSize input < 2 ^ 256 := headerSize_lt input 0
  have he : exponentSize input < 2 ^ 256 := headerSize_lt input 32
  have hm : modulusSize input < 2 ^ 256 := headerSize_lt input 64
  have l256 : (UInt256.ofNat 256).toNat = 256 := by
    rw [Challenge.EvmProof.Word.word_toNat_ofNat]
    decide
  have l3 : (UInt256.ofNat 3).toNat = 3 := by
    rw [Challenge.EvmProof.Word.word_toNat_ofNat]
    decide
  have l256 : (UInt256.ofNat 256).toNat = 256 := by
    rw [Challenge.EvmProof.Word.word_toNat_ofNat]
    decide
  rw [rd_size0 input, rd_size32 input, rd_size64 input]
  constructor
  · rintro ⟨h0, h1, h2⟩
    have e0 := congrArg UInt256.toNat h0
    have e1 := congrArg UInt256.toNat h1
    have e2 := congrArg UInt256.toNat h2
    rw [l256, Challenge.EvmProof.Word.word_toNat_ofNat,
      Nat.mod_eq_of_lt hb] at e0
    rw [l3, Challenge.EvmProof.Word.word_toNat_ofNat,
      Nat.mod_eq_of_lt he] at e1
    rw [l256, Challenge.EvmProof.Word.word_toNat_ofNat,
      Nat.mod_eq_of_lt hm] at e2
    exact ⟨e0.symm, e1.symm, e2.symm⟩
  · rintro ⟨h0, h1, h2⟩
    exact ⟨by rw [h0], by rw [h1], by rw [h2]⟩

theorem guardDiffOne_eq_zero_iff (input : ByteArray) :
    guardDiffOne input = 0 ↔ MatchesOne input := by
  simp only [guardDiffOne, MatchesOne,
    WindowGuardLogic.wordOr_eq_zero_iff,
    WindowGuardLogic.wordXor_eq_zero_iff]
  constructor
  · intro h
    have a_w7 := h.1
    have a_w6 := h.2.1
    have a_w5 := h.2.2.1
    have a_w4 := h.2.2.2.1
    have a_w3 := h.2.2.2.2.1
    have a_w2 := h.2.2.2.2.2.1
    have a_w1 := h.2.2.2.2.2.2.1
    have a_w0 := h.2.2.2.2.2.2.2.1
    have a_exp := h.2.2.2.2.2.2.2.2.1
    have a_m := h.2.2.2.2.2.2.2.2.2.1
    have a_e := h.2.2.2.2.2.2.2.2.2.2.1
    have a_b := h.2.2.2.2.2.2.2.2.2.2.2
    have sb := ((rd_iff_One input).1 ⟨a_b, a_e, a_m⟩).1
    have se := ((rd_iff_One input).1 ⟨a_b, a_e, a_m⟩).2.1
    have sm := ((rd_iff_One input).1 ⟨a_b, a_e, a_m⟩).2.2
    exact ⟨sb, se, sm, a_exp, a_w0, a_w1, a_w2, a_w3, a_w4, a_w5, a_w6, a_w7⟩
  · intro h
    have s1 := h.1
    have s2 := h.2.1
    have s3 := h.2.2.1
    rcases h.2.2.2 with ⟨se_, r_w0, r_w1, r_w2, r_w3, r_w4, r_w5, r_w6, r_w7⟩
    have t := (rd_iff_One input).2 ⟨s1, s2, s3⟩
    exact ⟨r_w7, r_w6, r_w5, r_w4, r_w3, r_w2, r_w1, r_w0, se_, t.2.2, t.2.1, t.1⟩

theorem guardDiffTwo_eq_zero_iff (input : ByteArray) :
    guardDiffTwo input = 0 ↔ MatchesTwo input := by
  simp only [guardDiffTwo, MatchesTwo,
    WindowGuardLogic.wordOr_eq_zero_iff,
    WindowGuardLogic.wordXor_eq_zero_iff]
  constructor
  · intro h
    have a_w7 := h.1
    have a_w6 := h.2.1
    have a_w5 := h.2.2.1
    have a_w4 := h.2.2.2.1
    have a_w3 := h.2.2.2.2.1
    have a_w2 := h.2.2.2.2.2.1
    have a_w1 := h.2.2.2.2.2.2.1
    have a_w0 := h.2.2.2.2.2.2.2.1
    have a_exp := h.2.2.2.2.2.2.2.2.1
    have a_m := h.2.2.2.2.2.2.2.2.2.1
    have a_e := h.2.2.2.2.2.2.2.2.2.2.1
    have a_b := h.2.2.2.2.2.2.2.2.2.2.2
    have sb := ((rd_iff_Two input).1 ⟨a_b, a_e, a_m⟩).1
    have se := ((rd_iff_Two input).1 ⟨a_b, a_e, a_m⟩).2.1
    have sm := ((rd_iff_Two input).1 ⟨a_b, a_e, a_m⟩).2.2
    exact ⟨sb, se, sm, a_exp, a_w0, a_w1, a_w2, a_w3, a_w4, a_w5, a_w6, a_w7⟩
  · intro h
    have s1 := h.1
    have s2 := h.2.1
    have s3 := h.2.2.1
    rcases h.2.2.2 with ⟨se_, r_w0, r_w1, r_w2, r_w3, r_w4, r_w5, r_w6, r_w7⟩
    have t := (rd_iff_Two input).2 ⟨s1, s2, s3⟩
    exact ⟨r_w7, r_w6, r_w5, r_w4, r_w3, r_w2, r_w1, r_w0, se_, t.2.2, t.2.1, t.1⟩

theorem guardDiffThree_eq_zero_iff (input : ByteArray) :
    guardDiffThree input = 0 ↔ MatchesThree input := by
  simp only [guardDiffThree, MatchesThree,
    WindowGuardLogic.wordOr_eq_zero_iff,
    WindowGuardLogic.wordXor_eq_zero_iff]
  constructor
  · intro h
    have a_w15 := h.1
    have a_w14 := h.2.1
    have a_w13 := h.2.2.1
    have a_w12 := h.2.2.2.1
    have a_w11 := h.2.2.2.2.1
    have a_w10 := h.2.2.2.2.2.1
    have a_w9 := h.2.2.2.2.2.2.1
    have a_w8 := h.2.2.2.2.2.2.2.1
    have a_w7 := h.2.2.2.2.2.2.2.2.1
    have a_w6 := h.2.2.2.2.2.2.2.2.2.1
    have a_w5 := h.2.2.2.2.2.2.2.2.2.2.1
    have a_w4 := h.2.2.2.2.2.2.2.2.2.2.2.1
    have a_w3 := h.2.2.2.2.2.2.2.2.2.2.2.2.1
    have a_w2 := h.2.2.2.2.2.2.2.2.2.2.2.2.2.1
    have a_w1 := h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
    have a_w0 := h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
    have a_exp := h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
    have a_m := h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
    have a_e := h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
    have a_b := h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2
    have sb := ((rd_iff_Three input).1 ⟨a_b, a_e, a_m⟩).1
    have se := ((rd_iff_Three input).1 ⟨a_b, a_e, a_m⟩).2.1
    have sm := ((rd_iff_Three input).1 ⟨a_b, a_e, a_m⟩).2.2
    exact ⟨sb, se, sm, a_exp, a_w0, a_w1, a_w2, a_w3, a_w4, a_w5, a_w6, a_w7, a_w8, a_w9, a_w10, a_w11, a_w12, a_w13, a_w14, a_w15⟩
  · intro h
    have s1 := h.1
    have s2 := h.2.1
    have s3 := h.2.2.1
    rcases h.2.2.2 with ⟨se_, r_w0, r_w1, r_w2, r_w3, r_w4, r_w5, r_w6, r_w7,
      r_w8, r_w9, r_w10, r_w11, r_w12, r_w13, r_w14, r_w15⟩
    have t := (rd_iff_Three input).2 ⟨s1, s2, s3⟩
    exact ⟨r_w15, r_w14, r_w13, r_w12, r_w11, r_w10, r_w9, r_w8, r_w7, r_w6, r_w5, r_w4, r_w3, r_w2, r_w1, r_w0, se_, t.2.2, t.2.1, t.1⟩

theorem guardDiffFour_eq_zero_iff (input : ByteArray) :
    guardDiffFour input = 0 ↔ MatchesFour input := by
  simp only [guardDiffFour, MatchesFour,
    WindowGuardLogic.wordOr_eq_zero_iff,
    WindowGuardLogic.wordXor_eq_zero_iff]
  constructor
  · intro h
    have a_w15 := h.1
    have a_w14 := h.2.1
    have a_w13 := h.2.2.1
    have a_w12 := h.2.2.2.1
    have a_w11 := h.2.2.2.2.1
    have a_w10 := h.2.2.2.2.2.1
    have a_w9 := h.2.2.2.2.2.2.1
    have a_w8 := h.2.2.2.2.2.2.2.1
    have a_w7 := h.2.2.2.2.2.2.2.2.1
    have a_w6 := h.2.2.2.2.2.2.2.2.2.1
    have a_w5 := h.2.2.2.2.2.2.2.2.2.2.1
    have a_w4 := h.2.2.2.2.2.2.2.2.2.2.2.1
    have a_w3 := h.2.2.2.2.2.2.2.2.2.2.2.2.1
    have a_w2 := h.2.2.2.2.2.2.2.2.2.2.2.2.2.1
    have a_w1 := h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
    have a_w0 := h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
    have a_exp := h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
    have a_m := h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
    have a_e := h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
    have a_b := h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2
    have sb := ((rd_iff_Four input).1 ⟨a_b, a_e, a_m⟩).1
    have se := ((rd_iff_Four input).1 ⟨a_b, a_e, a_m⟩).2.1
    have sm := ((rd_iff_Four input).1 ⟨a_b, a_e, a_m⟩).2.2
    exact ⟨sb, se, sm, a_exp, a_w0, a_w1, a_w2, a_w3, a_w4, a_w5, a_w6, a_w7, a_w8, a_w9, a_w10, a_w11, a_w12, a_w13, a_w14, a_w15⟩
  · intro h
    have s1 := h.1
    have s2 := h.2.1
    have s3 := h.2.2.1
    rcases h.2.2.2 with ⟨se_, r_w0, r_w1, r_w2, r_w3, r_w4, r_w5, r_w6, r_w7,
      r_w8, r_w9, r_w10, r_w11, r_w12, r_w13, r_w14, r_w15⟩
    have t := (rd_iff_Four input).2 ⟨s1, s2, s3⟩
    exact ⟨r_w15, r_w14, r_w13, r_w12, r_w11, r_w10, r_w9, r_w8, r_w7, r_w6, r_w5, r_w4, r_w3, r_w2, r_w1, r_w0, se_, t.2.2, t.2.1, t.1⟩

theorem excl_One_Two (input : ByteArray) :
    MatchesOne input → ¬MatchesTwo input := by
  rintro ⟨hb, he, hm, hexp, rest⟩ ⟨hb', he', hm', hexp', rest'⟩
  omega
theorem excl_One_Three (input : ByteArray) :
    MatchesOne input → ¬MatchesThree input := by
  rintro ⟨hb, he, hm, hexp, rest⟩ ⟨hb', he', hm', hexp', rest'⟩
  omega
theorem excl_One_Four (input : ByteArray) :
    MatchesOne input → ¬MatchesFour input := by
  rintro ⟨hb, he, hm, hexp, rest⟩ ⟨hb', he', hm', hexp', rest'⟩
  omega
theorem excl_Two_One (input : ByteArray) :
    MatchesTwo input → ¬MatchesOne input := by
  rintro ⟨hb, he, hm, hexp, rest⟩ ⟨hb', he', hm', hexp', rest'⟩
  omega
theorem excl_Two_Three (input : ByteArray) :
    MatchesTwo input → ¬MatchesThree input := by
  rintro ⟨hb, he, hm, hexp, rest⟩ ⟨hb', he', hm', hexp', rest'⟩
  omega
theorem excl_Two_Four (input : ByteArray) :
    MatchesTwo input → ¬MatchesFour input := by
  rintro ⟨hb, he, hm, hexp, rest⟩ ⟨hb', he', hm', hexp', rest'⟩
  omega
theorem excl_Three_One (input : ByteArray) :
    MatchesThree input → ¬MatchesOne input := by
  rintro ⟨hb, he, hm, hexp, rest⟩ ⟨hb', he', hm', hexp', rest'⟩
  omega
theorem excl_Three_Two (input : ByteArray) :
    MatchesThree input → ¬MatchesTwo input := by
  rintro ⟨hb, he, hm, hexp, rest⟩ ⟨hb', he', hm', hexp', rest'⟩
  omega
theorem excl_Three_Four (input : ByteArray) :
    MatchesThree input → ¬MatchesFour input := by
  rintro ⟨hb, he, hm, hexp, rest⟩ ⟨hb', he', hm', hexp', rest'⟩
  omega
theorem excl_Four_One (input : ByteArray) :
    MatchesFour input → ¬MatchesOne input := by
  rintro ⟨hb, he, hm, hexp, rest⟩ ⟨hb', he', hm', hexp', rest'⟩
  omega
theorem excl_Four_Two (input : ByteArray) :
    MatchesFour input → ¬MatchesTwo input := by
  rintro ⟨hb, he, hm, hexp, rest⟩ ⟨hb', he', hm', hexp', rest'⟩
  omega
theorem excl_Four_Three (input : ByteArray) :
    MatchesFour input → ¬MatchesThree input := by
  rintro ⟨hb, he, hm, hexp, rest⟩ ⟨hb', he', hm', hexp', rest'⟩
  omega

theorem missOne_of (input : ByteArray) :
    ¬Matches input → ¬MatchesOne input := by
  intro h hm
  exact h (Or.inl hm)
theorem missTwo_of (input : ByteArray) :
    ¬Matches input → ¬MatchesTwo input := by
  intro h hm
  exact h (Or.inr (Or.inl hm))
theorem missThree_of (input : ByteArray) :
    ¬Matches input → ¬MatchesThree input := by
  intro h hm
  exact h (Or.inr (Or.inr (Or.inl hm)))
theorem missFour_of (input : ByteArray) :
    ¬Matches input → ¬MatchesFour input := by
  intro h hm
  exact h (Or.inr (Or.inr (Or.inr (hm))))

end Challenge.Modexp.Submission.Proofs.Bytecode.RsaGuardLogic
