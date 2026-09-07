import Challenge.Ripemd160.Submission.Proofs.Bytecode.PatternedInputData

set_option warningAsError true
set_option maxRecDepth 100000
set_option maxHeartbeats 20000000

/-!
# The thirty-two words of the patterned scoring vector

`CALLDATALOAD` reads thirty-two bytes at a time, so the guard compares the
1000-byte vector as thirty-one whole words plus a final word whose low
twenty-four bytes are the zero padding `CALLDATALOAD` supplies past the end of
the calldata.
-/

namespace Challenge.Ripemd160.Submission.Proofs.Bytecode.PatternedWordData

open EvmSemantics
open EvmSemantics.EVM
open PatternedInputData

/-- Byte `i` of the vector, zero past its end. -/
def paddedByte (i : Nat) : UInt8 := if i < 1000 then expectedByte i else 0

/-- Word `j` as a natural number, most significant byte first. -/
def patternedWordNat (j : Nat) : Nat :=
  (List.range 32).foldl (fun acc k => acc * 256 + (paddedByte (32 * j + k)).toNat) 0

def expectedWordAt (j : Nat) : UInt256 := UInt256.ofNat (patternedWordNat j)

theorem patternedWordNat_0 : patternedWordNat 0 = 0x072c51769bc0e50a2f54799ec3e80d32577ca1c6eb10355a7fa4c9ee13385d82 := by decide

@[simp] theorem expectedWordAt_0 :
    expectedWordAt 0 = (0x072c51769bc0e50a2f54799ec3e80d32577ca1c6eb10355a7fa4c9ee13385d82 : UInt256) := by
  rw [expectedWordAt, patternedWordNat_0]
  rfl

theorem patternedWordNat_1 : patternedWordNat 1 = 0xa7ccf1163b6085aacff4193e6388add2f71c41668bb0d5fa1f44698eb3d8fd22 := by decide

@[simp] theorem expectedWordAt_1 :
    expectedWordAt 1 = (0xa7ccf1163b6085aacff4193e6388add2f71c41668bb0d5fa1f44698eb3d8fd22 : UInt256) := by
  rw [expectedWordAt, patternedWordNat_1]
  rfl

theorem patternedWordNat_2 : patternedWordNat 2 = 0x476c91b6db00254a6f94b9de03284d7297bce1062b50759abfe4092e53789dc2 := by decide

@[simp] theorem expectedWordAt_2 :
    expectedWordAt 2 = (0x476c91b6db00254a6f94b9de03284d7297bce1062b50759abfe4092e53789dc2 : UInt256) := by
  rw [expectedWordAt, patternedWordNat_2]
  rfl

theorem patternedWordNat_3 : patternedWordNat 3 = 0xe70c31567ba0c5ea0f34597ea3c8ed12375c81a6cbf0153a5f84a9cef3183d62 := by decide

@[simp] theorem expectedWordAt_3 :
    expectedWordAt 3 = (0xe70c31567ba0c5ea0f34597ea3c8ed12375c81a6cbf0153a5f84a9cef3183d62 : UInt256) := by
  rw [expectedWordAt, patternedWordNat_3]
  rfl

theorem patternedWordNat_4 : patternedWordNat 4 = 0x87acd1f61b40658aafd4f91e43688db2d7fc21466b90b5daff24496e93b8dd02 := by decide

@[simp] theorem expectedWordAt_4 :
    expectedWordAt 4 = (0x87acd1f61b40658aafd4f91e43688db2d7fc21466b90b5daff24496e93b8dd02 : UInt256) := by
  rw [expectedWordAt, patternedWordNat_4]
  rfl

theorem patternedWordNat_5 : patternedWordNat 5 = 0x274c7196bbe0052a4f7499bee3082d52779cc1e60b30557a9fc4e90e33587da2 := by decide

@[simp] theorem expectedWordAt_5 :
    expectedWordAt 5 = (0x274c7196bbe0052a4f7499bee3082d52779cc1e60b30557a9fc4e90e33587da2 : UInt256) := by
  rw [expectedWordAt, patternedWordNat_5]
  rfl

theorem patternedWordNat_6 : patternedWordNat 6 = 0xc7ec11365b80a5caef14395e83a8cdf2173c6186abd0f51a3f6489aed3f81d42 := by decide

@[simp] theorem expectedWordAt_6 :
    expectedWordAt 6 = (0xc7ec11365b80a5caef14395e83a8cdf2173c6186abd0f51a3f6489aed3f81d42 : UInt256) := by
  rw [expectedWordAt, patternedWordNat_6]
  rfl

theorem patternedWordNat_7 : patternedWordNat 7 = 0x678cb1d6fb20456a8fb4d9fe23486d92b7dc01264b7095badf0429597ea3c8ed := by decide

@[simp] theorem expectedWordAt_7 :
    expectedWordAt 7 = (0x678cb1d6fb20456a8fb4d9fe23486d92b7dc01264b7095badf0429597ea3c8ed : UInt256) := by
  rw [expectedWordAt, patternedWordNat_7]
  rfl

theorem patternedWordNat_8 : patternedWordNat 8 = 0x12375c81a6cbf0153a5f84a9cef3183d6287acd1f61b40658aafd4f91e43688d := by decide

@[simp] theorem expectedWordAt_8 :
    expectedWordAt 8 = (0x12375c81a6cbf0153a5f84a9cef3183d6287acd1f61b40658aafd4f91e43688d : UInt256) := by
  rw [expectedWordAt, patternedWordNat_8]
  rfl

theorem patternedWordNat_9 : patternedWordNat 9 = 0xb2d7fc21466b90b5daff24496e93b8dd02274c7196bbe0052a4f7499bee3082d := by decide

@[simp] theorem expectedWordAt_9 :
    expectedWordAt 9 = (0xb2d7fc21466b90b5daff24496e93b8dd02274c7196bbe0052a4f7499bee3082d : UInt256) := by
  rw [expectedWordAt, patternedWordNat_9]
  rfl

theorem patternedWordNat_10 : patternedWordNat 10 = 0x52779cc1e60b30557a9fc4e90e33587da2c7ec11365b80a5caef14395e83a8cd := by decide

@[simp] theorem expectedWordAt_10 :
    expectedWordAt 10 = (0x52779cc1e60b30557a9fc4e90e33587da2c7ec11365b80a5caef14395e83a8cd : UInt256) := by
  rw [expectedWordAt, patternedWordNat_10]
  rfl

theorem patternedWordNat_11 : patternedWordNat 11 = 0xf2173c6186abd0f51a3f6489aed3f81d42678cb1d6fb20456a8fb4d9fe23486d := by decide

@[simp] theorem expectedWordAt_11 :
    expectedWordAt 11 = (0xf2173c6186abd0f51a3f6489aed3f81d42678cb1d6fb20456a8fb4d9fe23486d : UInt256) := by
  rw [expectedWordAt, patternedWordNat_11]
  rfl

theorem patternedWordNat_12 : patternedWordNat 12 = 0x92b7dc01264b7095badf04294e7398bde2072c51769bc0e50a2f54799ec3e80d := by decide

@[simp] theorem expectedWordAt_12 :
    expectedWordAt 12 = (0x92b7dc01264b7095badf04294e7398bde2072c51769bc0e50a2f54799ec3e80d : UInt256) := by
  rw [expectedWordAt, patternedWordNat_12]
  rfl

theorem patternedWordNat_13 : patternedWordNat 13 = 0x32577ca1c6eb10355a7fa4c9ee13385d82a7ccf1163b6085aacff4193e6388ad := by decide

@[simp] theorem expectedWordAt_13 :
    expectedWordAt 13 = (0x32577ca1c6eb10355a7fa4c9ee13385d82a7ccf1163b6085aacff4193e6388ad : UInt256) := by
  rw [expectedWordAt, patternedWordNat_13]
  rfl

theorem patternedWordNat_14 : patternedWordNat 14 = 0xd2f71c41668bb0d5fa1f44698eb3d8fd22476c91b6db00254a6f94b9de03284d := by decide

@[simp] theorem expectedWordAt_14 :
    expectedWordAt 14 = (0xd2f71c41668bb0d5fa1f44698eb3d8fd22476c91b6db00254a6f94b9de03284d : UInt256) := by
  rw [expectedWordAt, patternedWordNat_14]
  rfl

theorem patternedWordNat_15 : patternedWordNat 15 = 0x7297bce1062b50759abfe4092e53789dc2e70c31567babd0f51a3f6489aed3f8 := by decide

@[simp] theorem expectedWordAt_15 :
    expectedWordAt 15 = (0x7297bce1062b50759abfe4092e53789dc2e70c31567babd0f51a3f6489aed3f8 : UInt256) := by
  rw [expectedWordAt, patternedWordNat_15]
  rfl

theorem patternedWordNat_16 : patternedWordNat 16 = 0x1d42678cb1d6fb20456a8fb4d9fe23486d92b7dc01264b7095badf04294e7398 := by decide

@[simp] theorem expectedWordAt_16 :
    expectedWordAt 16 = (0x1d42678cb1d6fb20456a8fb4d9fe23486d92b7dc01264b7095badf04294e7398 : UInt256) := by
  rw [expectedWordAt, patternedWordNat_16]
  rfl

theorem patternedWordNat_17 : patternedWordNat 17 = 0xbde2072c51769bc0e50a2f54799ec3e80d32577ca1c6eb10355a7fa4c9ee1338 := by decide

@[simp] theorem expectedWordAt_17 :
    expectedWordAt 17 = (0xbde2072c51769bc0e50a2f54799ec3e80d32577ca1c6eb10355a7fa4c9ee1338 : UInt256) := by
  rw [expectedWordAt, patternedWordNat_17]
  rfl

theorem patternedWordNat_18 : patternedWordNat 18 = 0x5d82a7ccf1163b6085aacff4193e6388add2f71c41668bb0d5fa1f44698eb3d8 := by decide

@[simp] theorem expectedWordAt_18 :
    expectedWordAt 18 = (0x5d82a7ccf1163b6085aacff4193e6388add2f71c41668bb0d5fa1f44698eb3d8 : UInt256) := by
  rw [expectedWordAt, patternedWordNat_18]
  rfl

theorem patternedWordNat_19 : patternedWordNat 19 = 0xfd22476c91b6db00254a6f94b9de03284d7297bce1062b50759abfe4092e5378 := by decide

@[simp] theorem expectedWordAt_19 :
    expectedWordAt 19 = (0xfd22476c91b6db00254a6f94b9de03284d7297bce1062b50759abfe4092e5378 : UInt256) := by
  rw [expectedWordAt, patternedWordNat_19]
  rfl

theorem patternedWordNat_20 : patternedWordNat 20 = 0x9dc2e70c31567ba0c5ea0f34597ea3c8ed12375c81a6cbf0153a5f84a9cef318 := by decide

@[simp] theorem expectedWordAt_20 :
    expectedWordAt 20 = (0x9dc2e70c31567ba0c5ea0f34597ea3c8ed12375c81a6cbf0153a5f84a9cef318 : UInt256) := by
  rw [expectedWordAt, patternedWordNat_20]
  rfl

theorem patternedWordNat_21 : patternedWordNat 21 = 0x3d6287acd1f61b40658aafd4f91e43688db2d7fc21466b90b5daff24496e93b8 := by decide

@[simp] theorem expectedWordAt_21 :
    expectedWordAt 21 = (0x3d6287acd1f61b40658aafd4f91e43688db2d7fc21466b90b5daff24496e93b8 : UInt256) := by
  rw [expectedWordAt, patternedWordNat_21]
  rfl

theorem patternedWordNat_22 : patternedWordNat 22 = 0xdd02274c7196bbe0052a4f7499bee3082d52779cc1e60b30557a9fc4e90e3358 := by decide

@[simp] theorem expectedWordAt_22 :
    expectedWordAt 22 = (0xdd02274c7196bbe0052a4f7499bee3082d52779cc1e60b30557a9fc4e90e3358 : UInt256) := by
  rw [expectedWordAt, patternedWordNat_22]
  rfl

theorem patternedWordNat_23 : patternedWordNat 23 = 0x7da2c7ec11365b80a5caef14395e83a8cdfd22476c91b6db00254a6f94b9de03 := by decide

@[simp] theorem expectedWordAt_23 :
    expectedWordAt 23 = (0x7da2c7ec11365b80a5caef14395e83a8cdfd22476c91b6db00254a6f94b9de03 : UInt256) := by
  rw [expectedWordAt, patternedWordNat_23]
  rfl

theorem patternedWordNat_24 : patternedWordNat 24 = 0x284d7297bce1062b50759abfe4092e53789dc2e70c31567ba0c5ea0f34597ea3 := by decide

@[simp] theorem expectedWordAt_24 :
    expectedWordAt 24 = (0x284d7297bce1062b50759abfe4092e53789dc2e70c31567ba0c5ea0f34597ea3 : UInt256) := by
  rw [expectedWordAt, patternedWordNat_24]
  rfl

theorem patternedWordNat_25 : patternedWordNat 25 = 0xc8ed12375c81a6cbf0153a5f84a9cef3183d6287acd1f61b40658aafd4f91e43 := by decide

@[simp] theorem expectedWordAt_25 :
    expectedWordAt 25 = (0xc8ed12375c81a6cbf0153a5f84a9cef3183d6287acd1f61b40658aafd4f91e43 : UInt256) := by
  rw [expectedWordAt, patternedWordNat_25]
  rfl

theorem patternedWordNat_26 : patternedWordNat 26 = 0x688db2d7fc21466b90b5daff24496e93b8dd02274c7196bbe0052a4f7499bee3 := by decide

@[simp] theorem expectedWordAt_26 :
    expectedWordAt 26 = (0x688db2d7fc21466b90b5daff24496e93b8dd02274c7196bbe0052a4f7499bee3 : UInt256) := by
  rw [expectedWordAt, patternedWordNat_26]
  rfl

theorem patternedWordNat_27 : patternedWordNat 27 = 0x082d52779cc1e60b30557a9fc4e90e33587da2c7ec11365b80a5caef14395e83 := by decide

@[simp] theorem expectedWordAt_27 :
    expectedWordAt 27 = (0x082d52779cc1e60b30557a9fc4e90e33587da2c7ec11365b80a5caef14395e83 : UInt256) := by
  rw [expectedWordAt, patternedWordNat_27]
  rfl

theorem patternedWordNat_28 : patternedWordNat 28 = 0xa8cdf2173c6186abd0f51a3f6489aed3f81d42678cb1d6fb20456a8fb4d9fe23 := by decide

@[simp] theorem expectedWordAt_28 :
    expectedWordAt 28 = (0xa8cdf2173c6186abd0f51a3f6489aed3f81d42678cb1d6fb20456a8fb4d9fe23 : UInt256) := by
  rw [expectedWordAt, patternedWordNat_28]
  rfl

theorem patternedWordNat_29 : patternedWordNat 29 = 0x486d92b7dc01264b7095badf04294e7398bde2072c51769bc0e50a2f54799ec3 := by decide

@[simp] theorem expectedWordAt_29 :
    expectedWordAt 29 = (0x486d92b7dc01264b7095badf04294e7398bde2072c51769bc0e50a2f54799ec3 : UInt256) := by
  rw [expectedWordAt, patternedWordNat_29]
  rfl

theorem patternedWordNat_30 : patternedWordNat 30 = 0xe80d32577ca1c6eb10355a7fa4c9ee13385d82a7ccf1163b6085aacff4193e63 := by decide

@[simp] theorem expectedWordAt_30 :
    expectedWordAt 30 = (0xe80d32577ca1c6eb10355a7fa4c9ee13385d82a7ccf1163b6085aacff4193e63 : UInt256) := by
  rw [expectedWordAt, patternedWordNat_30]
  rfl

theorem patternedWordNat_31 : patternedWordNat 31 = 0x88add2f71c41668b000000000000000000000000000000000000000000000000 := by decide

@[simp] theorem expectedWordAt_31 :
    expectedWordAt 31 = (0x88add2f71c41668b000000000000000000000000000000000000000000000000 : UInt256) := by
  rw [expectedWordAt, patternedWordNat_31]
  rfl

end Challenge.Ripemd160.Submission.Proofs.Bytecode.PatternedWordData
