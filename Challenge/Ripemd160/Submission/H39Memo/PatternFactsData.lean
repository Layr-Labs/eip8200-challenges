import Challenge.Ripemd160.Submission.H39Memo.InputData

set_option warningAsError true
set_option maxRecDepth 40000
set_option maxHeartbeats 2000000

namespace Challenge.Ripemd160.Submission.H39Memo.PatternFacts

open EvmSemantics

def targetIndex (p : Fin 14) : Fin 17 := ⟨p.val + 2, by omega⟩
def target (p : Fin 14) : ByteArray := input (targetIndex p)

def sizes : List Nat := [1, 31, 32, 55, 56, 63, 64, 65, 119, 120, 128, 256, 376, 1000]

def size (p : Fin 14) : Nat :=
  match p.val with
  | 0 => 1
  | 1 => 31
  | 2 => 32
  | 3 => 55
  | 4 => 56
  | 5 => 63
  | 6 => 64
  | 7 => 65
  | 8 => 119
  | 9 => 120
  | 10 => 128
  | 11 => 256
  | 12 => 376
  | _ => 1000

theorem target_size (p : Fin 14) : (target p).size = size p := by
  fin_cases p <;> rfl

theorem size_eq_list (p : Fin 14) : size p = sizes[p.val]'(by
    change p.val < 14
    exact p.isLt) := by
  fin_cases p <;> rfl

theorem target_size_le (p : Fin 14) : (target p).size ≤ 1000 := by
  fin_cases p <;> decide

/-- Exact frozen PUSH32 immediates for the 31 shared full words. -/
def prefixWord (k : Fin 31) : UInt256 :=
  match k.val with
  | 0 => 0x072c51769bc0e50a2f54799ec3e80d32577ca1c6eb10355a7fa4c9ee13385d82
  | 1 => 0xa7ccf1163b6085aacff4193e6388add2f71c41668bb0d5fa1f44698eb3d8fd22
  | 2 => 0x476c91b6db00254a6f94b9de03284d7297bce1062b50759abfe4092e53789dc2
  | 3 => 0xe70c31567ba0c5ea0f34597ea3c8ed12375c81a6cbf0153a5f84a9cef3183d62
  | 4 => 0x87acd1f61b40658aafd4f91e43688db2d7fc21466b90b5daff24496e93b8dd02
  | 5 => 0x274c7196bbe0052a4f7499bee3082d52779cc1e60b30557a9fc4e90e33587da2
  | 6 => 0xc7ec11365b80a5caef14395e83a8cdf2173c6186abd0f51a3f6489aed3f81d42
  | 7 => 0x678cb1d6fb20456a8fb4d9fe23486d92b7dc01264b7095badf0429597ea3c8ed
  | 8 => 0x12375c81a6cbf0153a5f84a9cef3183d6287acd1f61b40658aafd4f91e43688d
  | 9 => 0xb2d7fc21466b90b5daff24496e93b8dd02274c7196bbe0052a4f7499bee3082d
  | 10 => 0x52779cc1e60b30557a9fc4e90e33587da2c7ec11365b80a5caef14395e83a8cd
  | 11 => 0xf2173c6186abd0f51a3f6489aed3f81d42678cb1d6fb20456a8fb4d9fe23486d
  | 12 => 0x92b7dc01264b7095badf04294e7398bde2072c51769bc0e50a2f54799ec3e80d
  | 13 => 0x32577ca1c6eb10355a7fa4c9ee13385d82a7ccf1163b6085aacff4193e6388ad
  | 14 => 0xd2f71c41668bb0d5fa1f44698eb3d8fd22476c91b6db00254a6f94b9de03284d
  | 15 => 0x7297bce1062b50759abfe4092e53789dc2e70c31567babd0f51a3f6489aed3f8
  | 16 => 0x1d42678cb1d6fb20456a8fb4d9fe23486d92b7dc01264b7095badf04294e7398
  | 17 => 0xbde2072c51769bc0e50a2f54799ec3e80d32577ca1c6eb10355a7fa4c9ee1338
  | 18 => 0x5d82a7ccf1163b6085aacff4193e6388add2f71c41668bb0d5fa1f44698eb3d8
  | 19 => 0xfd22476c91b6db00254a6f94b9de03284d7297bce1062b50759abfe4092e5378
  | 20 => 0x9dc2e70c31567ba0c5ea0f34597ea3c8ed12375c81a6cbf0153a5f84a9cef318
  | 21 => 0x3d6287acd1f61b40658aafd4f91e43688db2d7fc21466b90b5daff24496e93b8
  | 22 => 0xdd02274c7196bbe0052a4f7499bee3082d52779cc1e60b30557a9fc4e90e3358
  | 23 => 0x7da2c7ec11365b80a5caef14395e83a8cdfd22476c91b6db00254a6f94b9de03
  | 24 => 0x284d7297bce1062b50759abfe4092e53789dc2e70c31567ba0c5ea0f34597ea3
  | 25 => 0xc8ed12375c81a6cbf0153a5f84a9cef3183d6287acd1f61b40658aafd4f91e43
  | 26 => 0x688db2d7fc21466b90b5daff24496e93b8dd02274c7196bbe0052a4f7499bee3
  | 27 => 0x082d52779cc1e60b30557a9fc4e90e33587da2c7ec11365b80a5caef14395e83
  | 28 => 0xa8cdf2173c6186abd0f51a3f6489aed3f81d42678cb1d6fb20456a8fb4d9fe23
  | 29 => 0x486d92b7dc01264b7095badf04294e7398bde2072c51769bc0e50a2f54799ec3
  | _ => 0xe80d32577ca1c6eb10355a7fa4c9ee13385d82a7ccf1163b6085aacff4193e63

def prefixPushIndex (k : Fin 31) : Nat :=
  match k.val with
  | 0 => 860
  | 1 => 886
  | 2 => 902
  | 3 => 918
  | 4 => 929
  | 5 => 935
  | 6 => 941
  | 7 => 947
  | 8 => 958
  | 9 => 964
  | 10 => 970
  | 11 => 981
  | 12 => 987
  | 13 => 993
  | 14 => 999
  | 15 => 1005
  | 16 => 1011
  | 17 => 1017
  | 18 => 1023
  | 19 => 1029
  | 20 => 1035
  | 21 => 1041
  | 22 => 1047
  | 23 => 1053
  | 24 => 1059
  | 25 => 1065
  | 26 => 1071
  | 27 => 1077
  | 28 => 1083
  | 29 => 1089
  | _ => 1095

/-- Exact frozen partial-tail PUSH32 words. Whole-word sizes use dummy zero. -/
def tailWord (p : Fin 14) : UInt256 :=
  match p.val with
  | 0 => 0x0700000000000000000000000000000000000000000000000000000000000000
  | 1 => 0x072c51769bc0e50a2f54799ec3e80d32577ca1c6eb10355a7fa4c9ee13385d00
  | 2 => 0
  | 3 => 0xa7ccf1163b6085aacff4193e6388add2f71c41668bb0d5000000000000000000
  | 4 => 0xa7ccf1163b6085aacff4193e6388add2f71c41668bb0d5fa0000000000000000
  | 5 => 0xa7ccf1163b6085aacff4193e6388add2f71c41668bb0d5fa1f44698eb3d8fd00
  | 6 => 0
  | 7 => 0x4700000000000000000000000000000000000000000000000000000000000000
  | 8 => 0xe70c31567ba0c5ea0f34597ea3c8ed12375c81a6cbf015000000000000000000
  | 9 => 0xe70c31567ba0c5ea0f34597ea3c8ed12375c81a6cbf0153a0000000000000000
  | 10 => 0
  | 11 => 0
  | 12 => 0xf2173c6186abd0f51a3f6489aed3f81d42678cb1d6fb20450000000000000000
  | _ => 0x88add2f71c41668b000000000000000000000000000000000000000000000000

def tailPushIndex (p : Fin 14) : Option Nat :=
  match p.val with
  | 0 => some 1184
  | 1 => some 1198
  | 2 => none
  | 3 => some 1220
  | 4 => some 1234
  | 5 => some 1248
  | 6 => none
  | 7 => some 1270
  | 8 => some 1284
  | 9 => some 1298
  | 10 => none
  | 11 => none
  | 12 => some 1328
  | _ => some 1342

end Challenge.Ripemd160.Submission.H39Memo.PatternFacts
