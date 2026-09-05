import Challenge.Ripemd160.Submission.H39Memo.PatternTerminal

set_option warningAsError true
set_option maxRecDepth 40000
set_option maxHeartbeats 2000000

namespace Challenge.Ripemd160.Submission.H39Memo.PatternTerminalCertificates

open EvmSemantics EvmSemantics.EVM Challenge.EvmProof PatternTerminal

def entryPC (p : Fin 14) : Nat :=
  match p.val with
  | 0 => 3362
  | 1 => 3431
  | 2 => 3500
  | 3 => 3529
  | 4 => 3599
  | 5 => 3669
  | 6 => 3739
  | 7 => 3768
  | 8 => 3838
  | 9 => 3908
  | 10 => 3978
  | 11 => 4007
  | 12 => 4036
  | _ => 4107

def entryIndex (p : Fin 14) : Nat :=
  match p.val with
  | 0 => 1180
  | 1 => 1194
  | 2 => 1208
  | 3 => 1216
  | 4 => 1230
  | 5 => 1244
  | 6 => 1258
  | 7 => 1266
  | 8 => 1280
  | 9 => 1294
  | 10 => 1308
  | 11 => 1316
  | 12 => 1324
  | _ => 1338

def offsetWidth (p : Fin 14) : Fin 33 :=
  match p.val with
  | 0 => 0
  | 1 => 0
  | 2 => 0
  | 3 => 1
  | 4 => 1
  | 5 => 1
  | 6 => 0
  | 7 => 1
  | 8 => 1
  | 9 => 1
  | 10 => 0
  | 11 => 0
  | 12 => 2
  | _ => 2

def tailOffset (p : Fin 14) : Nat := 32 * ((PatternFacts.target p).size / 32)

def headP1 : HeadCertificate 3362 where
  dest := ⟨1180, .op .JUMPDEST, by rfl, by exact ⟨by decide, by trivial, rfl⟩⟩
  pop := ⟨1181, .op .POP, by rfl, by exact ⟨by decide, by trivial, rfl⟩⟩
  destInstruction := rfl
  popInstruction := rfl
  destPC := by rfl
  popPC := by rfl
  pcBound := by decide

def tailP1 : TailCertificate 3364 0 0 (PatternFacts.tailWord 0) where
  pushOffset := ⟨1182, .push 0 (UInt256.ofNat 0), by rfl, by decide⟩
  load := ⟨1183, .op .CALLDATALOAD, by rfl, by exact ⟨by decide, by trivial, rfl⟩⟩
  pushValue := ⟨1184, .push 32 (PatternFacts.tailWord 0),
    PatternFacts.tail_push 0 1184 rfl, by decide⟩
  xor := ⟨1185, .op .XOR, by rfl, by exact ⟨by decide, by trivial, rfl⟩⟩
  pushFallback := ⟨1186, .push 2 1006, by rfl, by decide⟩
  jump := ⟨1187, .op .JUMPI, by rfl, by exact ⟨by decide, by trivial, rfl⟩⟩
  offsetInstruction := rfl
  loadInstruction := rfl
  valueInstruction := rfl
  xorInstruction := rfl
  fallbackInstruction := rfl
  jumpInstruction := rfl
  offsetPC := by rfl
  loadPC := by rfl
  valuePC := by rfl
  xorPC := by rfl
  fallbackPC := by rfl
  jumpPC := by rfl
  zeroOffset := by decide
  offsetBound := by decide
  pcBound := by decide

def headP31 : HeadCertificate 3431 where
  dest := ⟨1194, .op .JUMPDEST, by rfl, by exact ⟨by decide, by trivial, rfl⟩⟩
  pop := ⟨1195, .op .POP, by rfl, by exact ⟨by decide, by trivial, rfl⟩⟩
  destInstruction := rfl
  popInstruction := rfl
  destPC := by rfl
  popPC := by rfl
  pcBound := by decide

def tailP31 : TailCertificate 3433 0 0 (PatternFacts.tailWord 1) where
  pushOffset := ⟨1196, .push 0 (UInt256.ofNat 0), by rfl, by decide⟩
  load := ⟨1197, .op .CALLDATALOAD, by rfl, by exact ⟨by decide, by trivial, rfl⟩⟩
  pushValue := ⟨1198, .push 32 (PatternFacts.tailWord 1),
    PatternFacts.tail_push 1 1198 rfl, by decide⟩
  xor := ⟨1199, .op .XOR, by rfl, by exact ⟨by decide, by trivial, rfl⟩⟩
  pushFallback := ⟨1200, .push 2 1006, by rfl, by decide⟩
  jump := ⟨1201, .op .JUMPI, by rfl, by exact ⟨by decide, by trivial, rfl⟩⟩
  offsetInstruction := rfl
  loadInstruction := rfl
  valueInstruction := rfl
  xorInstruction := rfl
  fallbackInstruction := rfl
  jumpInstruction := rfl
  offsetPC := by rfl
  loadPC := by rfl
  valuePC := by rfl
  xorPC := by rfl
  fallbackPC := by rfl
  jumpPC := by rfl
  zeroOffset := by decide
  offsetBound := by decide
  pcBound := by decide

def headP32 : HeadCertificate 3500 where
  dest := ⟨1208, .op .JUMPDEST, by rfl, by exact ⟨by decide, by trivial, rfl⟩⟩
  pop := ⟨1209, .op .POP, by rfl, by exact ⟨by decide, by trivial, rfl⟩⟩
  destInstruction := rfl
  popInstruction := rfl
  destPC := by rfl
  popPC := by rfl
  pcBound := by decide

def headP55 : HeadCertificate 3529 where
  dest := ⟨1216, .op .JUMPDEST, by rfl, by exact ⟨by decide, by trivial, rfl⟩⟩
  pop := ⟨1217, .op .POP, by rfl, by exact ⟨by decide, by trivial, rfl⟩⟩
  destInstruction := rfl
  popInstruction := rfl
  destPC := by rfl
  popPC := by rfl
  pcBound := by decide

def tailP55 : TailCertificate 3531 1 32 (PatternFacts.tailWord 3) where
  pushOffset := ⟨1218, .push 1 (UInt256.ofNat 32), by rfl, by decide⟩
  load := ⟨1219, .op .CALLDATALOAD, by rfl, by exact ⟨by decide, by trivial, rfl⟩⟩
  pushValue := ⟨1220, .push 32 (PatternFacts.tailWord 3),
    PatternFacts.tail_push 3 1220 rfl, by decide⟩
  xor := ⟨1221, .op .XOR, by rfl, by exact ⟨by decide, by trivial, rfl⟩⟩
  pushFallback := ⟨1222, .push 2 1006, by rfl, by decide⟩
  jump := ⟨1223, .op .JUMPI, by rfl, by exact ⟨by decide, by trivial, rfl⟩⟩
  offsetInstruction := rfl
  loadInstruction := rfl
  valueInstruction := rfl
  xorInstruction := rfl
  fallbackInstruction := rfl
  jumpInstruction := rfl
  offsetPC := by rfl
  loadPC := by rfl
  valuePC := by rfl
  xorPC := by rfl
  fallbackPC := by rfl
  jumpPC := by rfl
  zeroOffset := by decide
  offsetBound := by decide
  pcBound := by decide

def headP56 : HeadCertificate 3599 where
  dest := ⟨1230, .op .JUMPDEST, by rfl, by exact ⟨by decide, by trivial, rfl⟩⟩
  pop := ⟨1231, .op .POP, by rfl, by exact ⟨by decide, by trivial, rfl⟩⟩
  destInstruction := rfl
  popInstruction := rfl
  destPC := by rfl
  popPC := by rfl
  pcBound := by decide

def tailP56 : TailCertificate 3601 1 32 (PatternFacts.tailWord 4) where
  pushOffset := ⟨1232, .push 1 (UInt256.ofNat 32), by rfl, by decide⟩
  load := ⟨1233, .op .CALLDATALOAD, by rfl, by exact ⟨by decide, by trivial, rfl⟩⟩
  pushValue := ⟨1234, .push 32 (PatternFacts.tailWord 4),
    PatternFacts.tail_push 4 1234 rfl, by decide⟩
  xor := ⟨1235, .op .XOR, by rfl, by exact ⟨by decide, by trivial, rfl⟩⟩
  pushFallback := ⟨1236, .push 2 1006, by rfl, by decide⟩
  jump := ⟨1237, .op .JUMPI, by rfl, by exact ⟨by decide, by trivial, rfl⟩⟩
  offsetInstruction := rfl
  loadInstruction := rfl
  valueInstruction := rfl
  xorInstruction := rfl
  fallbackInstruction := rfl
  jumpInstruction := rfl
  offsetPC := by rfl
  loadPC := by rfl
  valuePC := by rfl
  xorPC := by rfl
  fallbackPC := by rfl
  jumpPC := by rfl
  zeroOffset := by decide
  offsetBound := by decide
  pcBound := by decide

def headP63 : HeadCertificate 3669 where
  dest := ⟨1244, .op .JUMPDEST, by rfl, by exact ⟨by decide, by trivial, rfl⟩⟩
  pop := ⟨1245, .op .POP, by rfl, by exact ⟨by decide, by trivial, rfl⟩⟩
  destInstruction := rfl
  popInstruction := rfl
  destPC := by rfl
  popPC := by rfl
  pcBound := by decide

def tailP63 : TailCertificate 3671 1 32 (PatternFacts.tailWord 5) where
  pushOffset := ⟨1246, .push 1 (UInt256.ofNat 32), by rfl, by decide⟩
  load := ⟨1247, .op .CALLDATALOAD, by rfl, by exact ⟨by decide, by trivial, rfl⟩⟩
  pushValue := ⟨1248, .push 32 (PatternFacts.tailWord 5),
    PatternFacts.tail_push 5 1248 rfl, by decide⟩
  xor := ⟨1249, .op .XOR, by rfl, by exact ⟨by decide, by trivial, rfl⟩⟩
  pushFallback := ⟨1250, .push 2 1006, by rfl, by decide⟩
  jump := ⟨1251, .op .JUMPI, by rfl, by exact ⟨by decide, by trivial, rfl⟩⟩
  offsetInstruction := rfl
  loadInstruction := rfl
  valueInstruction := rfl
  xorInstruction := rfl
  fallbackInstruction := rfl
  jumpInstruction := rfl
  offsetPC := by rfl
  loadPC := by rfl
  valuePC := by rfl
  xorPC := by rfl
  fallbackPC := by rfl
  jumpPC := by rfl
  zeroOffset := by decide
  offsetBound := by decide
  pcBound := by decide

def headP64 : HeadCertificate 3739 where
  dest := ⟨1258, .op .JUMPDEST, by rfl, by exact ⟨by decide, by trivial, rfl⟩⟩
  pop := ⟨1259, .op .POP, by rfl, by exact ⟨by decide, by trivial, rfl⟩⟩
  destInstruction := rfl
  popInstruction := rfl
  destPC := by rfl
  popPC := by rfl
  pcBound := by decide

def headP65 : HeadCertificate 3768 where
  dest := ⟨1266, .op .JUMPDEST, by rfl, by exact ⟨by decide, by trivial, rfl⟩⟩
  pop := ⟨1267, .op .POP, by rfl, by exact ⟨by decide, by trivial, rfl⟩⟩
  destInstruction := rfl
  popInstruction := rfl
  destPC := by rfl
  popPC := by rfl
  pcBound := by decide

def tailP65 : TailCertificate 3770 1 64 (PatternFacts.tailWord 7) where
  pushOffset := ⟨1268, .push 1 (UInt256.ofNat 64), by rfl, by decide⟩
  load := ⟨1269, .op .CALLDATALOAD, by rfl, by exact ⟨by decide, by trivial, rfl⟩⟩
  pushValue := ⟨1270, .push 32 (PatternFacts.tailWord 7),
    PatternFacts.tail_push 7 1270 rfl, by decide⟩
  xor := ⟨1271, .op .XOR, by rfl, by exact ⟨by decide, by trivial, rfl⟩⟩
  pushFallback := ⟨1272, .push 2 1006, by rfl, by decide⟩
  jump := ⟨1273, .op .JUMPI, by rfl, by exact ⟨by decide, by trivial, rfl⟩⟩
  offsetInstruction := rfl
  loadInstruction := rfl
  valueInstruction := rfl
  xorInstruction := rfl
  fallbackInstruction := rfl
  jumpInstruction := rfl
  offsetPC := by rfl
  loadPC := by rfl
  valuePC := by rfl
  xorPC := by rfl
  fallbackPC := by rfl
  jumpPC := by rfl
  zeroOffset := by decide
  offsetBound := by decide
  pcBound := by decide

def headP119 : HeadCertificate 3838 where
  dest := ⟨1280, .op .JUMPDEST, by rfl, by exact ⟨by decide, by trivial, rfl⟩⟩
  pop := ⟨1281, .op .POP, by rfl, by exact ⟨by decide, by trivial, rfl⟩⟩
  destInstruction := rfl
  popInstruction := rfl
  destPC := by rfl
  popPC := by rfl
  pcBound := by decide

def tailP119 : TailCertificate 3840 1 96 (PatternFacts.tailWord 8) where
  pushOffset := ⟨1282, .push 1 (UInt256.ofNat 96), by rfl, by decide⟩
  load := ⟨1283, .op .CALLDATALOAD, by rfl, by exact ⟨by decide, by trivial, rfl⟩⟩
  pushValue := ⟨1284, .push 32 (PatternFacts.tailWord 8),
    PatternFacts.tail_push 8 1284 rfl, by decide⟩
  xor := ⟨1285, .op .XOR, by rfl, by exact ⟨by decide, by trivial, rfl⟩⟩
  pushFallback := ⟨1286, .push 2 1006, by rfl, by decide⟩
  jump := ⟨1287, .op .JUMPI, by rfl, by exact ⟨by decide, by trivial, rfl⟩⟩
  offsetInstruction := rfl
  loadInstruction := rfl
  valueInstruction := rfl
  xorInstruction := rfl
  fallbackInstruction := rfl
  jumpInstruction := rfl
  offsetPC := by rfl
  loadPC := by rfl
  valuePC := by rfl
  xorPC := by rfl
  fallbackPC := by rfl
  jumpPC := by rfl
  zeroOffset := by decide
  offsetBound := by decide
  pcBound := by decide

def headP120 : HeadCertificate 3908 where
  dest := ⟨1294, .op .JUMPDEST, by rfl, by exact ⟨by decide, by trivial, rfl⟩⟩
  pop := ⟨1295, .op .POP, by rfl, by exact ⟨by decide, by trivial, rfl⟩⟩
  destInstruction := rfl
  popInstruction := rfl
  destPC := by rfl
  popPC := by rfl
  pcBound := by decide

def tailP120 : TailCertificate 3910 1 96 (PatternFacts.tailWord 9) where
  pushOffset := ⟨1296, .push 1 (UInt256.ofNat 96), by rfl, by decide⟩
  load := ⟨1297, .op .CALLDATALOAD, by rfl, by exact ⟨by decide, by trivial, rfl⟩⟩
  pushValue := ⟨1298, .push 32 (PatternFacts.tailWord 9),
    PatternFacts.tail_push 9 1298 rfl, by decide⟩
  xor := ⟨1299, .op .XOR, by rfl, by exact ⟨by decide, by trivial, rfl⟩⟩
  pushFallback := ⟨1300, .push 2 1006, by rfl, by decide⟩
  jump := ⟨1301, .op .JUMPI, by rfl, by exact ⟨by decide, by trivial, rfl⟩⟩
  offsetInstruction := rfl
  loadInstruction := rfl
  valueInstruction := rfl
  xorInstruction := rfl
  fallbackInstruction := rfl
  jumpInstruction := rfl
  offsetPC := by rfl
  loadPC := by rfl
  valuePC := by rfl
  xorPC := by rfl
  fallbackPC := by rfl
  jumpPC := by rfl
  zeroOffset := by decide
  offsetBound := by decide
  pcBound := by decide

def headP128 : HeadCertificate 3978 where
  dest := ⟨1308, .op .JUMPDEST, by rfl, by exact ⟨by decide, by trivial, rfl⟩⟩
  pop := ⟨1309, .op .POP, by rfl, by exact ⟨by decide, by trivial, rfl⟩⟩
  destInstruction := rfl
  popInstruction := rfl
  destPC := by rfl
  popPC := by rfl
  pcBound := by decide

def headP256 : HeadCertificate 4007 where
  dest := ⟨1316, .op .JUMPDEST, by rfl, by exact ⟨by decide, by trivial, rfl⟩⟩
  pop := ⟨1317, .op .POP, by rfl, by exact ⟨by decide, by trivial, rfl⟩⟩
  destInstruction := rfl
  popInstruction := rfl
  destPC := by rfl
  popPC := by rfl
  pcBound := by decide

def headP376 : HeadCertificate 4036 where
  dest := ⟨1324, .op .JUMPDEST, by rfl, by exact ⟨by decide, by trivial, rfl⟩⟩
  pop := ⟨1325, .op .POP, by rfl, by exact ⟨by decide, by trivial, rfl⟩⟩
  destInstruction := rfl
  popInstruction := rfl
  destPC := by rfl
  popPC := by rfl
  pcBound := by decide

def tailP376 : TailCertificate 4038 2 352 (PatternFacts.tailWord 12) where
  pushOffset := ⟨1326, .push 2 (UInt256.ofNat 352), by rfl, by decide⟩
  load := ⟨1327, .op .CALLDATALOAD, by rfl, by exact ⟨by decide, by trivial, rfl⟩⟩
  pushValue := ⟨1328, .push 32 (PatternFacts.tailWord 12),
    PatternFacts.tail_push 12 1328 rfl, by decide⟩
  xor := ⟨1329, .op .XOR, by rfl, by exact ⟨by decide, by trivial, rfl⟩⟩
  pushFallback := ⟨1330, .push 2 1006, by rfl, by decide⟩
  jump := ⟨1331, .op .JUMPI, by rfl, by exact ⟨by decide, by trivial, rfl⟩⟩
  offsetInstruction := rfl
  loadInstruction := rfl
  valueInstruction := rfl
  xorInstruction := rfl
  fallbackInstruction := rfl
  jumpInstruction := rfl
  offsetPC := by rfl
  loadPC := by rfl
  valuePC := by rfl
  xorPC := by rfl
  fallbackPC := by rfl
  jumpPC := by rfl
  zeroOffset := by decide
  offsetBound := by decide
  pcBound := by decide

def headP1000 : HeadCertificate 4107 where
  dest := ⟨1338, .op .JUMPDEST, by rfl, by exact ⟨by decide, by trivial, rfl⟩⟩
  pop := ⟨1339, .op .POP, by rfl, by exact ⟨by decide, by trivial, rfl⟩⟩
  destInstruction := rfl
  popInstruction := rfl
  destPC := by rfl
  popPC := by rfl
  pcBound := by decide

def tailP1000 : TailCertificate 4109 2 992 (PatternFacts.tailWord 13) where
  pushOffset := ⟨1340, .push 2 (UInt256.ofNat 992), by rfl, by decide⟩
  load := ⟨1341, .op .CALLDATALOAD, by rfl, by exact ⟨by decide, by trivial, rfl⟩⟩
  pushValue := ⟨1342, .push 32 (PatternFacts.tailWord 13),
    PatternFacts.tail_push 13 1342 rfl, by decide⟩
  xor := ⟨1343, .op .XOR, by rfl, by exact ⟨by decide, by trivial, rfl⟩⟩
  pushFallback := ⟨1344, .push 2 1006, by rfl, by decide⟩
  jump := ⟨1345, .op .JUMPI, by rfl, by exact ⟨by decide, by trivial, rfl⟩⟩
  offsetInstruction := rfl
  loadInstruction := rfl
  valueInstruction := rfl
  xorInstruction := rfl
  fallbackInstruction := rfl
  jumpInstruction := rfl
  offsetPC := by rfl
  loadPC := by rfl
  valuePC := by rfl
  xorPC := by rfl
  fallbackPC := by rfl
  jumpPC := by rfl
  zeroOffset := by decide
  offsetBound := by decide
  pcBound := by decide

def headCertificate : (p : Fin 14) → HeadCertificate (entryPC p)
  | ⟨0, _⟩ => headP1
  | ⟨1, _⟩ => headP31
  | ⟨2, _⟩ => headP32
  | ⟨3, _⟩ => headP55
  | ⟨4, _⟩ => headP56
  | ⟨5, _⟩ => headP63
  | ⟨6, _⟩ => headP64
  | ⟨7, _⟩ => headP65
  | ⟨8, _⟩ => headP119
  | ⟨9, _⟩ => headP120
  | ⟨10, _⟩ => headP128
  | ⟨11, _⟩ => headP256
  | ⟨12, _⟩ => headP376
  | ⟨13, _⟩ => headP1000
  | ⟨n + 14, h⟩ => False.elim (by omega)

end Challenge.Ripemd160.Submission.H39Memo.PatternTerminalCertificates

