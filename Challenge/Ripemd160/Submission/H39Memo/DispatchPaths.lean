import Challenge.Ripemd160.Submission.H39Memo.Artifact
import Challenge.Ripemd160.Submission.H39Memo.DispatchState
import Challenge.Ripemd160.Submission.H39Memo.DispatchTable

set_option warningAsError true
set_option maxRecDepth 40000
set_option maxHeartbeats 8000000

namespace Challenge.Ripemd160.Submission.H39Memo.DispatchPaths

open EvmSemantics
open EvmSemantics.EVM
open Challenge.EvmProof

abbrev Located :=
  Challenge.EvmProof.Stepper.Located
    Challenge.Ripemd160.Submission.H39Memo.Artifact.referenceArtifact .Osaka

def wfOp {op : Operation}
    (hopcode : Decode.opcodeOf (YulEvmCompiler.Instr.opByte op) = some op)
    (hplain : YulEvmCompiler.plainOp op)
    (havailable : op.availableInFork .Osaka = true) :
    Challenge.EvmProof.Stepper.WellFormed .Osaka (.op op) :=
  ⟨hopcode, hplain, havailable⟩

def opAt (index : Nat) (op : Operation)
    (hget : Challenge.Ripemd160.Submission.H39Memo.Artifact.referenceInstructions[index]? =
      some (.op op) := by rfl)
    (hopcode : Decode.opcodeOf (YulEvmCompiler.Instr.opByte op) = some op := by decide)
    (hplain : YulEvmCompiler.plainOp op := by trivial)
    (havailable : op.availableInFork .Osaka = true := by rfl) : Located :=
  ⟨index, .op op, hget, wfOp hopcode hplain havailable⟩

def pushAt (index : Nat) (width : Fin 33) (value : UInt256)
    (hget : Challenge.Ripemd160.Submission.H39Memo.Artifact.referenceInstructions[index]? =
      some (.push width value) := by rfl)
    (hwf : Challenge.EvmProof.Stepper.WellFormed .Osaka (.push width value) := by decide) :
    Located :=
  ⟨index, .push width value, hget, hwf⟩

def pushValue (index : Nat) : UInt256 :=
  match Challenge.Ripemd160.Submission.H39Memo.Artifact.referenceInstructions[index]? with
  | some (.push _ value) => value
  | _ => 0

def abcWord : UInt256 := pushValue 1170

def initialPath : List Located :=
  [ pushAt 0 2 (UInt256.ofNat 1671)
  , opAt 1 .JUMP ]

def fallbackJumpDestPath : List Located :=
  [ opAt 682 .JUMPDEST ]

def guardPath : List Located :=
  [ opAt 831 .JUMPDEST
  , opAt 832 .CALLDATASIZE
  , opAt 833 (.Dup ⟨0, by decide⟩)
  , opAt 834 .ISZERO
  , pushAt 835 2 (UInt256.ofNat 3264)
  , opAt 836 .JUMPI ]

def guardAbcPath : List Located :=
  guardPath ++
  [ opAt 837 (.Dup ⟨0, by decide⟩)
  , pushAt 838 1 (UInt256.ofNat 3)
  , opAt 839 .EQ
  , pushAt 840 2 (UInt256.ofNat 3293)
  , opAt 841 .JUMPI ]

def guardToPattern1Path : List Located :=
  guardAbcPath ++
  [ opAt 842 (.Dup ⟨0, by decide⟩)
  , pushAt 843 2 (UInt256.ofNat 1000)
  , opAt 844 .EQ
  , pushAt 845 2 (UInt256.ofNat 3115)
  , opAt 846 .JUMPI
  , opAt 847 .JUMPDEST
  , opAt 848 (.Dup ⟨0, by decide⟩)
  , pushAt 849 1 (UInt256.ofNat 1)
  , opAt 850 .EQ
  , pushAt 851 2 (UInt256.ofNat 3362)
  , opAt 852 .JUMPI ]

def guardToA1000Path : List Located :=
  guardAbcPath ++
  [ opAt 842 (.Dup ⟨0, by decide⟩)
  , pushAt 843 2 (UInt256.ofNat 1000)
  , opAt 844 .EQ
  , pushAt 845 2 (UInt256.ofNat 3115)
  , opAt 846 .JUMPI ]

def guardToPatternRootPath : List Located :=
  guardToA1000Path

def emptyHeadPath : List Located :=
  [ opAt 1158 .JUMPDEST
  , opAt 1159 .POP ]

def emptyPath : List Located := emptyHeadPath

def abcCheckPath : List Located :=
  [ opAt 1166 .JUMPDEST
  , opAt 1167 .POP
  , pushAt 1168 0 (pushValue 1168)
  , opAt 1169 .CALLDATALOAD
  , pushAt 1170 32 abcWord
  , opAt 1171 .XOR
  , pushAt 1172 2 (UInt256.ofNat 1006)
  , opAt 1173 .JUMPI ]

def abcPath : List Located := abcCheckPath

def pattern1Path : List Located :=
  [ opAt 1180 .JUMPDEST
  , opAt 1181 .POP
  , pushAt 1182 0 (pushValue 1182)
  , opAt 1183 .CALLDATALOAD
  , pushAt 1184 32 (pushValue 1184)
  , opAt 1185 .XOR
  , pushAt 1186 2 (UInt256.ofNat 1006)
  , opAt 1187 .JUMPI ]

def pattern31Path : List Located :=
  [ opAt 1194 .JUMPDEST
  , opAt 1195 .POP
  , pushAt 1196 0 (pushValue 1196)
  , opAt 1197 .CALLDATALOAD
  , pushAt 1198 32 (pushValue 1198)
  , opAt 1199 .XOR
  , pushAt 1200 2 (UInt256.ofNat 1006)
  , opAt 1201 .JUMPI ]

def pattern32Path : List Located :=
  [ opAt 1208 .JUMPDEST
  , opAt 1209 .POP ]

def pattern55Path : List Located :=
  [ opAt 1216 .JUMPDEST
  , opAt 1217 .POP
  , pushAt 1218 1 (pushValue 1218)
  , opAt 1219 .CALLDATALOAD
  , pushAt 1220 32 (pushValue 1220)
  , opAt 1221 .XOR
  , pushAt 1222 2 (UInt256.ofNat 1006)
  , opAt 1223 .JUMPI ]

def pattern56Path : List Located :=
  [ opAt 1230 .JUMPDEST
  , opAt 1231 .POP
  , pushAt 1232 1 (pushValue 1232)
  , opAt 1233 .CALLDATALOAD
  , pushAt 1234 32 (pushValue 1234)
  , opAt 1235 .XOR
  , pushAt 1236 2 (UInt256.ofNat 1006)
  , opAt 1237 .JUMPI ]

def pattern63Path : List Located :=
  [ opAt 1244 .JUMPDEST
  , opAt 1245 .POP
  , pushAt 1246 1 (pushValue 1246)
  , opAt 1247 .CALLDATALOAD
  , pushAt 1248 32 (pushValue 1248)
  , opAt 1249 .XOR
  , pushAt 1250 2 (UInt256.ofNat 1006)
  , opAt 1251 .JUMPI ]

def pattern64Path : List Located :=
  [ opAt 1258 .JUMPDEST
  , opAt 1259 .POP ]

def pattern65Path : List Located :=
  [ opAt 1266 .JUMPDEST
  , opAt 1267 .POP
  , pushAt 1268 1 (pushValue 1268)
  , opAt 1269 .CALLDATALOAD
  , pushAt 1270 32 (pushValue 1270)
  , opAt 1271 .XOR
  , pushAt 1272 2 (UInt256.ofNat 1006)
  , opAt 1273 .JUMPI ]

def pattern119Path : List Located :=
  [ opAt 1280 .JUMPDEST
  , opAt 1281 .POP
  , pushAt 1282 1 (pushValue 1282)
  , opAt 1283 .CALLDATALOAD
  , pushAt 1284 32 (pushValue 1284)
  , opAt 1285 .XOR
  , pushAt 1286 2 (UInt256.ofNat 1006)
  , opAt 1287 .JUMPI ]

def pattern120Path : List Located :=
  [ opAt 1294 .JUMPDEST
  , opAt 1295 .POP
  , pushAt 1296 1 (pushValue 1296)
  , opAt 1297 .CALLDATALOAD
  , pushAt 1298 32 (pushValue 1298)
  , opAt 1299 .XOR
  , pushAt 1300 2 (UInt256.ofNat 1006)
  , opAt 1301 .JUMPI ]

def pattern128Path : List Located :=
  [ opAt 1308 .JUMPDEST
  , opAt 1309 .POP ]

def pattern256Path : List Located :=
  [ opAt 1316 .JUMPDEST
  , opAt 1317 .POP ]

def pattern376Path : List Located :=
  [ opAt 1324 .JUMPDEST
  , opAt 1325 .POP
  , pushAt 1326 2 (pushValue 1326)
  , opAt 1327 .CALLDATALOAD
  , pushAt 1328 32 (pushValue 1328)
  , opAt 1329 .XOR
  , pushAt 1330 2 (UInt256.ofNat 1006)
  , opAt 1331 .JUMPI ]

def pattern1000Path : List Located :=
  [ opAt 1338 .JUMPDEST
  , opAt 1339 .POP
  , pushAt 1340 2 (pushValue 1340)
  , opAt 1341 .CALLDATALOAD
  , pushAt 1342 32 (pushValue 1342)
  , opAt 1343 .XOR
  , pushAt 1344 2 (UInt256.ofNat 1006)
  , opAt 1345 .JUMPI ]

def patternedPaths : List (Nat × List Located) :=
  [ (1, pattern1Path)
  , (31, pattern31Path)
  , (32, pattern32Path)
  , (55, pattern55Path)
  , (56, pattern56Path)
  , (63, pattern63Path)
  , (64, pattern64Path)
  , (65, pattern65Path)
  , (119, pattern119Path)
  , (120, pattern120Path)
  , (128, pattern128Path)
  , (256, pattern256Path)
  , (376, pattern376Path)
  , (1000, pattern1000Path) ]

@[simp] theorem patternedPaths_sizes :
    patternedPaths.map Prod.fst =
      [1, 31, 32, 55, 56, 63, 64, 65, 119, 120, 128, 256, 376, 1000] := by
  rfl

end Challenge.Ripemd160.Submission.H39Memo.DispatchPaths
