import Challenge.Modexp.Submission.Proofs.Fast.Defs
set_option warningAsError true
set_option maxRecDepth 40000
set_option maxHeartbeats 4000000
/-! Basic-block instruction paths, group 6 (instructions 1314..1368). -/

namespace Challenge.Modexp.Submission.Proofs.Fast

open EvmSemantics
open EvmSemantics.EVM
open Challenge.Modexp.Submission.Proofs.Bytecode

/-- Instructions 1314..1319, pc 1889..1897. -/
def blk1314 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 1165 .POP,
   opAt 1166 .POP,
   pushAt 1167 1 1,
   opAt 1168 .ADD,
   pushAt 1169 2 1522,
   opAt 1170 .JUMP]

/-- Instructions 1320..1332, pc 1898..1923. -/
def blk1320 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 1171 .JUMPDEST,
   opAt 1172 .POP,
   pushAt 1173 1 1,
   opAt 1174 (.Dup ⟨1, by decide⟩),
   pushAt 1175 2 3040,
   opAt 1176 .ADD,
   opAt 1177 .MSTORE,
   pushAt 1178 2 1619,
   pushAt 1179 2 1024,
   pushAt 1180 2 3072,
   pushAt 1181 2 1024,
   pushAt 1182 2 4055,
   opAt 1183 .JUMP]

/-- Instructions 1381..1388, pc 1924..1933. -/
def blk1333 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 1184 .JUMPDEST,
   opAt 1185 (.Dup ⟨4, by decide⟩),
   opAt 1186 (.Dup ⟨0, by decide⟩),
   opAt 1187 (.Dup ⟨2, by decide⟩),
   pushAt 1188 2 1024,
   opAt 1189 .ADD,
   opAt 1190 .SUB,
   opAt 1191 .RETURN]

/-- Instructions 1389..1344, pc 1934..1939. -/
def blk1341 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 1192 .JUMPDEST,
   opAt 1193 .POP,
   pushAt 1194 2 1107,
   opAt 1195 .JUMP]

/- `blk1345` (the oversize bail target `BAIL3`, pristine instructions 1345..1350) is
deleted with the size test that was its only predecessor: nothing jumps to it any more,
so the bytes are not in the candidate and the block, `bail3State`, `run_sizeCheck_bail`,
`run_bail3` and their two gas traces in `Fast/Setup.lean` are dead proof code. -/

/-- Instructions 1399..1407, pc 1900..1958. -/
def blk1351 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 1196 .JUMPDEST,
   opAt 1197 .POP,
   opAt 1198 .POP,
   opAt 1199 .POP,
   opAt 1200 .POP,
   opAt 1201 .POP,
   opAt 1202 .POP,
   pushAt 1203 2 1107,
   opAt 1204 .JUMP]

/-- Instructions 1408..1361, pc 1959..1960. -/
def blk1360 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 1205 .JUMPDEST,
   pushAt 1206 2 256]

/-- Instructions 1362..1368, pc 1963..1973. -/
def blk1362 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 1207 .JUMPDEST,
   pushAt 1208 2 1661,
   opAt 1209 (.Dup ⟨2, by decide⟩),
   opAt 1210 (.Dup ⟨0, by decide⟩),
   opAt 1211 (.Dup ⟨0, by decide⟩),
   pushAt 1212 2 1946,
   opAt 1213 .JUMP]

end Challenge.Modexp.Submission.Proofs.Fast
