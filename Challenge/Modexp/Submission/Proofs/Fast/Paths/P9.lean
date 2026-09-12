import Challenge.Modexp.Submission.Proofs.Fast.Defs
set_option warningAsError true
set_option maxRecDepth 40000
set_option maxHeartbeats 4000000
/-! Basic-block instruction paths, group 9 (instructions 1469..1518). -/

namespace Challenge.Modexp.Submission.Proofs.Fast

open EvmSemantics
open EvmSemantics.EVM
open Challenge.Modexp.Submission.Proofs.Bytecode

/-- Instructions 1469..1518, pc 2050..2118. -/
def blk1469 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 1173 .POP,
   opAt 1174 .POP,
   opAt 1175 (.Dup ⟨0, by decide⟩),
   pushAt 1176 2 8224,
   opAt 1177 .MLOAD,
   opAt 1178 .ADD,
   opAt 1179 (.Dup ⟨0, by decide⟩),
   pushAt 1180 2 8224,
   opAt 1181 .MSTORE,
   opAt 1182 .LT,
   pushAt 1183 2 8192,
   opAt 1184 .MSTORE,
   pushAt 1185 2 9440,
   opAt 1186 .MLOAD,
   opAt 1187 .MLOAD,
   pushAt 1188 2 9376,
   opAt 1189 .MLOAD,
   opAt 1190 .MUL,
   opAt 1191 (.Dup ⟨0, by decide⟩),
   pushAt 1192 2 9408,
   opAt 1193 .MLOAD,
   opAt 1194 .MLOAD,
   opAt 1195 (.Dup ⟨1, by decide⟩),
   opAt 1196 (.Dup ⟨1, by decide⟩),
   opAt 1197 .MUL,
   opAt 1198 (.Swap ⟨1, by decide⟩),
   pushAt 1199 0 0,
   opAt 1200 .NOT,
   opAt 1201 (.Swap ⟨1, by decide⟩),
   opAt 1202 .MULMOD,
   opAt 1203 (.Dup ⟨1, by decide⟩),
   opAt 1204 (.Dup ⟨1, by decide⟩),
   opAt 1205 .LT,
   opAt 1206 (.Dup ⟨2, by decide⟩),
   opAt 1207 .ADD,
   opAt 1208 (.Swap ⟨0, by decide⟩),
   opAt 1209 .SUB,
   opAt 1210 (.Swap ⟨0, by decide⟩),
   pushAt 1211 0 0,
   opAt 1212 .LT,
   opAt 1213 .ADD,
   pushAt 1214 2 9440,
   opAt 1215 .MLOAD,
   pushAt 1216 1 32,
   opAt 1217 (.Swap ⟨0, by decide⟩),
   opAt 1218 .SUB,
   pushAt 1219 2 9408,
   opAt 1220 .MLOAD,
   pushAt 1221 1 32,
   opAt 1222 (.Swap ⟨0, by decide⟩),
   opAt 1223 .SUB]

end Challenge.Modexp.Submission.Proofs.Fast
