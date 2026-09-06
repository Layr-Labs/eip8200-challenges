import Challenge.Modexp.Submission.Proofs.Bytecode.WindowHitTableUpdateCommon

set_option warningAsError true
set_option maxRecDepth 40000
set_option maxHeartbeats 5000000

namespace Challenge.Modexp.Submission.Proofs.Bytecode.WindowHitTableUpdate13

open EvmSemantics
open EvmSemantics.EVM
open WindowHitPaths

window_table_update run_table13 gasSteps_table13 table13Path 12 13 3158 3169 1960 416

end Challenge.Modexp.Submission.Proofs.Bytecode.WindowHitTableUpdate13
