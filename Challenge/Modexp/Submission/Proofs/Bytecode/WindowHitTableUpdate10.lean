import Challenge.Modexp.Submission.Proofs.Bytecode.WindowHitTableUpdateCommon

set_option warningAsError true
set_option maxRecDepth 40000
set_option maxHeartbeats 5000000

namespace Challenge.Modexp.Submission.Proofs.Bytecode.WindowHitTableUpdate10

open EvmSemantics
open EvmSemantics.EVM
open WindowHitPaths

window_table_update run_table10 gasSteps_table10 table10Path 9 10 3125 3136 1933 320

end Challenge.Modexp.Submission.Proofs.Bytecode.WindowHitTableUpdate10
