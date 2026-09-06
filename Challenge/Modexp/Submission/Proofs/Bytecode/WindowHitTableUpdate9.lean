import Challenge.Modexp.Submission.Proofs.Bytecode.WindowHitTableUpdateCommon

set_option warningAsError true
set_option maxRecDepth 40000
set_option maxHeartbeats 5000000

namespace Challenge.Modexp.Submission.Proofs.Bytecode.WindowHitTableUpdate9

open EvmSemantics
open EvmSemantics.EVM
open WindowHitPaths

window_table_update run_table9 gasSteps_table9 table9Path 8 9 3114 3125 1924 288

end Challenge.Modexp.Submission.Proofs.Bytecode.WindowHitTableUpdate9
