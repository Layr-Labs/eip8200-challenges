import Challenge.Modexp.Submission.Proofs.Bytecode.WindowHitTableUpdateCommon

set_option warningAsError true
set_option maxRecDepth 40000
set_option maxHeartbeats 5000000

namespace Challenge.Modexp.Submission.Proofs.Bytecode.WindowHitTableUpdate15

open EvmSemantics
open EvmSemantics.EVM
open WindowHitPaths

window_table_update run_table15 gasSteps_table15 table15Path 14 15 3180 3191 1978 480

end Challenge.Modexp.Submission.Proofs.Bytecode.WindowHitTableUpdate15
