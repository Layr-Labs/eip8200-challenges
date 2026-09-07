import Challenge.Modexp.Submission.Proofs.Bytecode.WindowHitTableUpdateCommon

set_option warningAsError true
set_option maxRecDepth 40000
set_option maxHeartbeats 5000000

namespace Challenge.Modexp.Submission.Proofs.Bytecode.WindowHitTableUpdate

open EvmSemantics
open EvmSemantics.EVM
open WindowHitPaths

window_table_update run_table3 gasSteps_table3 table3Path 2 3 3053 3063 1870 96

end Challenge.Modexp.Submission.Proofs.Bytecode.WindowHitTableUpdate
