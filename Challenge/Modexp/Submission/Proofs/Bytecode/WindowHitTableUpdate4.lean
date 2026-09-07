import Challenge.Modexp.Submission.Proofs.Bytecode.WindowHitTableUpdateCommon

set_option warningAsError true
set_option maxRecDepth 40000
set_option maxHeartbeats 5000000

namespace Challenge.Modexp.Submission.Proofs.Bytecode.WindowHitTableUpdate4

open EvmSemantics
open EvmSemantics.EVM
open WindowHitPaths

window_table_update run_table4 gasSteps_table4 table4Path 3 4 3061 3069 1877 128

end Challenge.Modexp.Submission.Proofs.Bytecode.WindowHitTableUpdate4
