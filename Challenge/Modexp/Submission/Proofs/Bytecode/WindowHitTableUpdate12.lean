import Challenge.Modexp.Submission.Proofs.Bytecode.WindowHitTableUpdateCommon

set_option warningAsError true
set_option maxRecDepth 40000
set_option maxHeartbeats 5000000

namespace Challenge.Modexp.Submission.Proofs.Bytecode.WindowHitTableUpdate12

open EvmSemantics
open EvmSemantics.EVM
open WindowHitPaths

window_table_update run_table12 gasSteps_table12 table12Path 11 12 3147 3158 1951 384

end Challenge.Modexp.Submission.Proofs.Bytecode.WindowHitTableUpdate12
