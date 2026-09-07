import Challenge.Modexp.Submission.Proofs.Bytecode.WindowHitTableUpdateCommon

set_option warningAsError true
set_option maxRecDepth 40000
set_option maxHeartbeats 5000000

namespace Challenge.Modexp.Submission.Proofs.Bytecode.WindowHitTableUpdate14

open EvmSemantics
open EvmSemantics.EVM
open WindowHitPaths

window_table_update run_table14 gasSteps_table14 table14Path 13 14 3198 3209 1994 448

end Challenge.Modexp.Submission.Proofs.Bytecode.WindowHitTableUpdate14
