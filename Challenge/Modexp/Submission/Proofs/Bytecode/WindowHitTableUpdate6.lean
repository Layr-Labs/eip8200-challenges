import Challenge.Modexp.Submission.Proofs.Bytecode.WindowHitTableUpdateCommon

set_option warningAsError true
set_option maxRecDepth 40000
set_option maxHeartbeats 5000000

namespace Challenge.Modexp.Submission.Proofs.Bytecode.WindowHitTableUpdate6

open EvmSemantics
open EvmSemantics.EVM
open WindowHitPaths

window_table_update run_table6 gasSteps_table6 table6Path 5 6 3083 3093 1897 192

end Challenge.Modexp.Submission.Proofs.Bytecode.WindowHitTableUpdate6
