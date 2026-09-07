import Challenge.Modexp.Submission.Proofs.Bytecode.WindowHitTableUpdateCommon

set_option warningAsError true
set_option maxRecDepth 40000
set_option maxHeartbeats 5000000

namespace Challenge.Modexp.Submission.Proofs.Bytecode.WindowHitTableUpdate5

open EvmSemantics
open EvmSemantics.EVM
open WindowHitPaths

window_table_update run_table5 gasSteps_table5 table5Path 4 5 3069 3077 1884 160

end Challenge.Modexp.Submission.Proofs.Bytecode.WindowHitTableUpdate5
