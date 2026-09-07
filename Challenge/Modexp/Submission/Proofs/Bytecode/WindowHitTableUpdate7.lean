import Challenge.Modexp.Submission.Proofs.Bytecode.WindowHitTableUpdateCommon

set_option warningAsError true
set_option maxRecDepth 40000
set_option maxHeartbeats 5000000

namespace Challenge.Modexp.Submission.Proofs.Bytecode.WindowHitTableUpdate7

open EvmSemantics
open EvmSemantics.EVM
open WindowHitPaths

window_table_update run_table7 gasSteps_table7 table7Path 6 7 3093 3103 1906 224

end Challenge.Modexp.Submission.Proofs.Bytecode.WindowHitTableUpdate7
