import Challenge.Modexp.Submission.Proofs.Bytecode.WindowHitTableUpdateCommon

set_option warningAsError true
set_option maxRecDepth 40000
set_option maxHeartbeats 5000000

namespace Challenge.Modexp.Submission.Proofs.Bytecode.WindowHitTableUpdate8

open EvmSemantics
open EvmSemantics.EVM
open WindowHitPaths

window_table_update run_table8 gasSteps_table8 table8Path 7 8 3103 3114 1915 256

end Challenge.Modexp.Submission.Proofs.Bytecode.WindowHitTableUpdate8
