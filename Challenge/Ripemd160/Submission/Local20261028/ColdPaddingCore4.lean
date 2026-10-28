import Challenge.Ripemd160.Submission.Local20261028.ColdPaddingCore3
import Challenge.Ripemd160.Submission.Local20261028.ColdShared32Scratch
import Challenge.Ripemd160.Submission.Proofs.Bytecode.PcEncoding
import Challenge.Ripemd160.Submission.Proofs.Bytecode.Padding
import Challenge.Ripemd160.Submission.Proofs.Bytecode.StackTail
import Challenge.Ripemd160.Submission.Proofs.Bytecode.RawExpressionAC
import Challenge.Ripemd160.Submission.Local20261028.ColdTrace
import Challenge.Ripemd160.Submission.Local20261028.ColdMain
import Challenge.Ripemd160.Submission.Local20261028.ColdStaggerPersistentStart
import Challenge.Ripemd160.Submission.Local20261028.ColdGuardFinish
import Challenge.Ripemd160.Submission.Proofs.Bytecode.DataStepper
import Challenge.Ripemd160.Submission.Proofs.Bytecode.Msize
import Challenge.Ripemd160.Submission.Proofs.Bytecode.PadLimitArithmetic
set_option warningAsError true
set_option linter.unusedSimpArgs false
set_option maxRecDepth 1000000
set_option maxHeartbeats 2000000
set_option linter.unusedSimpArgs false
/-!
# Direct execution of the RIPEMD-160 padding function (setup, guard, sentinel, footer loop and exit)

The fixed setup and the eight-iteration little-endian footer loop are exposed
as located paths.  The resulting state is shared by correctness and exact gas
accounting.
-/

namespace Challenge.Ripemd160.Submission.Proofs.Bytecode.Local20261028.Control.PaddingTrace
open EvmSemantics EvmSemantics.EVM

end Challenge.Ripemd160.Submission.Proofs.Bytecode.Local20261028.Control.PaddingTrace
