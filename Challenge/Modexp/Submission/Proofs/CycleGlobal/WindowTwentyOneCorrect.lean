import Challenge.Modexp.Submission.Proofs.CycleGlobal.Binding
import Challenge.Modexp.Submission.Proofs.CycleGlobal.WindowRoute

noncomputable section
set_option warningAsError true

namespace CycleSubmission.Global.WindowTwentyOneCorrect
open Challenge.Modexp
open Challenge.Modexp.Submission.Proofs
open Challenge.Modexp.Submission.Proofs.Bytecode

def route : WindowRoute.Route where
  enter := Dispatch.gasSteps_wordRouteEnter

end CycleSubmission.Global.WindowTwentyOneCorrect

