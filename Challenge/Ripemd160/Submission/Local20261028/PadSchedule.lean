import Challenge.Ripemd160.Submission.Local20261028.PadModel
import Challenge.Ripemd160.Submission.Local20261028.PadCore0
import Challenge.Ripemd160.Submission.Local20261028.PadCore1
import Challenge.Ripemd160.Submission.Local20261028.PadCore2
import Challenge.Ripemd160.Submission.Local20261028.PadCore3
import Challenge.Ripemd160.Submission.Local20261028.PadCore4
import Challenge.Ripemd160.Submission.Local20261028.PadCore5
import Challenge.Ripemd160.Submission.Local20261028.PadCore6
import Challenge.Ripemd160.Submission.Local20261028.PadCore7
import Challenge.Ripemd160.Submission.Local20261028.PadCore8
import Challenge.Ripemd160.Submission.Local20261028.PadCore9
import Challenge.Ripemd160.Submission.Local20261028.PadCore10
import Challenge.Ripemd160.Submission.Local20261028.PadCore11
import Challenge.Ripemd160.Submission.Local20261028.PadCore12
import Challenge.Ripemd160.Submission.Local20261028.PadCore13
import Challenge.Ripemd160.Submission.Local20261028.PadCore14
import Challenge.Ripemd160.Submission.Local20261028.PadCore15
import Challenge.Ripemd160.Submission.Local20261028.PadCore16
import Challenge.Ripemd160.Submission.Local20261028.PadCore17
import Challenge.Ripemd160.Submission.Local20261028.PadCore18
import Challenge.Ripemd160.Submission.Local20261028.PadCore19
import Challenge.Ripemd160.Submission.Local20261028.PadCore20
import Challenge.Ripemd160.Submission.Local20261028.PadCore21
import Challenge.Ripemd160.Submission.Local20261028.PadCore22
import Challenge.Ripemd160.Submission.Local20261028.PadCore23
import Challenge.Ripemd160.Submission.Local20261028.PadCore24
import Challenge.Ripemd160.Submission.Local20261028.PadCore25
import Challenge.Ripemd160.Submission.Local20261028.PadCore26
import Challenge.Ripemd160.Submission.Local20261028.PadCore27
import Challenge.Ripemd160.Submission.Local20261028.PadCore28
import Challenge.Ripemd160.Submission.Local20261028.PadCore29
import Challenge.Ripemd160.Submission.Local20261028.PadCore30
import Challenge.Ripemd160.Submission.Local20261028.PadCore31
import Challenge.Ripemd160.Submission.Local20261028.PadCore32
import Challenge.Ripemd160.Submission.Local20261028.PadCore33
import Challenge.Ripemd160.Submission.Local20261028.PadCore34
import Challenge.Ripemd160.Submission.Local20261028.PadCore35
import Challenge.Ripemd160.Submission.Local20261028.PadCore36
import Challenge.Ripemd160.Submission.Local20261028.PadCore37
import Challenge.Ripemd160.Submission.Local20261028.PadCore38
import Challenge.Ripemd160.Submission.Local20261028.PadCore39
import Challenge.Ripemd160.Submission.Local20261028.PadCore40
import Challenge.Ripemd160.Submission.Local20261028.PadCore41
import Challenge.Ripemd160.Submission.Local20261028.PadCore42
import Challenge.Ripemd160.Submission.Local20261028.PadCore43
import Challenge.Ripemd160.Submission.Local20261028.PadCore44
import Challenge.Ripemd160.Submission.Local20261028.PadCore45
import Challenge.Ripemd160.Submission.Local20261028.PadCore46
import Challenge.Ripemd160.Submission.Local20261028.PadCore47
import Challenge.Ripemd160.Submission.Local20261028.PadCore48
import Challenge.Ripemd160.Submission.Local20261028.PadCore49
import Challenge.Ripemd160.Submission.Local20261028.PadCore50
import Challenge.Ripemd160.Submission.Local20261028.PadCore51
import Challenge.Ripemd160.Submission.Local20261028.PadCore52
import Challenge.Ripemd160.Submission.Local20261028.PadCore53
import Challenge.Ripemd160.Submission.Local20261028.PadCore54
import Challenge.Ripemd160.Submission.Local20261028.PadCore55
import Challenge.Ripemd160.Submission.Local20261028.PadCore56
import Challenge.Ripemd160.Submission.Local20261028.PadCore57
import Challenge.Ripemd160.Submission.Local20261028.PadCore58
import Challenge.Ripemd160.Submission.Local20261028.PadCore59
import Challenge.Ripemd160.Submission.Local20261028.PadCore60
import Challenge.Ripemd160.Submission.Local20261028.PadCore61
import Challenge.Ripemd160.Submission.Local20261028.PadCore62
import Challenge.Ripemd160.Submission.Local20261028.PadCore63
import Challenge.Ripemd160.Submission.Local20261028.PadCore64
import Challenge.Ripemd160.Submission.Local20261028.PadCore65
import Challenge.Ripemd160.Submission.Local20261028.PadCore66
import Challenge.Ripemd160.Submission.Local20261028.PadCore67
import Challenge.Ripemd160.Submission.Local20261028.PadCore68
import Challenge.Ripemd160.Submission.Local20261028.PadCore69
import Challenge.Ripemd160.Submission.Local20261028.PadCore70
import Challenge.Ripemd160.Submission.Local20261028.PadCore71
import Challenge.Ripemd160.Submission.Local20261028.PadCore72
import Challenge.Ripemd160.Submission.Local20261028.PadCore73
import Challenge.Ripemd160.Submission.Local20261028.PadCore74
import Challenge.Ripemd160.Submission.Local20261028.PadCore75
import Challenge.Ripemd160.Submission.Local20261028.PadCore76

set_option warningAsError true
set_option autoImplicit false
set_option maxErrors 3
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000
namespace Challenge.Ripemd160.Submission.Proofs.Bytecode.Local20261028.PadComposition
open EvmSemantics EvmSemantics.EVM YulEvmCompiler Challenge.EvmProof
open PairedLaneUInt256Bridge Paired144WordRound StackRoundTrace PadCommon
def shapes : Nat → List Reg
  | 0 => [ .pair, .upper, .e, .b, .a, .d, .c, .factor, .lower, .cache 140, .cache 350, .cache 310, .cache 190, .cache 500 ]
  | 1 => [ .d, .factor, .cache 350, .literal 23, .literal 1109194275457955143375908765704, .pair, .upper, .a, .c, .k, .e, .b, .factor, .lower, .cache 140, .cache 350, .cache 310, .cache 190, .cache 500 ]
  | 2 => [ .d, .literal 23, .literal 1109194275457955143375908765704, .pair, .upper, .e, .b, .k, .a, .c, .factor, .lower, .cache 140, .cache 350, .cache 310, .cache 190, .cache 500 ]
  | 3 => [ .d, .cache 310, .cache 140, .e, .literal 23, .literal 1109194275457955143375908765704, .pair, .upper, .a, .c, .k, .e, .b, .factor, .lower, .cache 140, .cache 350, .cache 310, .cache 190, .cache 500 ]
  | 4 => [ .d, .literal 23, .literal 1109194275457955143375908765704, .pair, .upper, .e, .b, .k, .a, .c, .factor, .lower, .cache 140, .cache 350, .cache 310, .cache 190, .cache 500 ]
  | 5 => [ .d, .factor, .cache 350, .e, .literal 23, .literal 1109194275457955143375908765704, .pair, .upper, .a, .c, .k, .e, .b, .factor, .lower, .cache 140, .cache 350, .cache 310, .cache 190, .cache 500 ]
  | 6 => [ .d, .literal 23, .literal 1109194275457955143375908765704, .pair, .upper, .e, .b, .k, .a, .c, .factor, .lower, .cache 140, .cache 350, .cache 310, .cache 190, .cache 500 ]
  | 7 => [ .d, .factor, .cache 350, .e, .literal 23, .literal 1109194275457955143375908765704, .pair, .upper, .a, .c, .k, .e, .b, .factor, .lower, .cache 140, .cache 350, .cache 310, .cache 190, .cache 500 ]
  | 8 => [ .d, .literal 23, .literal 1109194275457955143375908765704, .pair, .upper, .e, .b, .k, .a, .c, .factor, .lower, .cache 140, .cache 350, .cache 310, .cache 190, .cache 500 ]
  | 9 => [ .d, .cache 140, .e, .literal 23, .literal 1109194275457955143375908765704, .pair, .upper, .a, .c, .k, .e, .b, .factor, .lower, .cache 140, .cache 350, .cache 310, .cache 190, .cache 500 ]
  | 10 => [ .d, .literal 23, .literal 1109194275457955143375908765704, .pair, .upper, .e, .b, .k, .a, .c, .factor, .lower, .cache 140, .cache 350, .cache 310, .cache 190, .cache 500 ]
  | 11 => [ .d, .cache 350, .e, .literal 23, .literal 1109194275457955143375908765704, .pair, .upper, .a, .c, .k, .e, .b, .factor, .lower, .cache 140, .cache 350, .cache 310, .cache 190, .cache 500 ]
  | 12 => [ .d, .literal 23, .literal 1109194275457955143375908765704, .pair, .upper, .e, .b, .k, .a, .c, .factor, .lower, .cache 140, .cache 350, .cache 310, .cache 190, .cache 500 ]
  | 13 => [ .d, .literal 1109194275457955143375908765704, .pair, .upper, .a, .c, .literal 23, .e, .b, .factor, .lower, .cache 140, .cache 350, .cache 310, .cache 190, .cache 500 ]
  | 14 => [ .d, .e, .literal 1109194275457955143375908765704, .pair, .upper, .k, .b, .literal 23, .a, .c, .factor, .lower, .cache 140, .cache 350, .cache 310, .cache 190, .cache 500 ]
  | 15 => [ .d, .cache 140, .cache 140, .a, .literal 1109194275457955143375908765704, .pair, .upper, .k, .c, .literal 23, .e, .b, .factor, .lower, .cache 140, .cache 350, .cache 310, .cache 190, .cache 500 ]
  | 16 => [ .d, .cache 140, .e, .literal 1109194275457955143375908765704, .pair, .upper, .k, .b, .literal 23, .a, .c, .factor, .lower, .cache 140, .cache 350, .cache 310, .cache 190, .cache 500 ]
  | 17 => [ .d, .cache 140, .a, .literal 1109194275457955143375908765704, .pair, .upper, .e, .c, .literal 23, .k, .b, .factor, .lower, .cache 140, .cache 350, .cache 310, .cache 190, .cache 500 ]
  | 18 => [ .d, .e, .literal 1109194275457955143375908765704, .pair, .upper, .a, .b, .literal 23, .k, .c, .factor, .lower, .cache 140, .cache 350, .cache 310, .cache 190, .cache 500 ]
  | 19 => [ .d, .cache 350, .e, .a, .literal 1109194275457955143375908765704, .pair, .upper, .e, .c, .literal 23, .k, .b, .factor, .lower, .cache 140, .cache 350, .cache 310, .cache 190, .cache 500 ]
  | 20 => [ .d, .e, .literal 1109194275457955143375908765704, .pair, .upper, .a, .b, .literal 23, .k, .c, .factor, .lower, .cache 140, .cache 350, .cache 310, .cache 190, .cache 500 ]
  | 21 => [ .d, .cache 350, .e, .a, .literal 1109194275457955143375908765704, .pair, .upper, .e, .c, .literal 23, .k, .b, .factor, .lower, .cache 140, .cache 350, .cache 310, .cache 190, .cache 500 ]
  | 22 => [ .d, .e, .literal 1109194275457955143375908765704, .pair, .upper, .a, .b, .literal 23, .k, .c, .factor, .lower, .cache 140, .cache 350, .cache 310, .cache 190, .cache 500 ]
  | 23 => [ .d, .cache 350, .e, .a, .literal 1109194275457955143375908765704, .pair, .upper, .e, .c, .literal 23, .k, .b, .factor, .lower, .cache 140, .cache 350, .cache 310, .cache 190, .cache 500 ]
  | 24 => [ .d, .e, .literal 1109194275457955143375908765704, .pair, .upper, .a, .b, .literal 23, .k, .c, .factor, .lower, .cache 140, .cache 350, .cache 310, .cache 190, .cache 500 ]
  | 25 => [ .d, .cache 350, .e, .a, .literal 1109194275457955143375908765704, .pair, .upper, .e, .c, .literal 23, .k, .b, .factor, .lower, .cache 140, .cache 350, .cache 310, .cache 190, .cache 500 ]
  | 26 => [ .d, .e, .literal 1109194275457955143375908765704, .pair, .upper, .a, .b, .literal 23, .k, .c, .factor, .lower, .cache 140, .cache 350, .cache 310, .cache 190, .cache 500 ]
  | 27 => [ .d, .a, .literal 1109194275457955143375908765704, .pair, .upper, .e, .c, .literal 23, .k, .b, .factor, .lower, .cache 140, .cache 350, .cache 310, .cache 190, .cache 500 ]
  | 28 => [ .d, .cache 190, .cache 140, .e, .literal 1109194275457955143375908765704, .pair, .upper, .a, .b, .literal 23, .k, .c, .factor, .lower, .cache 140, .cache 350, .cache 310, .cache 190, .cache 500 ]
  | 29 => [ .d, .cache 190, .cache 140, .a, .literal 1109194275457955143375908765704, .pair, .upper, .e, .c, .literal 23, .literal 40945789247971450477386360121479348807026276516919705, .b, .factor, .lower, .cache 140, .cache 350, .cache 310, .cache 190, .cache 500 ]
  | 30 => [ .d, .e, .literal 1109194275457955143375908765704, .pair, .upper, .a, .b, .literal 23, .k, .c, .factor, .lower, .cache 140, .cache 350, .cache 310, .cache 190, .cache 500 ]
  | 31 => [ .d, .a, .literal 1109194275457955143375908765704, .pair, .upper, .e, .c, .literal 23, .k, .b, .factor, .lower, .cache 140, .cache 350, .cache 310, .cache 190, .cache 500 ]
  | 32 => [ .d, .literal 1109194275457955143375908765704, .pair, .upper, .a, .b, .literal 23, .e, .c, .factor, .lower, .cache 140, .cache 350, .cache 310, .cache 190, .cache 500 ]
  | 33 => [ .d, .cache 350, .factor, .cache 350, .e, .literal 1109194275457955143375908765704, .pair, .upper, .k, .c, .literal 23, .a, .b, .factor, .lower, .cache 140, .cache 350, .cache 310, .cache 190, .cache 500 ]
  | 34 => [ .d, .factor, .cache 350, .a, .literal 1109194275457955143375908765704, .pair, .upper, .k, .b, .literal 23, .e, .c, .factor, .lower, .cache 140, .cache 350, .cache 310, .cache 190, .cache 500 ]
  | 35 => [ .d, .factor, .cache 350, .e, .literal 1109194275457955143375908765704, .pair, .upper, .k, .c, .literal 23, .a, .b, .factor, .lower, .cache 140, .cache 350, .cache 310, .cache 190, .cache 500 ]
  | 36 => [ .d, .a, .literal 1109194275457955143375908765704, .pair, .upper, .k, .b, .literal 23, .e, .c, .factor, .lower, .cache 140, .cache 350, .cache 310, .cache 190, .cache 500 ]
  | 37 => [ .d, .cache 310, .cache 140, .e, .e, .literal 1109194275457955143375908765704, .pair, .upper, .k, .c, .literal 23, .a, .b, .factor, .lower, .cache 140, .cache 350, .cache 310, .cache 190, .cache 500 ]
  | 38 => [ .d, .a, .literal 1109194275457955143375908765704, .pair, .upper, .k, .b, .literal 23, .e, .c, .factor, .lower, .cache 140, .cache 350, .cache 310, .cache 190, .cache 500 ]
  | 39 => [ .d, .cache 350, .e, .e, .literal 1109194275457955143375908765704, .pair, .upper, .k, .c, .literal 23, .a, .b, .factor, .lower, .cache 140, .cache 350, .cache 310, .cache 190, .cache 500 ]
  | 40 => [ .d, .a, .literal 1109194275457955143375908765704, .pair, .upper, .k, .b, .literal 23, .e, .c, .factor, .lower, .cache 140, .cache 350, .cache 310, .cache 190, .cache 500 ]
  | 41 => [ .d, .cache 140, .e, .e, .literal 1109194275457955143375908765704, .pair, .upper, .k, .c, .literal 23, .a, .b, .factor, .lower, .cache 140, .cache 350, .cache 310, .cache 190, .cache 500 ]
  | 42 => [ .d, .a, .literal 1109194275457955143375908765704, .pair, .upper, .k, .b, .literal 23, .e, .c, .factor, .lower, .cache 140, .cache 350, .cache 310, .cache 190, .cache 500 ]
  | 43 => [ .d, .e, .literal 1109194275457955143375908765704, .pair, .upper, .k, .c, .literal 23, .a, .b, .factor, .lower, .cache 140, .cache 350, .cache 310, .cache 190, .cache 500 ]
  | 44 => [ .d, .cache 310, .cache 140, .a, .literal 1109194275457955143375908765704, .pair, .upper, .k, .b, .literal 23, .e, .c, .factor, .lower, .cache 140, .cache 350, .cache 310, .cache 190, .cache 500 ]
  | 45 => [ .d, .cache 310, .cache 140, .e, .literal 1109194275457955143375908765704, .pair, .upper, .literal 45805601672572416830120737830960963807809187239029665, .c, .literal 23, .a, .b, .factor, .lower, .cache 140, .cache 350, .cache 310, .cache 190, .cache 500 ]
  | 46 => [ .d, .a, .literal 1109194275457955143375908765704, .pair, .upper, .k, .b, .literal 23, .e, .c, .factor, .lower, .cache 140, .cache 350, .cache 310, .cache 190, .cache 500 ]
  | 47 => [ .d, .cache 310, .cache 140, .e, .literal 1109194275457955143375908765704, .pair, .upper, .k, .c, .literal 23, .a, .b, .factor, .lower, .cache 140, .cache 350, .cache 310, .cache 190, .cache 500 ]
  | 48 => [ .d, .a, .literal 1109194275457955143375908765704, .pair, .upper, .k, .b, .literal 23, .e, .c, .factor, .lower, .cache 140, .cache 350, .cache 310, .cache 190, .cache 500 ]
  | 49 => [ .d, .k, .literal 1109194275457955143375908765704, .pair, .upper, .e, .c, .literal 23, .a, .b, .factor, .lower, .cache 140, .cache 350, .cache 310, .cache 190, .cache 500 ]
  | 50 => [ .d, .k, .literal 1109194275457955143375908765704, .pair, .upper, .a, .b, .literal 23, .e, .c, .factor, .lower, .cache 140, .cache 350, .cache 310, .cache 190, .cache 500 ]
  | 51 => [ .d, .cache 350, .e, .k, .literal 1109194275457955143375908765704, .pair, .upper, .e, .c, .literal 23, .a, .b, .factor, .lower, .cache 140, .cache 350, .cache 310, .cache 190, .cache 500 ]
  | 52 => [ .d, .k, .literal 1109194275457955143375908765704, .pair, .upper, .a, .b, .literal 23, .e, .c, .factor, .lower, .cache 140, .cache 350, .cache 310, .cache 190, .cache 500 ]
  | 53 => [ .d, .cache 350, .e, .k, .literal 1109194275457955143375908765704, .pair, .upper, .e, .c, .literal 23, .a, .b, .factor, .lower, .cache 140, .cache 350, .cache 310, .cache 190, .cache 500 ]
  | 54 => [ .d, .k, .literal 1109194275457955143375908765704, .pair, .upper, .a, .b, .literal 23, .e, .c, .factor, .lower, .cache 140, .cache 350, .cache 310, .cache 190, .cache 500 ]
  | 55 => [ .d, .cache 140, .e, .k, .literal 1109194275457955143375908765704, .pair, .upper, .e, .c, .literal 23, .a, .b, .factor, .lower, .cache 140, .cache 350, .cache 310, .cache 190, .cache 500 ]
  | 56 => [ .d, .k, .literal 1109194275457955143375908765704, .pair, .upper, .a, .b, .literal 23, .e, .c, .factor, .lower, .cache 140, .cache 350, .cache 310, .cache 190, .cache 500 ]
  | 57 => [ .d, .cache 350, .e, .k, .literal 1109194275457955143375908765704, .pair, .upper, .e, .c, .literal 23, .a, .b, .factor, .lower, .cache 140, .cache 350, .cache 310, .cache 190, .cache 500 ]
  | 58 => [ .d, .k, .literal 1109194275457955143375908765704, .pair, .upper, .a, .b, .literal 23, .e, .c, .factor, .lower, .cache 140, .cache 350, .cache 310, .cache 190, .cache 500 ]
  | 59 => [ .d, .cache 140, .e, .k, .literal 1109194275457955143375908765704, .pair, .upper, .e, .c, .literal 23, .a, .b, .factor, .lower, .cache 140, .cache 350, .cache 310, .cache 190, .cache 500 ]
  | 60 => [ .d, .k, .literal 1109194275457955143375908765704, .pair, .upper, .a, .b, .literal 23, .e, .c, .factor, .lower, .cache 140, .cache 350, .cache 310, .cache 190, .cache 500 ]
  | 61 => [ .d, .literal 1109194275457955143375908765704, .pair, .upper, .e, .c, .literal 23, .a, .b, .factor, .lower, .cache 140, .cache 350, .cache 310, .cache 190, .cache 500 ]
  | 62 => [ .d, .e, .literal 1109194275457955143375908765704, .pair, .upper, .a, .b, .literal 23, .k, .c, .factor, .lower, .cache 140, .cache 350, .cache 310, .cache 190, .cache 500 ]
  | 63 => [ .d, .a, .literal 1109194275457955143375908765704, .pair, .upper, .e, .c, .literal 23, .k, .b, .factor, .lower, .cache 140, .cache 350, .cache 310, .cache 190, .cache 500 ]
  | 64 => [ .d, .e, .literal 1109194275457955143375908765704, .pair, .upper, .a, .b, .literal 23, .literal 2840853838, .c, .factor, .lower, .cache 140, .cache 350, .cache 310, .cache 190, .cache 500 ]
  | 65 => [ .d, .cache 350, .e, .a, .literal 1109194275457955143375908765704, .pair, .upper, .e, .c, .literal 23, .k, .b, .factor, .lower, .cache 140, .cache 350, .cache 310, .cache 190, .cache 500 ]
  | 66 => [ .d, .e, .literal 1109194275457955143375908765704, .pair, .upper, .a, .b, .literal 23, .k, .c, .factor, .lower, .cache 140, .cache 350, .cache 310, .cache 190, .cache 500 ]
  | 67 => [ .d, .cache 310, .cache 140, .e, .a, .literal 1109194275457955143375908765704, .pair, .upper, .e, .c, .literal 23, .k, .b, .factor, .lower, .cache 140, .cache 350, .cache 310, .cache 190, .cache 500 ]
  | 68 => [ .d, .e, .literal 1109194275457955143375908765704, .pair, .upper, .a, .b, .literal 23, .k, .c, .factor, .lower, .cache 140, .cache 350, .cache 310, .cache 190, .cache 500 ]
  | 69 => [ .d, .a, .literal 1109194275457955143375908765704, .pair, .upper, .e, .c, .literal 23, .k, .b, .factor, .lower, .cache 140, .cache 350, .cache 310, .cache 190, .cache 500 ]
  | 70 => [ .d, .e, .literal 1109194275457955143375908765704, .pair, .upper, .a, .b, .literal 23, .k, .c, .factor, .lower, .cache 140, .cache 350, .cache 310, .cache 190, .cache 500 ]
  | 71 => [ .d, .a, .literal 1109194275457955143375908765704, .pair, .upper, .e, .c, .literal 23, .k, .b, .factor, .lower, .cache 140, .cache 350, .cache 310, .cache 190, .cache 500 ]
  | 72 => [ .d, .e, .e, .literal 1109194275457955143375908765704, .pair, .upper, .a, .b, .literal 23, .k, .c, .factor, .lower, .cache 140, .cache 350, .cache 310, .cache 190, .cache 500 ]
  | 73 => [ .d, .a, .literal 1109194275457955143375908765704, .pair, .upper, .e, .c, .literal 23, .k, .b, .factor, .lower, .cache 140, .cache 350, .cache 310, .cache 190, .cache 500 ]
  | 74 => [ .d, .e, .e, .literal 1109194275457955143375908765704, .pair, .upper, .a, .b, .literal 23, .k, .c, .factor, .lower, .cache 140, .cache 350, .cache 310, .cache 190, .cache 500 ]
  | 75 => [ .d, .a, .literal 1109194275457955143375908765704, .pair, .upper, .e, .c, .literal 23, .k, .b, .factor, .lower, .cache 140, .cache 350, .cache 310, .cache 190, .cache 500 ]
  | 76 => [ .d, .e, .e, .literal 1109194275457955143375908765704, .pair, .upper, .a, .b, .literal 23, .k, .c, .factor, .lower, .cache 140, .cache 350, .cache 310, .cache 190, .cache 500 ]
  | 77 => [ .d, .a, .literal 1109194275457955143375908765704, .pair, .upper, .e, .c, .literal 23, .k, .b, .factor, .lower, .cache 140, .cache 350, .cache 310, .cache 190, .cache 500 ]
  | _ => []
def pcs : Nat → Nat
  | 0 => 6641
  | 1 => 6737
  | 2 => 6769
  | 3 => 6805
  | 4 => 6836
  | 5 => 6872
  | 6 => 6903
  | 7 => 6939
  | 8 => 6970
  | 9 => 7005
  | 10 => 7050
  | 11 => 7085
  | 12 => 7117
  | 13 => 7151
  | 14 => 7210
  | 15 => 7266
  | 16 => 7314
  | 17 => 7374
  | 18 => 7444
  | 19 => 7481
  | 20 => 7527
  | 21 => 7564
  | 22 => 7616
  | 23 => 7653
  | 24 => 7687
  | 25 => 7724
  | 26 => 7774
  | 27 => 7809
  | 28 => 7860
  | 29 => 7918
  | 30 => 7957
  | 31 => 8007
  | 32 => 8043
  | 33 => 8098
  | 34 => 8139
  | 35 => 8170
  | 36 => 8197
  | 37 => 8228
  | 38 => 8253
  | 39 => 8283
  | 40 => 8324
  | 41 => 8354
  | 42 => 8394
  | 43 => 8445
  | 44 => 8491
  | 45 => 8542
  | 46 => 8576
  | 47 => 8628
  | 48 => 8662
  | 49 => 8722
  | 50 => 8759
  | 51 => 8796
  | 52 => 8844
  | 53 => 8902
  | 54 => 8950
  | 55 => 8987
  | 56 => 9034
  | 57 => 9071
  | 58 => 9118
  | 59 => 9155
  | 60 => 9203
  | 61 => 9240
  | 62 => 9281
  | 63 => 9316
  | 64 => 9356
  | 65 => 9391
  | 66 => 9426
  | 67 => 9462
  | 68 => 9493
  | 69 => 9526
  | 70 => 9559
  | 71 => 9592
  | 72 => 9640
  | 73 => 9675
  | 74 => 9729
  | 75 => 9761
  | 76 => 9794
  | 77 => 9824
  | _ => 0
def templates : Nat → List Instr
  | 0 => PadRaw0.template
  | 1 => PadRaw1.template
  | 2 => PadRaw2.template
  | 3 => PadRaw3.template
  | 4 => PadRaw4.template
  | 5 => PadRaw5.template
  | 6 => PadRaw6.template
  | 7 => PadRaw7.template
  | 8 => PadRaw8.template
  | 9 => PadRaw9.template
  | 10 => PadRaw10.template
  | 11 => PadRaw11.template
  | 12 => PadRaw12.template
  | 13 => PadRaw13.template
  | 14 => PadRaw14.template
  | 15 => PadRaw15.template
  | 16 => PadRaw16.template
  | 17 => PadRaw17.template
  | 18 => PadRaw18.template
  | 19 => PadRaw19.template
  | 20 => PadRaw20.template
  | 21 => PadRaw21.template
  | 22 => PadRaw22.template
  | 23 => PadRaw23.template
  | 24 => PadRaw24.template
  | 25 => PadRaw25.template
  | 26 => PadRaw26.template
  | 27 => PadRaw27.template
  | 28 => PadRaw28.template
  | 29 => PadRaw29.template
  | 30 => PadRaw30.template
  | 31 => PadRaw31.template
  | 32 => PadRaw32.template
  | 33 => PadRaw33.template
  | 34 => PadRaw34.template
  | 35 => PadRaw35.template
  | 36 => PadRaw36.template
  | 37 => PadRaw37.template
  | 38 => PadRaw38.template
  | 39 => PadRaw39.template
  | 40 => PadRaw40.template
  | 41 => PadRaw41.template
  | 42 => PadRaw42.template
  | 43 => PadRaw43.template
  | 44 => PadRaw44.template
  | 45 => PadRaw45.template
  | 46 => PadRaw46.template
  | 47 => PadRaw47.template
  | 48 => PadRaw48.template
  | 49 => PadRaw49.template
  | 50 => PadRaw50.template
  | 51 => PadRaw51.template
  | 52 => PadRaw52.template
  | 53 => PadRaw53.template
  | 54 => PadRaw54.template
  | 55 => PadRaw55.template
  | 56 => PadRaw56.template
  | 57 => PadRaw57.template
  | 58 => PadRaw58.template
  | 59 => PadRaw59.template
  | 60 => PadRaw60.template
  | 61 => PadRaw61.template
  | 62 => PadRaw62.template
  | 63 => PadRaw63.template
  | 64 => PadRaw64.template
  | 65 => PadRaw65.template
  | 66 => PadRaw66.template
  | 67 => PadRaw67.template
  | 68 => PadRaw68.template
  | 69 => PadRaw69.template
  | 70 => PadRaw70.template
  | 71 => PadRaw71.template
  | 72 => PadRaw72.template
  | 73 => PadRaw73.template
  | 74 => PadRaw74.template
  | 75 => PadRaw75.template
  | 76 => PadRaw76.template
  | _ => []
def state (s : State) (len h4 : UInt256) (right : WordLane) (rho : List UInt256) (i : Nat) (q : WordLane) : State :=
  {s with pc := UInt256.ofNat (pcs i), stack := stack len h4 (shapes i) q right (StaggerModeSeven.physicalKey (i-1)) rho}

end Challenge.Ripemd160.Submission.Proofs.Bytecode.Local20261028.PadComposition
