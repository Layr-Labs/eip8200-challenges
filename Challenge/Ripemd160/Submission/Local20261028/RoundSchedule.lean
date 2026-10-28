import Challenge.Ripemd160.Submission.Local20261028.CorePaired0
import Challenge.Ripemd160.Submission.Local20261028.CorePaired1
import Challenge.Ripemd160.Submission.Local20261028.CorePaired2
import Challenge.Ripemd160.Submission.Local20261028.CorePaired3
import Challenge.Ripemd160.Submission.Local20261028.CorePaired4
import Challenge.Ripemd160.Submission.Local20261028.CorePaired5
import Challenge.Ripemd160.Submission.Local20261028.CorePaired6
import Challenge.Ripemd160.Submission.Local20261028.CorePaired7
import Challenge.Ripemd160.Submission.Local20261028.CorePaired8
import Challenge.Ripemd160.Submission.Local20261028.CorePaired9
import Challenge.Ripemd160.Submission.Local20261028.CorePaired10
import Challenge.Ripemd160.Submission.Local20261028.CorePaired11
import Challenge.Ripemd160.Submission.Local20261028.CorePaired12
import Challenge.Ripemd160.Submission.Local20261028.CorePaired13
import Challenge.Ripemd160.Submission.Local20261028.CorePaired14
import Challenge.Ripemd160.Submission.Local20261028.CorePaired15
import Challenge.Ripemd160.Submission.Local20261028.CorePaired16
import Challenge.Ripemd160.Submission.Local20261028.CorePaired17
import Challenge.Ripemd160.Submission.Local20261028.CorePaired18
import Challenge.Ripemd160.Submission.Local20261028.CorePaired19
import Challenge.Ripemd160.Submission.Local20261028.CorePaired20
import Challenge.Ripemd160.Submission.Local20261028.CorePaired21
import Challenge.Ripemd160.Submission.Local20261028.CorePaired22
import Challenge.Ripemd160.Submission.Local20261028.CorePaired23
import Challenge.Ripemd160.Submission.Local20261028.CorePaired24
import Challenge.Ripemd160.Submission.Local20261028.CorePaired25
import Challenge.Ripemd160.Submission.Local20261028.CorePaired26
import Challenge.Ripemd160.Submission.Local20261028.CorePaired27
import Challenge.Ripemd160.Submission.Local20261028.CorePaired28
import Challenge.Ripemd160.Submission.Local20261028.CorePaired29
import Challenge.Ripemd160.Submission.Local20261028.CorePaired30
import Challenge.Ripemd160.Submission.Local20261028.CorePaired31
import Challenge.Ripemd160.Submission.Local20261028.CorePaired32
import Challenge.Ripemd160.Submission.Local20261028.CorePaired33
import Challenge.Ripemd160.Submission.Local20261028.CorePaired34
import Challenge.Ripemd160.Submission.Local20261028.CorePaired35
import Challenge.Ripemd160.Submission.Local20261028.CorePaired36
import Challenge.Ripemd160.Submission.Local20261028.CorePaired37
import Challenge.Ripemd160.Submission.Local20261028.CorePaired38
import Challenge.Ripemd160.Submission.Local20261028.CorePaired39
import Challenge.Ripemd160.Submission.Local20261028.CorePaired40
import Challenge.Ripemd160.Submission.Local20261028.CorePaired41
import Challenge.Ripemd160.Submission.Local20261028.CorePaired42
import Challenge.Ripemd160.Submission.Local20261028.CorePaired43
import Challenge.Ripemd160.Submission.Local20261028.CorePaired44
import Challenge.Ripemd160.Submission.Local20261028.CorePaired45
import Challenge.Ripemd160.Submission.Local20261028.CorePaired46
import Challenge.Ripemd160.Submission.Local20261028.CorePaired47
import Challenge.Ripemd160.Submission.Local20261028.CorePaired48
import Challenge.Ripemd160.Submission.Local20261028.CorePaired49
import Challenge.Ripemd160.Submission.Local20261028.CorePaired50
import Challenge.Ripemd160.Submission.Local20261028.CorePaired51
import Challenge.Ripemd160.Submission.Local20261028.CorePaired52
import Challenge.Ripemd160.Submission.Local20261028.CorePaired53
import Challenge.Ripemd160.Submission.Local20261028.CorePaired54
import Challenge.Ripemd160.Submission.Local20261028.CorePaired55
import Challenge.Ripemd160.Submission.Local20261028.CorePaired56
import Challenge.Ripemd160.Submission.Local20261028.CorePaired57
import Challenge.Ripemd160.Submission.Local20261028.CorePaired58
import Challenge.Ripemd160.Submission.Local20261028.CorePaired59
import Challenge.Ripemd160.Submission.Local20261028.CorePaired60
import Challenge.Ripemd160.Submission.Local20261028.CorePaired61
import Challenge.Ripemd160.Submission.Local20261028.CorePaired62
import Challenge.Ripemd160.Submission.Local20261028.CorePaired63
import Challenge.Ripemd160.Submission.Local20261028.CorePaired64
import Challenge.Ripemd160.Submission.Local20261028.CorePaired65
import Challenge.Ripemd160.Submission.Local20261028.CorePaired66
import Challenge.Ripemd160.Submission.Local20261028.CorePaired67
import Challenge.Ripemd160.Submission.Local20261028.CorePaired68
import Challenge.Ripemd160.Submission.Local20261028.CorePaired69
import Challenge.Ripemd160.Submission.Local20261028.CorePaired70
import Challenge.Ripemd160.Submission.Local20261028.CorePaired71
import Challenge.Ripemd160.Submission.Local20261028.CorePaired72
import Challenge.Ripemd160.Submission.Local20261028.CorePaired73
import Challenge.Ripemd160.Submission.Local20261028.CorePaired74
import Challenge.Ripemd160.Submission.Local20261028.CorePaired75
import Challenge.Ripemd160.Submission.Local20261028.CorePaired76

set_option warningAsError true
set_option autoImplicit false
set_option maxErrors 3
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000
namespace Challenge.Ripemd160.Submission.Proofs.Bytecode.Local20261028.RoundComposition
open EvmSemantics EvmSemantics.EVM YulEvmCompiler Challenge.EvmProof
open PairedLaneUInt256Bridge Paired144WordRound StackRoundTrace CoreCommon
def shapes : Nat → List Reg
  | 0 => [ .pair, .upper, .e, .b, .a, .d, .c, .factor, .lower, .cache 140, .cache 350, .cache 310, .cache 190, .cache 500 ]
  | 1 => [ .d, .factor, .cache 350, .literal 23, .cachedMessage 360, .pair, .upper, .a, .c, .k, .e, .b, .factor, .lower, .cache 140, .cache 350, .cache 310, .cache 190, .cache 500 ]
  | 2 => [ .d, .literal 23, .cachedMessage 360, .pair, .upper, .e, .b, .k, .a, .c, .factor, .lower, .cache 140, .cache 350, .cache 310, .cache 190, .cache 500 ]
  | 3 => [ .d, .cache 310, .cache 140, .e, .literal 23, .cachedMessage 360, .pair, .upper, .a, .c, .k, .e, .b, .factor, .lower, .cache 140, .cache 350, .cache 310, .cache 190, .cache 500 ]
  | 4 => [ .d, .literal 23, .cachedMessage 360, .pair, .upper, .e, .b, .k, .a, .c, .factor, .lower, .cache 140, .cache 350, .cache 310, .cache 190, .cache 500 ]
  | 5 => [ .d, .factor, .cache 350, .e, .literal 23, .cachedMessage 360, .pair, .upper, .a, .c, .k, .e, .b, .factor, .lower, .cache 140, .cache 350, .cache 310, .cache 190, .cache 500 ]
  | 6 => [ .d, .literal 23, .cachedMessage 360, .pair, .upper, .e, .b, .k, .a, .c, .factor, .lower, .cache 140, .cache 350, .cache 310, .cache 190, .cache 500 ]
  | 7 => [ .d, .factor, .cache 350, .e, .literal 23, .cachedMessage 360, .pair, .upper, .a, .c, .k, .e, .b, .factor, .lower, .cache 140, .cache 350, .cache 310, .cache 190, .cache 500 ]
  | 8 => [ .d, .literal 23, .cachedMessage 360, .pair, .upper, .e, .b, .k, .a, .c, .factor, .lower, .cache 140, .cache 350, .cache 310, .cache 190, .cache 500 ]
  | 9 => [ .d, .cache 140, .e, .literal 23, .cachedMessage 360, .pair, .upper, .a, .c, .k, .e, .b, .factor, .lower, .cache 140, .cache 350, .cache 310, .cache 190, .cache 500 ]
  | 10 => [ .d, .literal 23, .cachedMessage 360, .pair, .upper, .e, .b, .k, .a, .c, .factor, .lower, .cache 140, .cache 350, .cache 310, .cache 190, .cache 500 ]
  | 11 => [ .d, .cache 350, .e, .literal 23, .cachedMessage 360, .pair, .upper, .a, .c, .k, .e, .b, .factor, .lower, .cache 140, .cache 350, .cache 310, .cache 190, .cache 500 ]
  | 12 => [ .d, .literal 23, .cachedMessage 360, .pair, .upper, .e, .b, .k, .a, .c, .factor, .lower, .cache 140, .cache 350, .cache 310, .cache 190, .cache 500 ]
  | 13 => [ .d, .cachedMessage 360, .pair, .upper, .a, .c, .literal 23, .e, .b, .factor, .lower, .cache 140, .cache 350, .cache 310, .cache 190, .cache 500 ]
  | 14 => [ .d, .e, .cachedMessage 360, .pair, .upper, .k, .b, .literal 23, .a, .c, .factor, .lower, .cache 140, .cache 350, .cache 310, .cache 190, .cache 500 ]
  | 15 => [ .d, .cache 140, .cache 140, .a, .cachedMessage 360, .pair, .upper, .k, .c, .literal 23, .e, .b, .factor, .lower, .cache 140, .cache 350, .cache 310, .cache 190, .cache 500 ]
  | 16 => [ .d, .cache 140, .e, .cachedMessage 360, .pair, .upper, .k, .b, .literal 23, .a, .c, .factor, .lower, .cache 140, .cache 350, .cache 310, .cache 190, .cache 500 ]
  | 17 => [ .d, .cache 140, .a, .cachedMessage 360, .pair, .upper, .e, .c, .literal 23, .k, .b, .factor, .lower, .cache 140, .cache 350, .cache 310, .cache 190, .cache 500 ]
  | 18 => [ .d, .e, .cachedMessage 360, .pair, .upper, .a, .b, .literal 23, .k, .c, .factor, .lower, .cache 140, .cache 350, .cache 310, .cache 190, .cache 500 ]
  | 19 => [ .d, .cache 350, .e, .a, .cachedMessage 360, .pair, .upper, .e, .c, .literal 23, .k, .b, .factor, .lower, .cache 140, .cache 350, .cache 310, .cache 190, .cache 500 ]
  | 20 => [ .d, .e, .cachedMessage 360, .pair, .upper, .a, .b, .literal 23, .k, .c, .factor, .lower, .cache 140, .cache 350, .cache 310, .cache 190, .cache 500 ]
  | 21 => [ .d, .cache 350, .e, .a, .cachedMessage 360, .pair, .upper, .e, .c, .literal 23, .k, .b, .factor, .lower, .cache 140, .cache 350, .cache 310, .cache 190, .cache 500 ]
  | 22 => [ .d, .e, .cachedMessage 360, .pair, .upper, .a, .b, .literal 23, .k, .c, .factor, .lower, .cache 140, .cache 350, .cache 310, .cache 190, .cache 500 ]
  | 23 => [ .d, .cache 350, .e, .a, .cachedMessage 360, .pair, .upper, .e, .c, .literal 23, .k, .b, .factor, .lower, .cache 140, .cache 350, .cache 310, .cache 190, .cache 500 ]
  | 24 => [ .d, .e, .cachedMessage 360, .pair, .upper, .a, .b, .literal 23, .k, .c, .factor, .lower, .cache 140, .cache 350, .cache 310, .cache 190, .cache 500 ]
  | 25 => [ .d, .cache 350, .e, .a, .cachedMessage 360, .pair, .upper, .e, .c, .literal 23, .k, .b, .factor, .lower, .cache 140, .cache 350, .cache 310, .cache 190, .cache 500 ]
  | 26 => [ .d, .e, .cachedMessage 360, .pair, .upper, .a, .b, .literal 23, .k, .c, .factor, .lower, .cache 140, .cache 350, .cache 310, .cache 190, .cache 500 ]
  | 27 => [ .d, .a, .cachedMessage 360, .pair, .upper, .e, .c, .literal 23, .k, .b, .factor, .lower, .cache 140, .cache 350, .cache 310, .cache 190, .cache 500 ]
  | 28 => [ .d, .cache 190, .cache 140, .e, .cachedMessage 360, .pair, .upper, .a, .b, .literal 23, .k, .c, .factor, .lower, .cache 140, .cache 350, .cache 310, .cache 190, .cache 500 ]
  | 29 => [ .d, .cache 190, .cache 140, .a, .cachedMessage 360, .pair, .upper, .e, .c, .literal 23, .literal 40945789247971450477386360121479348807026276516919705, .b, .factor, .lower, .cache 140, .cache 350, .cache 310, .cache 190, .cache 500 ]
  | 30 => [ .d, .e, .cachedMessage 360, .pair, .upper, .a, .b, .literal 23, .k, .c, .factor, .lower, .cache 140, .cache 350, .cache 310, .cache 190, .cache 500 ]
  | 31 => [ .d, .a, .cachedMessage 360, .pair, .upper, .e, .c, .literal 23, .k, .b, .factor, .lower, .cache 140, .cache 350, .cache 310, .cache 190, .cache 500 ]
  | 32 => [ .d, .cachedMessage 360, .pair, .upper, .a, .b, .literal 23, .e, .c, .factor, .lower, .cache 140, .cache 350, .cache 310, .cache 190, .cache 500 ]
  | 33 => [ .d, .cache 350, .factor, .cache 350, .e, .cachedMessage 360, .pair, .upper, .k, .c, .literal 23, .a, .b, .factor, .lower, .cache 140, .cache 350, .cache 310, .cache 190, .cache 500 ]
  | 34 => [ .d, .factor, .cache 350, .a, .cachedMessage 360, .pair, .upper, .k, .b, .literal 23, .e, .c, .factor, .lower, .cache 140, .cache 350, .cache 310, .cache 190, .cache 500 ]
  | 35 => [ .d, .factor, .cache 350, .e, .cachedMessage 360, .pair, .upper, .k, .c, .literal 23, .a, .b, .factor, .lower, .cache 140, .cache 350, .cache 310, .cache 190, .cache 500 ]
  | 36 => [ .d, .a, .cachedMessage 360, .pair, .upper, .k, .b, .literal 23, .e, .c, .factor, .lower, .cache 140, .cache 350, .cache 310, .cache 190, .cache 500 ]
  | 37 => [ .d, .cache 310, .cache 140, .e, .e, .cachedMessage 360, .pair, .upper, .k, .c, .literal 23, .a, .b, .factor, .lower, .cache 140, .cache 350, .cache 310, .cache 190, .cache 500 ]
  | 38 => [ .d, .a, .cachedMessage 360, .pair, .upper, .k, .b, .literal 23, .e, .c, .factor, .lower, .cache 140, .cache 350, .cache 310, .cache 190, .cache 500 ]
  | 39 => [ .d, .cache 350, .e, .e, .cachedMessage 360, .pair, .upper, .k, .c, .literal 23, .a, .b, .factor, .lower, .cache 140, .cache 350, .cache 310, .cache 190, .cache 500 ]
  | 40 => [ .d, .a, .cachedMessage 360, .pair, .upper, .k, .b, .literal 23, .e, .c, .factor, .lower, .cache 140, .cache 350, .cache 310, .cache 190, .cache 500 ]
  | 41 => [ .d, .cache 140, .e, .e, .cachedMessage 360, .pair, .upper, .k, .c, .literal 23, .a, .b, .factor, .lower, .cache 140, .cache 350, .cache 310, .cache 190, .cache 500 ]
  | 42 => [ .d, .a, .cachedMessage 360, .pair, .upper, .k, .b, .literal 23, .e, .c, .factor, .lower, .cache 140, .cache 350, .cache 310, .cache 190, .cache 500 ]
  | 43 => [ .d, .e, .cachedMessage 360, .pair, .upper, .k, .c, .literal 23, .a, .b, .factor, .lower, .cache 140, .cache 350, .cache 310, .cache 190, .cache 500 ]
  | 44 => [ .d, .cache 310, .cache 140, .a, .cachedMessage 360, .pair, .upper, .k, .b, .literal 23, .e, .c, .factor, .lower, .cache 140, .cache 350, .cache 310, .cache 190, .cache 500 ]
  | 45 => [ .d, .cache 310, .cache 140, .e, .cachedMessage 360, .pair, .upper, .literal 45805601672572416830120737830960963807809187239029665, .c, .literal 23, .a, .b, .factor, .lower, .cache 140, .cache 350, .cache 310, .cache 190, .cache 500 ]
  | 46 => [ .d, .a, .cachedMessage 360, .pair, .upper, .k, .b, .literal 23, .e, .c, .factor, .lower, .cache 140, .cache 350, .cache 310, .cache 190, .cache 500 ]
  | 47 => [ .d, .cache 310, .cache 140, .e, .cachedMessage 360, .pair, .upper, .k, .c, .literal 23, .a, .b, .factor, .lower, .cache 140, .cache 350, .cache 310, .cache 190, .cache 500 ]
  | 48 => [ .d, .a, .cachedMessage 360, .pair, .upper, .k, .b, .literal 23, .e, .c, .factor, .lower, .cache 140, .cache 350, .cache 310, .cache 190, .cache 500 ]
  | 49 => [ .d, .k, .cachedMessage 360, .pair, .upper, .e, .c, .literal 23, .a, .b, .factor, .lower, .cache 140, .cache 350, .cache 310, .cache 190, .cache 500 ]
  | 50 => [ .d, .k, .cachedMessage 360, .pair, .upper, .a, .b, .literal 23, .e, .c, .factor, .lower, .cache 140, .cache 350, .cache 310, .cache 190, .cache 500 ]
  | 51 => [ .d, .cache 350, .e, .k, .cachedMessage 360, .pair, .upper, .e, .c, .literal 23, .a, .b, .factor, .lower, .cache 140, .cache 350, .cache 310, .cache 190, .cache 500 ]
  | 52 => [ .d, .k, .cachedMessage 360, .pair, .upper, .a, .b, .literal 23, .e, .c, .factor, .lower, .cache 140, .cache 350, .cache 310, .cache 190, .cache 500 ]
  | 53 => [ .d, .cache 350, .e, .k, .cachedMessage 360, .pair, .upper, .e, .c, .literal 23, .a, .b, .factor, .lower, .cache 140, .cache 350, .cache 310, .cache 190, .cache 500 ]
  | 54 => [ .d, .k, .cachedMessage 360, .pair, .upper, .a, .b, .literal 23, .e, .c, .factor, .lower, .cache 140, .cache 350, .cache 310, .cache 190, .cache 500 ]
  | 55 => [ .d, .cache 140, .e, .k, .cachedMessage 360, .pair, .upper, .e, .c, .literal 23, .a, .b, .factor, .lower, .cache 140, .cache 350, .cache 310, .cache 190, .cache 500 ]
  | 56 => [ .d, .k, .cachedMessage 360, .pair, .upper, .a, .b, .literal 23, .e, .c, .factor, .lower, .cache 140, .cache 350, .cache 310, .cache 190, .cache 500 ]
  | 57 => [ .d, .cache 350, .e, .k, .cachedMessage 360, .pair, .upper, .e, .c, .literal 23, .a, .b, .factor, .lower, .cache 140, .cache 350, .cache 310, .cache 190, .cache 500 ]
  | 58 => [ .d, .k, .cachedMessage 360, .pair, .upper, .a, .b, .literal 23, .e, .c, .factor, .lower, .cache 140, .cache 350, .cache 310, .cache 190, .cache 500 ]
  | 59 => [ .d, .cache 140, .e, .k, .cachedMessage 360, .pair, .upper, .e, .c, .literal 23, .a, .b, .factor, .lower, .cache 140, .cache 350, .cache 310, .cache 190, .cache 500 ]
  | 60 => [ .d, .k, .cachedMessage 360, .pair, .upper, .a, .b, .literal 23, .e, .c, .factor, .lower, .cache 140, .cache 350, .cache 310, .cache 190, .cache 500 ]
  | 61 => [ .d, .cachedMessage 360, .pair, .upper, .e, .c, .literal 23, .a, .b, .factor, .lower, .cache 140, .cache 350, .cache 310, .cache 190, .cache 500 ]
  | 62 => [ .d, .e, .cachedMessage 360, .pair, .upper, .a, .b, .literal 23, .k, .c, .factor, .lower, .cache 140, .cache 350, .cache 310, .cache 190, .cache 500 ]
  | 63 => [ .d, .a, .cachedMessage 360, .pair, .upper, .e, .c, .literal 23, .k, .b, .factor, .lower, .cache 140, .cache 350, .cache 310, .cache 190, .cache 500 ]
  | 64 => [ .d, .e, .cachedMessage 360, .pair, .upper, .a, .b, .literal 23, .literal 2840853838, .c, .factor, .lower, .cache 140, .cache 350, .cache 310, .cache 190, .cache 500 ]
  | 65 => [ .d, .cache 350, .e, .a, .cachedMessage 360, .pair, .upper, .e, .c, .literal 23, .k, .b, .factor, .lower, .cache 140, .cache 350, .cache 310, .cache 190, .cache 500 ]
  | 66 => [ .d, .e, .cachedMessage 360, .pair, .upper, .a, .b, .literal 23, .k, .c, .factor, .lower, .cache 140, .cache 350, .cache 310, .cache 190, .cache 500 ]
  | 67 => [ .d, .cache 310, .cache 140, .e, .a, .cachedMessage 360, .pair, .upper, .e, .c, .literal 23, .k, .b, .factor, .lower, .cache 140, .cache 350, .cache 310, .cache 190, .cache 500 ]
  | 68 => [ .d, .e, .cachedMessage 360, .pair, .upper, .a, .b, .literal 23, .k, .c, .factor, .lower, .cache 140, .cache 350, .cache 310, .cache 190, .cache 500 ]
  | 69 => [ .d, .a, .cachedMessage 360, .pair, .upper, .e, .c, .literal 23, .k, .b, .factor, .lower, .cache 140, .cache 350, .cache 310, .cache 190, .cache 500 ]
  | 70 => [ .d, .e, .cachedMessage 360, .pair, .upper, .a, .b, .literal 23, .k, .c, .factor, .lower, .cache 140, .cache 350, .cache 310, .cache 190, .cache 500 ]
  | 71 => [ .d, .a, .cachedMessage 360, .pair, .upper, .e, .c, .literal 23, .k, .b, .factor, .lower, .cache 140, .cache 350, .cache 310, .cache 190, .cache 500 ]
  | 72 => [ .d, .e, .e, .cachedMessage 360, .pair, .upper, .a, .b, .literal 23, .k, .c, .factor, .lower, .cache 140, .cache 350, .cache 310, .cache 190, .cache 500 ]
  | 73 => [ .d, .a, .cachedMessage 360, .pair, .upper, .e, .c, .literal 23, .k, .b, .factor, .lower, .cache 140, .cache 350, .cache 310, .cache 190, .cache 500 ]
  | 74 => [ .d, .e, .e, .cachedMessage 360, .pair, .upper, .a, .b, .literal 23, .k, .c, .factor, .lower, .cache 140, .cache 350, .cache 310, .cache 190, .cache 500 ]
  | 75 => [ .d, .a, .cachedMessage 360, .pair, .upper, .e, .c, .literal 23, .k, .b, .factor, .lower, .cache 140, .cache 350, .cache 310, .cache 190, .cache 500 ]
  | 76 => [ .d, .e, .e, .cachedMessage 360, .pair, .upper, .a, .b, .literal 23, .k, .c, .factor, .lower, .cache 140, .cache 350, .cache 310, .cache 190, .cache 500 ]
  | 77 => [ .d, .a, .cachedMessage 360, .pair, .upper, .e, .c, .literal 23, .k, .b, .factor, .lower, .cache 140, .cache 350, .cache 310, .cache 190, .cache 500 ]
  | _ => []
def pcs : Nat → Nat
  | 0 => 1006
  | 1 => 1075
  | 2 => 1112
  | 3 => 1150
  | 4 => 1186
  | 5 => 1226
  | 6 => 1261
  | 7 => 1301
  | 8 => 1336
  | 9 => 1375
  | 10 => 1425
  | 11 => 1464
  | 12 => 1514
  | 13 => 1552
  | 14 => 1616
  | 15 => 1671
  | 16 => 1724
  | 17 => 1789
  | 18 => 1841
  | 19 => 1883
  | 20 => 1933
  | 21 => 1974
  | 22 => 2025
  | 23 => 2067
  | 24 => 2119
  | 25 => 2160
  | 26 => 2211
  | 27 => 2250
  | 28 => 2305
  | 29 => 2365
  | 30 => 2404
  | 31 => 2458
  | 32 => 2499
  | 33 => 2559
  | 34 => 2605
  | 35 => 2638
  | 36 => 2670
  | 37 => 2705
  | 38 => 2735
  | 39 => 2769
  | 40 => 2815
  | 41 => 2847
  | 42 => 2892
  | 43 => 2925
  | 44 => 2975
  | 45 => 3031
  | 46 => 3070
  | 47 => 3127
  | 48 => 3166
  | 49 => 3231
  | 50 => 3273
  | 51 => 3314
  | 52 => 3366
  | 53 => 3408
  | 54 => 3461
  | 55 => 3502
  | 56 => 3554
  | 57 => 3596
  | 58 => 3648
  | 59 => 3690
  | 60 => 3743
  | 61 => 3782
  | 62 => 3828
  | 63 => 3868
  | 64 => 3913
  | 65 => 3952
  | 66 => 4002
  | 67 => 4042
  | 68 => 4078
  | 69 => 4116
  | 70 => 4153
  | 71 => 4188
  | 72 => 4240
  | 73 => 4277
  | 74 => 4317
  | 75 => 4354
  | 76 => 4405
  | 77 => 4441
  | _ => 0
def templates : Nat → List Instr
  | 0 => RawPaired0.template
  | 1 => RawPaired1.template
  | 2 => RawPaired2.template
  | 3 => RawPaired3.template
  | 4 => RawPaired4.template
  | 5 => RawPaired5.template
  | 6 => RawPaired6.template
  | 7 => RawPaired7.template
  | 8 => RawPaired8.template
  | 9 => RawPaired9.template
  | 10 => RawPaired10.template
  | 11 => RawPaired11.template
  | 12 => RawPaired12.template
  | 13 => RawPaired13.template
  | 14 => RawPaired14.template
  | 15 => RawPaired15.template
  | 16 => RawPaired16.template
  | 17 => RawPaired17.template
  | 18 => RawPaired18.template
  | 19 => RawPaired19.template
  | 20 => RawPaired20.template
  | 21 => RawPaired21.template
  | 22 => RawPaired22.template
  | 23 => RawPaired23.template
  | 24 => RawPaired24.template
  | 25 => RawPaired25.template
  | 26 => RawPaired26.template
  | 27 => RawPaired27.template
  | 28 => RawPaired28.template
  | 29 => RawPaired29.template
  | 30 => RawPaired30.template
  | 31 => RawPaired31.template
  | 32 => RawPaired32.template
  | 33 => RawPaired33.template
  | 34 => RawPaired34.template
  | 35 => RawPaired35.template
  | 36 => RawPaired36.template
  | 37 => RawPaired37.template
  | 38 => RawPaired38.template
  | 39 => RawPaired39.template
  | 40 => RawPaired40.template
  | 41 => RawPaired41.template
  | 42 => RawPaired42.template
  | 43 => RawPaired43.template
  | 44 => RawPaired44.template
  | 45 => RawPaired45.template
  | 46 => RawPaired46.template
  | 47 => RawPaired47.template
  | 48 => RawPaired48.template
  | 49 => RawPaired49.template
  | 50 => RawPaired50.template
  | 51 => RawPaired51.template
  | 52 => RawPaired52.template
  | 53 => RawPaired53.template
  | 54 => RawPaired54.template
  | 55 => RawPaired55.template
  | 56 => RawPaired56.template
  | 57 => RawPaired57.template
  | 58 => RawPaired58.template
  | 59 => RawPaired59.template
  | 60 => RawPaired60.template
  | 61 => RawPaired61.template
  | 62 => RawPaired62.template
  | 63 => RawPaired63.template
  | 64 => RawPaired64.template
  | 65 => RawPaired65.template
  | 66 => RawPaired66.template
  | 67 => RawPaired67.template
  | 68 => RawPaired68.template
  | 69 => RawPaired69.template
  | 70 => RawPaired70.template
  | 71 => RawPaired71.template
  | 72 => RawPaired72.template
  | 73 => RawPaired73.template
  | 74 => RawPaired74.template
  | 75 => RawPaired75.template
  | 76 => RawPaired76.template
  | _ => []
def state (s : State) (h4 : UInt256) (right : WordLane) (rho : List UInt256) (i : Nat) (q : WordLane) : State :=
  {s with pc := UInt256.ofNat (pcs i), stack := stack s.memory h4 (shapes i) q right (StaggerModeSeven.physicalKey (i-1)) rho}

end Challenge.Ripemd160.Submission.Proofs.Bytecode.Local20261028.RoundComposition
