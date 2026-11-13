import Challenge.Ripemd160.Submission.Local20261028.CorePrologue
import Challenge.Ripemd160.Submission.Local20261028.PrepFirstCertificate
import Challenge.Ripemd160.Submission.Local20261028.PrepPrefixBefore
import Challenge.Ripemd160.Submission.Local20261028.PrepPrefixAfter
set_option warningAsError true
set_option maxRecDepth 100000
set_option maxHeartbeats 12000000
set_option linter.unusedSimpArgs false
namespace RipemdSubmission20261101.FirstPrologue
open EvmSemantics EvmSemantics.EVM YulEvmCompiler Challenge.EvmProof
open Challenge.Ripemd160.Submission.Proofs.Bytecode
open Challenge.Ripemd160.Submission.Proofs.Bytecode.Local20261028
open StackRoundTrace
theorem times_comm (a b : UInt256) : a * b = b * a := RawExpressionAC.mul_comm a b
theorem first_sum (x : UInt256) :
    UInt256.ofNat 1352829926 + (UInt256.ofNat 5708990770823839524233143877797980548816364272 + x) =
    UInt256.ofNat 5708990770823839524233143877797980550169194198 + x := by
  change UInt256.add _ (UInt256.add _ _) = UInt256.add _ _
  rw [← RawExpressionAC.add_assoc]
  rfl
theorem second_sum (x y : UInt256) :
    (x + (y + UInt256.ofNat 271733878)) + UInt256.ofNat 1352829926 =
    UInt256.ofNat 1624563804 + (x + y) := by
  change UInt256.add (UInt256.add _ (UInt256.add _ _)) _ = UInt256.add _ (UInt256.add _ _)
  have hc : UInt256.add (UInt256.ofNat 271733878) (UInt256.ofNat 1352829926) =
      UInt256.ofNat 1624563804 := by decide
  rw [← hc]
  simp only [RawExpressionAC.add_assoc, RawExpressionAC.add_comm, RawExpressionAC.add_left_comm]

theorem initial_sum (x : UInt256) :
    UInt256.ofNat 115792089237316195423570985008687907853269984665640564039457584007909106406518 +
      (x + UInt256.ofNat 3085414119) =
    UInt256.ofNat 115792089237316195423570985008687907853269984665640564039457584007912191820637 + x := by
  change UInt256.add _ (UInt256.add _ _) = UInt256.add _ _
  rw [RawExpressionAC.add_comm x, ← RawExpressionAC.add_assoc]
  rfl
def frame (cont : UInt256) (rho : List UInt256) : List UInt256 := [UInt256.ofNat 158456325065422163343096938498, UInt256.ofNat 4294967295, UInt256.ofNat 822752278660603021055183846080144629349832214544141570168324096, UInt256.ofNat 822752278660603021099785336477205875632903651089438293180284928, UInt256.ofNat 1109194275457955143345843994625, UInt256.ofNat 475368975196266490007815979009, UInt256.ofNat 3285377520, UInt256.ofNat 271733878, UInt256.ofNat 2562383102, UInt256.ofNat 4023233417, UInt256.ofNat 1732584193, UInt256.ofNat 1056, cont, UInt256.ofNat 450552876409790643671482431940419874915447411150352389258589821042463539455, UInt256.ofNat 1766820105243087041267848467410591083712559083657179364930612997358944255] ++ rho

def before : List Instr := [
  .op (.Dup ⟨8, by decide⟩),
  .op (.Dup ⟨1, by decide⟩),
  .op .MUL,
  .push ⟨1, by decide⟩ (UInt256.ofNat 23),
  .op .SHR,
  .op (.Dup ⟨8, by decide⟩),
  .op (.Dup ⟨8, by decide⟩),
  .op (.Dup ⟨13, by decide⟩),
  .push ⟨4, by decide⟩ (UInt256.ofNat 1352829926),
  .op .ADD,
  .push ⟨1, by decide⟩ (UInt256.ofNat 94),
  .op .MLOAD,
  .op .ADD,
  .op (.Dup ⟨13, by decide⟩),
  .op (.Dup ⟨13, by decide⟩),
  .op (.Dup ⟨13, by decide⟩),
  .op .NOT,
  .op .OR,
  .op .XOR,
  .op .ADD,
  .op (.Dup ⟨5, by decide⟩),
  .op .AND,
  .op (.Dup ⟨4, by decide⟩),
  .op .MUL,
  .push ⟨1, by decide⟩ (UInt256.ofNat 25),
  .op .SHR,
  .op .ADD,
  .op (.Dup ⟨4, by decide⟩),
  .op .AND,
  .op (.Dup ⟨4, by decide⟩),
  .op (.Dup ⟨4, by decide⟩),
  .op (.Dup ⟨6, by decide⟩),
  .op (.Dup ⟨15, by decide⟩),
  .op (.Dup ⟨6, by decide⟩),
  .op .NOT,
  .op .OR,
  .op (.Dup ⟨4, by decide⟩),
  .op .XOR,
  .push ⟨2, by decide⟩ (UInt256.ofNat 608),
  .op .MLOAD,
  .op (.Dup ⟨14, by decide⟩),
  .op .ADD,
  .op .ADD,
  .push ⟨4, by decide⟩ (UInt256.ofNat 1352829926),
  .op .ADD,
  .op .AND,
  .op .MUL,
  .push ⟨1, by decide⟩ (UInt256.ofNat 24),
  .op .SHR,
  .op (.Dup ⟨3, by decide⟩),
  .op .ADD,
  .op .AND,
  .push ⟨4, by decide⟩ (UInt256.ofNat 1352829926),
  .op (.Dup ⟨14, by decide⟩),
  .op (.Dup ⟨6, by decide⟩),
  .op .MUL,
  .push ⟨1, by decide⟩ (UInt256.ofNat 23),
  .op .SHR,
  .op (.Swap ⟨3, by decide⟩),
  .op (.Dup ⟨3, by decide⟩),
  .op (.Dup ⟨5, by decide⟩),
  .op .NOT,
  .op .OR,
  .op (.Dup ⟨3, by decide⟩),
  .op .XOR,
  .op .ADD,
  .push ⟨2, by decide⟩ (UInt256.ofNat 728),
  .op .MLOAD,
  .op .ADD,
  .op .ADD,
  .op (.Dup ⟨6, by decide⟩),
  .op .AND,
  .op (.Dup ⟨5, by decide⟩),
  .op .MUL,
  .push ⟨1, by decide⟩ (UInt256.ofNat 24),
  .op .SHR,
  .op (.Dup ⟨4, by decide⟩),
  .op .ADD,
  .op (.Dup ⟨6, by decide⟩),
  .op .AND,
  .push ⟨1, by decide⟩ (UInt256.ofNat 144),
  .op .SHL,
  .op (.Dup ⟨14, by decide⟩),
  .op .OR,
  .op (.Swap ⟨0, by decide⟩),
  .push ⟨1, by decide⟩ (UInt256.ofNat 144),
  .op .SHL,
  .op (.Dup ⟨13, by decide⟩),
  .op .OR,
  .op (.Swap ⟨3, by decide⟩),
  .push ⟨1, by decide⟩ (UInt256.ofNat 144),
  .op .SHL,
  .op (.Dup ⟨15, by decide⟩),
  .op .OR,
  .op (.Swap ⟨1, by decide⟩),
  .op (.Dup ⟨5, by decide⟩),
  .op .MUL,
  .push ⟨1, by decide⟩ (UInt256.ofNat 23),
  .op .SHR,
  .push ⟨1, by decide⟩ (UInt256.ofNat 144),
  .op .SHL,
  .op (.Dup ⟨12, by decide⟩),
  .op .OR,
  .op (.Swap ⟨2, by decide⟩),
  .push ⟨1, by decide⟩ (UInt256.ofNat 144),
  .op .SHL,
  .op (.Dup ⟨11, by decide⟩),
  .op .OR]
def after : List Instr := [
  .push ⟨1, by decide⟩ (UInt256.ofNat 94),
  .op .MLOAD,
  .push ⟨4, by decide⟩ (UInt256.ofNat 937819298),
  .op .NOT,
  .op .ADD,
  .op (.Dup ⟨2, by decide⟩),
  .op .AND,
  .op (.Dup ⟨1, by decide⟩),
  .op .MUL,
  .push ⟨1, by decide⟩ (UInt256.ofNat 25),
  .op .SHR,
  .op (.Dup ⟨7, by decide⟩),
  .op .ADD,
  .op (.Dup ⟨2, by decide⟩),
  .op .AND,
  .push ⟨2, by decide⟩ (UInt256.ofNat 144),
  .push ⟨14, by decide⟩ (UInt256.ofNat 48402048319894885521722115772514),
  .op .NOT,
  .op (.Dup ⟨2, by decide⟩),
  .op .XOR,
  .push ⟨20, by decide⟩ (UInt256.ofNat 5708990770823839524233143877797980550169194198),
  .op .ADD,
  .op (.Dup ⟨4, by decide⟩),
  .op .AND,
  .op (.Dup ⟨3, by decide⟩),
  .op .MUL,
  .push ⟨1, by decide⟩ (UInt256.ofNat 24),
  .op .SHR,
  .op (.Dup ⟨10, by decide⟩),
  .op .ADD,
  .op (.Dup ⟨4, by decide⟩),
  .op .AND,
  .push ⟨32, by decide⟩ (UInt256.ofNat 115792089237316195423570985008687907853269984589643833456955557596096051140672),
  .op (.Dup ⟨3, by decide⟩),
  .op .OR,
  .op (.Dup ⟨1, by decide⟩),
  .op .XOR,
  .push ⟨2, by decide⟩ (UInt256.ofNat 728),
  .op .MLOAD,
  .op .ADD,
  .push ⟨4, by decide⟩ (UInt256.ofNat 1624563804),
  .op .ADD,
  .op (.Dup ⟨5, by decide⟩),
  .op .AND,
  .op (.Dup ⟨4, by decide⟩),
  .op .MUL,
  .push ⟨1, by decide⟩ (UInt256.ofNat 24),
  .op .SHR,
  .push ⟨14, by decide⟩ (UInt256.ofNat 48402048319894885521726062721634),
  .op .ADD,
  .op (.Dup ⟨5, by decide⟩),
  .op .AND,
  .op (.Dup ⟨2, by decide⟩),
  .op .SHL,
  .op (.Dup ⟨13, by decide⟩),
  .op .OR,
  .op (.Swap ⟨1, by decide⟩),
  .op .SHL,
  .op (.Dup ⟨11, by decide⟩),
  .op .OR,
  .push ⟨32, by decide⟩ (UInt256.ofNat 1079401746668943083099658476574876559591009258535258467804039595810196103937),
  .op (.Swap ⟨0, by decide⟩),
  .op (.Swap ⟨2, by decide⟩),
  .op (.Dup ⟨4, by decide⟩),
  .op .MUL,
  .push ⟨2, by decide⟩ (UInt256.ofNat 23),
  .op .SHR,
  .push ⟨2, by decide⟩ (UInt256.ofNat 144),
  .op .SHL,
  .op (.Dup ⟨11, by decide⟩),
  .op .OR,
  .op (.Swap ⟨1, by decide⟩),
  .push ⟨32, by decide⟩ (UInt256.ofNat 1694783724641757432256729705924912625215692456039486305160589352908033810928)]
def suffix : List Instr := [
  .op .JUMPDEST,
  .push ⟨22, by decide⟩ (UInt256.ofNat 95780971281817308448866066055358605703522833630494720),
  .push ⟨22, by decide⟩ (UInt256.ofNat 95780971281817308448866066055358605703522837925462015)]
def erasePC (s : State) : State := {s with pc := UInt256.ofNat 0}
private theorem const0 : UInt256.mul (UInt256.ofNat 158456325065422163343096938498) (UInt256.ofNat 2562383102) = (UInt256.ofNat 406025809752656795846635423555208460796) := by decide +kernel
private theorem const1 : UInt256.shiftRight (UInt256.ofNat 406025809752656795846635423555208460796) (UInt256.ofNat 23) = (UInt256.ofNat 48402048319894885521726062721634) := by decide +kernel
private theorem const2 : UInt256.add (UInt256.ofNat 1352829926) (UInt256.ofNat 1732584193) = (UInt256.ofNat 3085414119) := by decide +kernel
private theorem const3 : UInt256.lnot (UInt256.ofNat 271733878) = (UInt256.ofNat 115792089237316195423570985008687907853269984665640564039457584007912857906057) := by decide +kernel
private theorem const4 : UInt256.lor (UInt256.ofNat 115792089237316195423570985008687907853269984665640564039457584007912857906057) (UInt256.ofNat 2562383102) = (UInt256.ofNat 115792089237316195423570985008687907853269984665640564039457584007913129639935) := by decide +kernel
private theorem const5 : UInt256.xor (UInt256.ofNat 115792089237316195423570985008687907853269984665640564039457584007913129639935) (UInt256.ofNat 4023233417) = (UInt256.ofNat 115792089237316195423570985008687907853269984665640564039457584007909106406518) := by decide +kernel
private theorem const6 : UInt256.lnot (UInt256.ofNat 48402048319894885521726062721634) = (UInt256.ofNat 115792089237316195423570985008687907853269984617238515719562698486187066918301) := by decide +kernel
private theorem const7 : UInt256.lor (UInt256.ofNat 115792089237316195423570985008687907853269984617238515719562698486187066918301) (UInt256.ofNat 4023233417) = (UInt256.ofNat 115792089237316195423570985008687907853269984617238515719562698486191013867421) := by decide +kernel
private theorem const8 : UInt256.add (UInt256.ofNat 3285377520) (UInt256.ofNat 5708990770823839524233143877797980545530986752) = (UInt256.ofNat 5708990770823839524233143877797980548816364272) := by decide +kernel
private theorem const9 : UInt256.mul (UInt256.ofNat 158456325065422163343096938498) (UInt256.ofNat 4023233417) = (UInt256.ofNat 637506782138221158774380039235547387666) := by decide +kernel
private theorem const10 : UInt256.shiftRight (UInt256.ofNat 637506782138221158774380039235547387666) (UInt256.ofNat 23) = (UInt256.ofNat 75996730582502026411817078499263) := by decide +kernel
private theorem const11 : UInt256.lnot (UInt256.ofNat 75996730582502026411817078499263) = (UInt256.ofNat 115792089237316195423570985008687907853269984589643833456955557596096051140672) := by decide +kernel
private theorem const12 : UInt256.shiftLeft (UInt256.ofNat 48402048319894885521726062721634) (UInt256.ofNat 144) = (UInt256.ofNat 1079401746668943083099658476574876559591009258535258467804039595808463519744) := by decide +kernel
private theorem const13 : UInt256.lor (UInt256.ofNat 1732584193) (UInt256.ofNat 1079401746668943083099658476574876559591009258535258467804039595808463519744) = (UInt256.ofNat 1079401746668943083099658476574876559591009258535258467804039595810196103937) := by decide +kernel
private theorem const14 : UInt256.shiftLeft (UInt256.ofNat 75996730582502026411817078499263) (UInt256.ofNat 144) = (UInt256.ofNat 1694783724641757432256729705924912625215692456039486305160589352904748433408) := by decide +kernel
private theorem const15 : UInt256.lor (UInt256.ofNat 3285377520) (UInt256.ofNat 1694783724641757432256729705924912625215692456039486305160589352904748433408) = (UInt256.ofNat 1694783724641757432256729705924912625215692456039486305160589352908033810928) := by decide +kernel
private theorem const16 : UInt256.lnot (UInt256.ofNat 937819298) = (UInt256.ofNat 115792089237316195423570985008687907853269984665640564039457584007912191820637) := by decide +kernel
private theorem const17 : UInt256.lnot (UInt256.ofNat 48402048319894885521722115772514) = (UInt256.ofNat 115792089237316195423570985008687907853269984617238515719562698486191013867421) := by decide +kernel
private theorem add_literals (a b : Nat) :
    UInt256.add (UInt256.ofNat a) (UInt256.ofNat b) = UInt256.ofNat (a+b) := Word.ofNat_add_mod a b
private theorem add_literal_chain (a b : Nat) (x : UInt256) :
    UInt256.add (UInt256.ofNat a) (UInt256.add (UInt256.ofNat b) x) = UInt256.add (UInt256.ofNat (a+b)) x := by
  rw [← RawExpressionAC.add_assoc, add_literals]
def args (cont : UInt256) (j : Nat) : UInt256 := ((frame cont [])[j]?).getD 0
theorem outputs_eq (s : State) (cont : UInt256) (rho : List UInt256)
    (hm608 : MachineState.readWord s.memory 608 = UInt256.ofNat 5708990770823839524233143877797980545530986752) :
    PrefixBefore.outputs (args cont) rho s = PrefixAfter.outputs (args cont) rho s := by
  simp [PrefixBefore.outputs, PrefixAfter.outputs, args, frame, hm608, const0, const1, const2, const3, const4, const5, const6, const7, const8, const9, const10, const11, const12, const13, const14, const15, const16, const17]
  simp only [initial_sum, first_sum, second_sum, times_comm,
    RawExpressionAC.land_comm, RawExpressionAC.lor_comm]
  all_goals simp only [RawExpressionAC.add_assoc, RawExpressionAC.add_comm, RawExpressionAC.add_left_comm,
    RawExpressionAC.mul_assoc, RawExpressionAC.mul_comm, RawExpressionAC.mul_left_comm,
    RawExpressionAC.land_assoc, RawExpressionAC.land_comm, RawExpressionAC.land_left_comm,
    RawExpressionAC.lor_assoc, RawExpressionAC.lor_comm, RawExpressionAC.lor_left_comm,
    RawExpressionAC.xor_assoc, RawExpressionAC.xor_comm, RawExpressionAC.xor_left_comm]
  all_goals simp only [add_literal_chain, add_literals, Nat.reduceAdd]
  all_goals trivial
#print axioms outputs_eq
theorem prefix_equivalent (s : State) (cont : UInt256) (rho : List UInt256)
    (hr : s.halt = .Running) (hs : rho.length ≤ 890) (ha : 34 ≤ s.activeWords.toNat)
    (hm608 : MachineState.readWord s.memory 608 = UInt256.ofNat 5708990770823839524233143877797980545530986752) :
    (runInstrSeq before {s with pc := UInt256.ofNat 794, stack := frame cont rho}).map erasePC =
    (runInstrSeq after {s with pc := UInt256.ofNat 10185, stack := frame cont rho}).map erasePC := by
  have hb := PrefixBefore.run s (args cont) rho (by omega) hr ha
  have he := PrefixAfter.run s (args cont) rho (by omega) hr ha
  have hi : PrefixBefore.inputs (args cont) rho = frame cont rho := by simp [PrefixBefore.inputs, args, frame]
  have hj : PrefixAfter.inputs (args cont) rho = frame cont rho := hi
  rw [hi] at hb
  rw [hj] at he
  change (runInstrSeq PrefixBefore.template _).map erasePC = (runInstrSeq PrefixAfter.template _).map erasePC
  rw [hb, he]
  simp only [Option.map_some, erasePC, PrefixBefore.memory, PrefixAfter.memory, outputs_eq s cont rho hm608]
#print axioms prefix_equivalent
end RipemdSubmission20261101.FirstPrologue
