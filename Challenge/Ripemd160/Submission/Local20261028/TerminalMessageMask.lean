import Challenge.Ripemd160.Submission.Local20261028.CandidateBytes
import Challenge.Ripemd160.Submission.Proofs.Bytecode.StackRoundTrace
import Challenge.Ripemd160.Submission.Proofs.Bytecode.PcEncoding
import Challenge.Ripemd160.Submission.Proofs.Bytecode.Paired144WordRound

set_option warningAsError true
set_option linter.unusedSimpArgs false
set_option maxHeartbeats 2000000
namespace RipemdSubmissionTerminalRepair20261028
open EvmSemantics EvmSemantics.EVM YulEvmCompiler Challenge.EvmProof
open Challenge.Ripemd160.Submission.Proofs.Bytecode
open PairedLaneUInt256Bridge Paired144Core Paired144WordRound StackRoundTrace
open RipemdSubmissionTables20261028

def template : List Instr := [.op (.Dup ⟨6, by decide⟩), .op .AND]

theorem exact_bytes :
    (Challenge.Ripemd160.Benchmark.bytecode.data.toList.drop 4420).take 2 =
      PcEncoding.assembleBytes template := by
  rw [CandidateBytes.exact_list]
  change (CandidateBytes.bytes.drop (4416+4)).take 2 = _
  rw [← List.drop_drop, CandidateBytes.drop69]
  decide +kernel

theorem run (s : State) (message a b c d e : UInt256) (rho : List UInt256)
    (hstack : rho.length ≤ 1000) (hrun : s.halt = .Running) :
    runInstrSeq template {s with pc := UInt256.ofNat 4420, stack := [message,a,b,c,d,e,pairWord] ++ rho} =
      some {s with pc := UInt256.ofNat 4422, stack := [UInt256.land pairWord message,a,b,c,d,e,pairWord] ++ rho} := by
  have hcap (n : Nat) (hn : n ≤ 20) : rho.length + n < 1024 := by omega
  simp (discharger := omega) [template, runInstrSeq, DataStepper.runInstr,
    UInt256.succ, Instr.size, hrun, hcap, Word.word_toNat_ofNat,
    Nat.add_assoc, List.getElem?_cons_zero]
  rfl

theorem masked_bits (message : UInt256) :
    bits (UInt256.land pairWord message) = normalize (bits message) := by
  simp only [bits_land, pairWord, bits_word, normalize_eq_and]
  exact BitVec.and_comm _ _

theorem masked_low (message : UInt256) :
    low (bits (UInt256.land pairWord message)) = low (bits message) := by
  rw [masked_bits, normalize, low_pack]

theorem masked_high (message : UInt256) :
    high (bits (UInt256.land pairWord message)) = high (bits message) := by
  rw [masked_bits, normalize, high_pack]

/-- This restores the terminal theorem's strict 120-bit bound for every word. -/
theorem masked_small (message : UInt256) :
    (UInt256.land pairWord message).toNat % 2^144 < 2^120 := by
  rw [← bits_toNat, masked_bits, normalize, pack_toNat]
  have hl := (low (bits message)).isLt
  omega

/-- A zero bit in the unmasked rotation now blocks a carry into the high lane. -/
theorem terminal_no_carry (message : UInt256) (junk : BitVec 144) (extra : Nat)
    (hgap : junk.getLsbD 121 = false) (hextra : extra < 2^34) :
    junk.toNat + (UInt256.land pairWord message).toNat % 2^144 + extra < 2^144 := by
  have hm := masked_small message
  have hj := junk.isLt
  have hbit : ¬ junk.toNat / 2^121 % 2 = 1 := by
    simpa only [← BitVec.testBit_toNat, Nat.testBit_eq_decide_div_mod_eq,
      decide_eq_false_iff_not] using hgap
  simp only [Nat.reducePow] at *
  omega

/-- Arithmetic values captured before the failing candidate's ADD at PC 4420.
    Their connection to calldata is reproduced by ReplayTerminalWitness.lean. -/
theorem observed_carry :
    let m : Nat := 0x93d58388d47fb29988bc0a41a6110000de8193d58388d47fb29988bc0a41a611
    let f : Nat := 0x1ffe695ffffe695c296d710ffffe400026f311a026f311a026f08cf12a7
    let a : Nat := 0x4125713400000000000000000000000000001336b25f
    let k : Nat := 0xa953fd4e
    let mask : Nat := (2^32-1)*(1+2^144)
    (m % 2^144 + f % 2^144 + a % 2^144 + k % 2^144) / 2^144 = 1 ∧
    ((m &&& mask) % 2^144 + f % 2^144 + a % 2^144 + k % 2^144) / 2^144 = 0 := by
  decide +kernel

#print axioms exact_bytes
#print axioms run
#print axioms masked_low
#print axioms masked_high
#print axioms masked_small
#print axioms terminal_no_carry
#print axioms observed_carry
end RipemdSubmissionTerminalRepair20261028
