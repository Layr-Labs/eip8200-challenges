import Challenge.Ripemd160.Submission.Proofs.Bytecode.Table144Setup
set_option warningAsError true
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000
set_option linter.unusedSimpArgs false
namespace Challenge.Ripemd160.Submission.Proofs.Bytecode.Table144Bootstrap
open EvmSemantics EvmSemantics.EVM YulEvmCompiler Challenge.EvmProof
open StackRoundTrace Table144Setup
def replication : UInt256 := UInt256.ofNat 22300745198530623141535718272648361505980417
def pairMask : UInt256 := UInt256.ofNat 95780971281817308448866066055358605703522837925462015
def upperMask : UInt256 := UInt256.ofNat 95780971281817308448866066055358605703522833630494720
def lowerMask : UInt256 := UInt256.ofNat 4294967295
def primaryFactor : UInt256 := UInt256.ofNat 20282409608374036907091774406720
def initialKey : UInt256 := UInt256.ofNat 30169115476673038213297653277143730720156734734729216
def cache : List UInt256 := [UInt256.ofNat 28, UInt256.ofNat 20282409598929303941081901039615, UInt256.ofNat 127, UInt256.ofNat 20282409608374036906834076368900, UInt256.ofNat 15, UInt256.ofNat 20282409608374036906851256238088]
def constantFrame : List UInt256 := [replication,pairMask,upperMask,lowerMask] ++ cache
def packed (h : UInt256) : UInt256 := UInt256.mul replication h

theorem run_cache (s : State) (pc : UInt256) (rho : List UInt256)
    (hstack : rho.length ≤ 996) (hrun : s.halt = .Running) :
    runInstrSeq cacheTemplate {s with pc := pc, stack := rho} =
      some {s with pc := pcAfter pc cacheTemplate, stack := constantFrame ++ rho} := by
  have hbase : rho.length < 1024 := by omega
  have hcap (n : Nat) (hn : n ≤ 27) : rho.length + n < 1024 := by omega
  simp (discharger := omega) [cacheTemplate, constantFrame, cache,
    replication, pairMask, upperMask, lowerMask,
    runInstrSeq, Stepper.runInstr, pcAfter, UInt256.succ, Instr.size,
    List.exchange, List.getElem?_cons_zero, Nat.add_assoc, hrun, hbase, hcap,
    Word.word_toNat_ofNat, Word.literal_eq_ofNat]
  all_goals repeat first | apply And.intro | rfl | decide

#print axioms run_cache
theorem run_hash (s : State) (pc h0 h1 h2 h3 h4 : UInt256) (rho : List UInt256)
    (hstack : rho.length ≤ 996) (hrun : s.halt = .Running) :
    runInstrSeq hashTemplate {s with pc := pc, stack := constantFrame ++ [h0,h1,h2,h3,h4] ++ rho} =
      some {s with
        pc := pcAfter pc hashTemplate
        stack := [packed h0, packed h1, packed h2, packed h3, packed h4] ++ constantFrame ++ [h0,h1,h2,h3,h4] ++ rho} := by
  have hbase : rho.length < 1024 := by omega
  have hcap (n : Nat) (hn : n ≤ 27) : rho.length + n < 1024 := by omega
  simp (discharger := omega) [hashTemplate, constantFrame, cache, packed,
    runInstrSeq, Stepper.runInstr, pcAfter, UInt256.succ, Instr.size,
    List.exchange, List.getElem?_cons_zero, Nat.add_assoc, hrun, hbase, hcap,
    Word.word_toNat_ofNat, Word.literal_eq_ofNat]
  all_goals repeat first | apply And.intro | rfl | decide
#print axioms run_hash
theorem run_factor (s : State) (pc a b c d e : UInt256) (rho : List UInt256)
    (hstack : rho.length ≤ 996) (hrun : s.halt = .Running) :
    runInstrSeq factorTemplate {s with pc := pc, stack := [a,b,c,d,e] ++ constantFrame ++ rho} =
      some {s with
        pc := pcAfter pc factorTemplate
        stack := [a,b,c,d,e,primaryFactor,pairMask,upperMask,lowerMask] ++ cache ++ rho} := by
  have hbase : rho.length < 1024 := by omega
  have hcap (n : Nat) (hn : n ≤ 27) : rho.length + n < 1024 := by omega
  simp (discharger := omega) [factorTemplate, constantFrame, cache, primaryFactor,
    runInstrSeq, Stepper.runInstr, pcAfter, UInt256.succ, Instr.size,
    List.exchange, List.getElem?_cons_zero, Nat.add_assoc, hrun, hbase, hcap,
    Word.word_toNat_ofNat, Word.literal_eq_ofNat]
  all_goals repeat first | apply And.intro | rfl | decide
#print axioms run_factor
theorem run_key (s : State) (pc : UInt256) (rho : List UInt256)
    (hstack : rho.length ≤ 1019) (hrun : s.halt = .Running) :
    runInstrSeq keyTemplate {s with pc := pc, stack := rho} =
      some {s with pc := pcAfter pc keyTemplate, stack := initialKey :: rho} := by
  have hbase : rho.length < 1024 := by omega
  have hcap (n : Nat) (hn : n ≤ 4) : rho.length + n < 1024 := by omega
  simp (discharger := omega) [keyTemplate, initialKey,
    runInstrSeq, Stepper.runInstr, pcAfter, UInt256.succ, Instr.size,
    List.exchange, List.getElem?_cons_zero, Nat.add_assoc, hrun, hbase, hcap,
    Word.word_toNat_ofNat, Word.literal_eq_ofNat]
  all_goals repeat first | apply And.intro | rfl | decide
#print axioms run_key
def template : List Instr := ((cacheTemplate ++ hashTemplate) ++ factorTemplate) ++ keyTemplate

def resultStack (h0 h1 h2 h3 h4 : UInt256) (rho : List UInt256) : List UInt256 :=
  [initialKey, packed h0, packed h1, packed h2, packed h3, packed h4,
    primaryFactor, pairMask, upperMask, lowerMask] ++ cache ++ [h0,h1,h2,h3,h4] ++ rho

theorem run_actual (s : State) (pc h0 h1 h2 h3 h4 : UInt256) (rho : List UInt256)
    (hstack : rho.length ≤ 991) (hrun : s.halt = .Running) :
    runInstrSeq template {s with pc := pc, stack := [h0,h1,h2,h3,h4] ++ rho} =
      some {s with pc := pcAfter pc template, stack := resultStack h0 h1 h2 h3 h4 rho} := by
  have hr1 := run_cache s pc ([h0,h1,h2,h3,h4] ++ rho) (by simp; omega) hrun
  have hr2 := run_hash s (pcAfter pc cacheTemplate) h0 h1 h2 h3 h4 rho (by omega) hrun
  have h12 := DenseScheduleTrace.runInstrSeq_append_running hr1 (by exact hrun) hr2
  have hr3 := run_factor s (pcAfter (pcAfter pc cacheTemplate) hashTemplate)
    (packed h0) (packed h1) (packed h2) (packed h3) (packed h4)
    ([h0,h1,h2,h3,h4] ++ rho) (by simp; omega) hrun
  have h123 := DenseScheduleTrace.runInstrSeq_append_running h12 (by exact hrun) hr3
  have hr4 := run_key s (pcAfter (pcAfter (pcAfter pc cacheTemplate) hashTemplate) factorTemplate)
    ([packed h0, packed h1, packed h2, packed h3, packed h4,
      primaryFactor, pairMask, upperMask, lowerMask] ++ cache ++ [h0,h1,h2,h3,h4] ++ rho)
    (by simp [cache]; omega) hrun
  have h := DenseScheduleTrace.runInstrSeq_append_running h123 (by exact hrun) hr4
  simpa only [template, resultStack, DenseScheduleTrace.pcAfter_append,
    List.cons_append, List.nil_append, List.append_assoc] using h
#print axioms run_actual

end Challenge.Ripemd160.Submission.Proofs.Bytecode.Table144Bootstrap
