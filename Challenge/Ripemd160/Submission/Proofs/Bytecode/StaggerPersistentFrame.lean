import Challenge.Ripemd160.Submission.Proofs.Bytecode.StaggerPersistentTailRaw
import Challenge.Ripemd160.Submission.Proofs.Bytecode.Compression
import Challenge.Ripemd160.Submission.Proofs.Bytecode.Paired144WordRound
set_option warningAsError true
set_option linter.unusedSimpArgs false
namespace Challenge.Ripemd160.Submission.Proofs.Bytecode.StaggerPersistentFrame
open EvmSemantics EvmSemantics.EVM YulEvmCompiler Challenge.EvmProof
open Challenge.EvmProof.Word StackRoundTrace

/-- The persistent loop keeps the six round constants resident on top of the
chaining words for the whole hash, so the per-block bootstrap no longer pushes them. -/
def frame (h : Compression.HashState) (off limit : UInt256) (rho : List UInt256) : List UInt256 :=
  [Paired144WordRound.factorPlusWord, UInt256.ofNat 4294967295, Paired144WordRound.fusedModulusWord 5 7,
   Paired144WordRound.fusedModulusWord 8 5, Paired144WordRound.fusedCoefficientWord 0 3,
   Paired144WordRound.fusedCoefficientWord 0 2,
   ofUInt32 h.h4, ofUInt32 h.h3, ofUInt32 h.h2, ofUInt32 h.h1, ofUInt32 h.h0, off, limit] ++ rho

def coreRest (h : Compression.HashState) (off limit : UInt256) (rho : List UInt256) : List UInt256 :=
  [ofUInt32 h.h3, ofUInt32 h.h2, ofUInt32 h.h1, ofUInt32 h.h0, off, limit] ++ rho

def bind (h : Compression.HashState) (q : StaggerPersistentTailRaw.Input) : StaggerPersistentTailRaw.Input :=
  {q with
    h0 := ofUInt32 h.h0
    h1 := ofUInt32 h.h1
    h2 := ofUInt32 h.h2
    h3 := ofUInt32 h.h3
    h4 := ofUInt32 h.h4
    lower := UInt256.ofNat 0xffffffff
    factor := Paired144WordRound.factorPlusWord
    cache140 := Paired144WordRound.fusedModulusWord 5 7
    cache350 := Paired144WordRound.fusedModulusWord 8 5
    cache310 := Paired144WordRound.fusedCoefficientWord 0 3
    cache190 := Paired144WordRound.fusedCoefficientWord 0 2}
def high (x : UInt256) : UInt32 := toUInt32 (UInt256.shiftRight x (UInt256.ofNat 172))
def combine (h : Compression.HashState) (q : StaggerPersistentTailRaw.Input) : Compression.HashState :=
  {h0 := h.h1 + toUInt32 q.lc + high q.rd,
   h1 := h.h2 + toUInt32 q.ld + high q.re,
   h2 := h.h3 + toUInt32 q.le + high q.ra,
   h3 := h.h4 + toUInt32 q.la + high q.rb,
   h4 := h.h0 + toUInt32 q.lb + high q.rc}

end Challenge.Ripemd160.Submission.Proofs.Bytecode.StaggerPersistentFrame
