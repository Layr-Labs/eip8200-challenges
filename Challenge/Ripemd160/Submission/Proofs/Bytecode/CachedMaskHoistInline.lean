import Challenge.Ripemd160.Submission.Proofs.Bytecode.CachedMaskInline

set_option warningAsError true
set_option maxRecDepth 40000
set_option maxHeartbeats 6000000

namespace Challenge.Ripemd160.Submission.Proofs.Bytecode.CachedMaskHoistInline

open EvmSemantics EvmSemantics.EVM YulEvmCompiler Challenge.EvmProof
open StackRoundTemplate StackRoundTrace QuadRoundState QuadRoundTemplate

/-- The cached-mask inline quad with each saved-word exchange hoisted across
    the following message-word load. -/
def template (shift : Fin 6) (j : Nat) (p0 p1 p2 p3 : UInt256)
    (r0 r1 r2 r3 : Nat) (constant : UInt256) : List Instr :=
  match j with
  | 0 =>
    [.push 2 (p0),
     .op .MLOAD,
     .op (.Dup ⟨2, by decide⟩),
     .op (.Dup ⟨4, by decide⟩),
     .op .XOR,
     .op (.Dup ⟨5, by decide⟩),
     .op .XOR,
     .op .ADD,
     .op .ADD,
     .op (.Dup ⟨6 + shift.val, by omega⟩),
     .op .AND,
     .op (.Dup ⟨5, by decide⟩),
     .op .MUL,
     .push 1 (UInt256.ofNat (32 - r0)),
     .op .SHR,
     .op (.Dup ⟨4, by decide⟩),
     .op .ADD,
     .op (.Dup ⟨6 + shift.val, by omega⟩),
     .op .AND,
     .op (.Swap ⟨1, by decide⟩),
     .op (.Dup ⟨5, by decide⟩),
     .op .MUL,
     .push 1 (UInt256.ofNat 22),
     .op .SHR,
     .op (.Swap ⟨3, by decide⟩),
     .push 2 (p1),
     .op .MLOAD,
     .op (.Dup ⟨3, by decide⟩),
     .op (.Dup ⟨3, by decide⟩),
     .op .XOR,
     .op (.Dup ⟨6, by decide⟩),
     .op .XOR,
     .op .ADD,
     .op .ADD,
     .op (.Dup ⟨6 + shift.val, by omega⟩),
     .op .AND,
     .op (.Dup ⟨5, by decide⟩),
     .op .MUL,
     .push 1 (UInt256.ofNat (32 - r1)),
     .op .SHR,
     .op (.Dup ⟨3, by decide⟩),
     .op .ADD,
     .op (.Dup ⟨6 + shift.val, by omega⟩),
     .op .AND,
     .op (.Swap ⟨0, by decide⟩),
     .op (.Dup ⟨5, by decide⟩),
     .op .MUL,
     .push 1 (UInt256.ofNat 22),
     .op .SHR,
     .op (.Swap ⟨2, by decide⟩),
     .push 2 (p2),
     .op .MLOAD,
     .op (.Dup ⟨2, by decide⟩),
     .op (.Dup ⟨4, by decide⟩),
     .op .XOR,
     .op (.Dup ⟨5, by decide⟩),
     .op .XOR,
     .op .ADD,
     .op .ADD,
     .op (.Dup ⟨6 + shift.val, by omega⟩),
     .op .AND,
     .op (.Dup ⟨5, by decide⟩),
     .op .MUL,
     .push 1 (UInt256.ofNat (32 - r2)),
     .op .SHR,
     .op (.Dup ⟨4, by decide⟩),
     .op .ADD,
     .op (.Dup ⟨6 + shift.val, by omega⟩),
     .op .AND,
     .op (.Swap ⟨1, by decide⟩),
     .op (.Dup ⟨5, by decide⟩),
     .op .MUL,
     .push 1 (UInt256.ofNat 22),
     .op .SHR,
     .op (.Swap ⟨3, by decide⟩),
     .push 2 (p3),
     .op .MLOAD,
     .op (.Dup ⟨3, by decide⟩),
     .op (.Dup ⟨3, by decide⟩),
     .op .XOR,
     .op (.Dup ⟨6, by decide⟩),
     .op .XOR,
     .op .ADD,
     .op .ADD,
     .op (.Dup ⟨6 + shift.val, by omega⟩),
     .op .AND,
     .op (.Dup ⟨5, by decide⟩),
     .op .MUL,
     .push 1 (UInt256.ofNat (32 - r3)),
     .op .SHR,
     .op (.Dup ⟨3, by decide⟩),
     .op .ADD,
     .op (.Dup ⟨6 + shift.val, by omega⟩),
     .op .AND,
     .op (.Swap ⟨0, by decide⟩),
     .op (.Dup ⟨5, by decide⟩),
     .op .MUL,
     .push 1 (UInt256.ofNat 22),
     .op .SHR,
     .op (.Swap ⟨2, by decide⟩)]
  | 1 =>
    [.push 2 (p0),
     .op .MLOAD,
     .op (.Dup ⟨3, by decide⟩),
     .op (.Dup ⟨5, by decide⟩),
     .op .XOR,
     .op (.Dup ⟨3, by decide⟩),
     .op .AND,
     .op (.Dup ⟨5, by decide⟩),
     .op .XOR,
     .op .ADD,
     .op .ADD,
     .push 4 (constant),
     .op .ADD,
     .op (.Dup ⟨6 + shift.val, by omega⟩),
     .op .AND,
     .op (.Dup ⟨5, by decide⟩),
     .op .MUL,
     .push 1 (UInt256.ofNat (32 - r0)),
     .op .SHR,
     .op (.Dup ⟨4, by decide⟩),
     .op .ADD,
     .op (.Dup ⟨6 + shift.val, by omega⟩),
     .op .AND,
     .op (.Swap ⟨1, by decide⟩),
     .op (.Dup ⟨5, by decide⟩),
     .op .MUL,
     .push 1 (UInt256.ofNat 22),
     .op .SHR,
     .op (.Swap ⟨3, by decide⟩),
     .push 2 (p1),
     .op .MLOAD,
     .op (.Dup ⟨2, by decide⟩),
     .op (.Dup ⟨6, by decide⟩),
     .op .XOR,
     .op (.Dup ⟨4, by decide⟩),
     .op .AND,
     .op (.Dup ⟨6, by decide⟩),
     .op .XOR,
     .op .ADD,
     .op .ADD,
     .push 4 (constant),
     .op .ADD,
     .op (.Dup ⟨6 + shift.val, by omega⟩),
     .op .AND,
     .op (.Dup ⟨5, by decide⟩),
     .op .MUL,
     .push 1 (UInt256.ofNat (32 - r1)),
     .op .SHR,
     .op (.Dup ⟨3, by decide⟩),
     .op .ADD,
     .op (.Dup ⟨6 + shift.val, by omega⟩),
     .op .AND,
     .op (.Swap ⟨0, by decide⟩),
     .op (.Dup ⟨5, by decide⟩),
     .op .MUL,
     .push 1 (UInt256.ofNat 22),
     .op .SHR,
     .op (.Swap ⟨2, by decide⟩),
     .push 2 (p2),
     .op .MLOAD,
     .op (.Dup ⟨3, by decide⟩),
     .op (.Dup ⟨5, by decide⟩),
     .op .XOR,
     .op (.Dup ⟨3, by decide⟩),
     .op .AND,
     .op (.Dup ⟨5, by decide⟩),
     .op .XOR,
     .op .ADD,
     .op .ADD,
     .push 4 (constant),
     .op .ADD,
     .op (.Dup ⟨6 + shift.val, by omega⟩),
     .op .AND,
     .op (.Dup ⟨5, by decide⟩),
     .op .MUL,
     .push 1 (UInt256.ofNat (32 - r2)),
     .op .SHR,
     .op (.Dup ⟨4, by decide⟩),
     .op .ADD,
     .op (.Dup ⟨6 + shift.val, by omega⟩),
     .op .AND,
     .op (.Swap ⟨1, by decide⟩),
     .op (.Dup ⟨5, by decide⟩),
     .op .MUL,
     .push 1 (UInt256.ofNat 22),
     .op .SHR,
     .op (.Swap ⟨3, by decide⟩),
     .push 2 (p3),
     .op .MLOAD,
     .op (.Dup ⟨2, by decide⟩),
     .op (.Dup ⟨6, by decide⟩),
     .op .XOR,
     .op (.Dup ⟨4, by decide⟩),
     .op .AND,
     .op (.Dup ⟨6, by decide⟩),
     .op .XOR,
     .op .ADD,
     .op .ADD,
     .push 4 (constant),
     .op .ADD,
     .op (.Dup ⟨6 + shift.val, by omega⟩),
     .op .AND,
     .op (.Dup ⟨5, by decide⟩),
     .op .MUL,
     .push 1 (UInt256.ofNat (32 - r3)),
     .op .SHR,
     .op (.Dup ⟨3, by decide⟩),
     .op .ADD,
     .op (.Dup ⟨6 + shift.val, by omega⟩),
     .op .AND,
     .op (.Swap ⟨0, by decide⟩),
     .op (.Dup ⟨5, by decide⟩),
     .op .MUL,
     .push 1 (UInt256.ofNat 22),
     .op .SHR,
     .op (.Swap ⟨2, by decide⟩)]
  | 2 =>
    [.push 2 (p0),
     .op .MLOAD,
     .op (.Dup ⟨3, by decide⟩),
     .op .NOT,
     .op (.Dup ⟨3, by decide⟩),
     .op .OR,
     .op (.Dup ⟨5, by decide⟩),
     .op .XOR,
     .op .ADD,
     .op .ADD,
     .push 4 (constant),
     .op .ADD,
     .op (.Dup ⟨6 + shift.val, by omega⟩),
     .op .AND,
     .op (.Dup ⟨5, by decide⟩),
     .op .MUL,
     .push 1 (UInt256.ofNat (32 - r0)),
     .op .SHR,
     .op (.Dup ⟨4, by decide⟩),
     .op .ADD,
     .op (.Dup ⟨6 + shift.val, by omega⟩),
     .op .AND,
     .op (.Swap ⟨1, by decide⟩),
     .op (.Dup ⟨5, by decide⟩),
     .op .MUL,
     .push 1 (UInt256.ofNat 22),
     .op .SHR,
     .op (.Swap ⟨3, by decide⟩),
     .push 2 (p1),
     .op .MLOAD,
     .op (.Dup ⟨2, by decide⟩),
     .op .NOT,
     .op (.Dup ⟨4, by decide⟩),
     .op .OR,
     .op (.Dup ⟨6, by decide⟩),
     .op .XOR,
     .op .ADD,
     .op .ADD,
     .push 4 (constant),
     .op .ADD,
     .op (.Dup ⟨6 + shift.val, by omega⟩),
     .op .AND,
     .op (.Dup ⟨5, by decide⟩),
     .op .MUL,
     .push 1 (UInt256.ofNat (32 - r1)),
     .op .SHR,
     .op (.Dup ⟨3, by decide⟩),
     .op .ADD,
     .op (.Dup ⟨6 + shift.val, by omega⟩),
     .op .AND,
     .op (.Swap ⟨0, by decide⟩),
     .op (.Dup ⟨5, by decide⟩),
     .op .MUL,
     .push 1 (UInt256.ofNat 22),
     .op .SHR,
     .op (.Swap ⟨2, by decide⟩),
     .push 2 (p2),
     .op .MLOAD,
     .op (.Dup ⟨3, by decide⟩),
     .op .NOT,
     .op (.Dup ⟨3, by decide⟩),
     .op .OR,
     .op (.Dup ⟨5, by decide⟩),
     .op .XOR,
     .op .ADD,
     .op .ADD,
     .push 4 (constant),
     .op .ADD,
     .op (.Dup ⟨6 + shift.val, by omega⟩),
     .op .AND,
     .op (.Dup ⟨5, by decide⟩),
     .op .MUL,
     .push 1 (UInt256.ofNat (32 - r2)),
     .op .SHR,
     .op (.Dup ⟨4, by decide⟩),
     .op .ADD,
     .op (.Dup ⟨6 + shift.val, by omega⟩),
     .op .AND,
     .op (.Swap ⟨1, by decide⟩),
     .op (.Dup ⟨5, by decide⟩),
     .op .MUL,
     .push 1 (UInt256.ofNat 22),
     .op .SHR,
     .op (.Swap ⟨3, by decide⟩),
     .push 2 (p3),
     .op .MLOAD,
     .op (.Dup ⟨2, by decide⟩),
     .op .NOT,
     .op (.Dup ⟨4, by decide⟩),
     .op .OR,
     .op (.Dup ⟨6, by decide⟩),
     .op .XOR,
     .op .ADD,
     .op .ADD,
     .push 4 (constant),
     .op .ADD,
     .op (.Dup ⟨6 + shift.val, by omega⟩),
     .op .AND,
     .op (.Dup ⟨5, by decide⟩),
     .op .MUL,
     .push 1 (UInt256.ofNat (32 - r3)),
     .op .SHR,
     .op (.Dup ⟨3, by decide⟩),
     .op .ADD,
     .op (.Dup ⟨6 + shift.val, by omega⟩),
     .op .AND,
     .op (.Swap ⟨0, by decide⟩),
     .op (.Dup ⟨5, by decide⟩),
     .op .MUL,
     .push 1 (UInt256.ofNat 22),
     .op .SHR,
     .op (.Swap ⟨2, by decide⟩)]
  | 3 =>
    [.push 2 (p0),
     .op .MLOAD,
     .op (.Dup ⟨2, by decide⟩),
     .op (.Dup ⟨4, by decide⟩),
     .op .XOR,
     .op (.Dup ⟨5, by decide⟩),
     .op .AND,
     .op (.Dup ⟨4, by decide⟩),
     .op .XOR,
     .op .ADD,
     .op .ADD,
     .push 4 (constant),
     .op .ADD,
     .op (.Dup ⟨6 + shift.val, by omega⟩),
     .op .AND,
     .op (.Dup ⟨5, by decide⟩),
     .op .MUL,
     .push 1 (UInt256.ofNat (32 - r0)),
     .op .SHR,
     .op (.Dup ⟨4, by decide⟩),
     .op .ADD,
     .op (.Dup ⟨6 + shift.val, by omega⟩),
     .op .AND,
     .op (.Swap ⟨1, by decide⟩),
     .op (.Dup ⟨5, by decide⟩),
     .op .MUL,
     .push 1 (UInt256.ofNat 22),
     .op .SHR,
     .op (.Swap ⟨3, by decide⟩),
     .push 2 (p1),
     .op .MLOAD,
     .op (.Dup ⟨3, by decide⟩),
     .op (.Dup ⟨3, by decide⟩),
     .op .XOR,
     .op (.Dup ⟨6, by decide⟩),
     .op .AND,
     .op (.Dup ⟨3, by decide⟩),
     .op .XOR,
     .op .ADD,
     .op .ADD,
     .push 4 (constant),
     .op .ADD,
     .op (.Dup ⟨6 + shift.val, by omega⟩),
     .op .AND,
     .op (.Dup ⟨5, by decide⟩),
     .op .MUL,
     .push 1 (UInt256.ofNat (32 - r1)),
     .op .SHR,
     .op (.Dup ⟨3, by decide⟩),
     .op .ADD,
     .op (.Dup ⟨6 + shift.val, by omega⟩),
     .op .AND,
     .op (.Swap ⟨0, by decide⟩),
     .op (.Dup ⟨5, by decide⟩),
     .op .MUL,
     .push 1 (UInt256.ofNat 22),
     .op .SHR,
     .op (.Swap ⟨2, by decide⟩),
     .push 2 (p2),
     .op .MLOAD,
     .op (.Dup ⟨2, by decide⟩),
     .op (.Dup ⟨4, by decide⟩),
     .op .XOR,
     .op (.Dup ⟨5, by decide⟩),
     .op .AND,
     .op (.Dup ⟨4, by decide⟩),
     .op .XOR,
     .op .ADD,
     .op .ADD,
     .push 4 (constant),
     .op .ADD,
     .op (.Dup ⟨6 + shift.val, by omega⟩),
     .op .AND,
     .op (.Dup ⟨5, by decide⟩),
     .op .MUL,
     .push 1 (UInt256.ofNat (32 - r2)),
     .op .SHR,
     .op (.Dup ⟨4, by decide⟩),
     .op .ADD,
     .op (.Dup ⟨6 + shift.val, by omega⟩),
     .op .AND,
     .op (.Swap ⟨1, by decide⟩),
     .op (.Dup ⟨5, by decide⟩),
     .op .MUL,
     .push 1 (UInt256.ofNat 22),
     .op .SHR,
     .op (.Swap ⟨3, by decide⟩),
     .push 2 (p3),
     .op .MLOAD,
     .op (.Dup ⟨3, by decide⟩),
     .op (.Dup ⟨3, by decide⟩),
     .op .XOR,
     .op (.Dup ⟨6, by decide⟩),
     .op .AND,
     .op (.Dup ⟨3, by decide⟩),
     .op .XOR,
     .op .ADD,
     .op .ADD,
     .push 4 (constant),
     .op .ADD,
     .op (.Dup ⟨6 + shift.val, by omega⟩),
     .op .AND,
     .op (.Dup ⟨5, by decide⟩),
     .op .MUL,
     .push 1 (UInt256.ofNat (32 - r3)),
     .op .SHR,
     .op (.Dup ⟨3, by decide⟩),
     .op .ADD,
     .op (.Dup ⟨6 + shift.val, by omega⟩),
     .op .AND,
     .op (.Swap ⟨0, by decide⟩),
     .op (.Dup ⟨5, by decide⟩),
     .op .MUL,
     .push 1 (UInt256.ofNat 22),
     .op .SHR,
     .op (.Swap ⟨2, by decide⟩)]
  | _ =>
    [.push 2 (p0),
     .op .MLOAD,
     .op (.Dup ⟨4, by decide⟩),
     .op .NOT,
     .op (.Dup ⟨4, by decide⟩),
     .op .OR,
     .op (.Dup ⟨3, by decide⟩),
     .op .XOR,
     .op .ADD,
     .op .ADD,
     .push 4 (constant),
     .op .ADD,
     .op (.Dup ⟨6 + shift.val, by omega⟩),
     .op .AND,
     .op (.Dup ⟨5, by decide⟩),
     .op .MUL,
     .push 1 (UInt256.ofNat (32 - r0)),
     .op .SHR,
     .op (.Dup ⟨4, by decide⟩),
     .op .ADD,
     .op (.Dup ⟨6 + shift.val, by omega⟩),
     .op .AND,
     .op (.Swap ⟨1, by decide⟩),
     .op (.Dup ⟨5, by decide⟩),
     .op .MUL,
     .push 1 (UInt256.ofNat 22),
     .op .SHR,
     .op (.Swap ⟨3, by decide⟩),
     .push 2 (p1),
     .op .MLOAD,
     .op (.Dup ⟨5, by decide⟩),
     .op .NOT,
     .op (.Dup ⟨3, by decide⟩),
     .op .OR,
     .op (.Dup ⟨4, by decide⟩),
     .op .XOR,
     .op .ADD,
     .op .ADD,
     .push 4 (constant),
     .op .ADD,
     .op (.Dup ⟨6 + shift.val, by omega⟩),
     .op .AND,
     .op (.Dup ⟨5, by decide⟩),
     .op .MUL,
     .push 1 (UInt256.ofNat (32 - r1)),
     .op .SHR,
     .op (.Dup ⟨3, by decide⟩),
     .op .ADD,
     .op (.Dup ⟨6 + shift.val, by omega⟩),
     .op .AND,
     .op (.Swap ⟨0, by decide⟩),
     .op (.Dup ⟨5, by decide⟩),
     .op .MUL,
     .push 1 (UInt256.ofNat 22),
     .op .SHR,
     .op (.Swap ⟨2, by decide⟩),
     .push 2 (p2),
     .op .MLOAD,
     .op (.Dup ⟨4, by decide⟩),
     .op .NOT,
     .op (.Dup ⟨4, by decide⟩),
     .op .OR,
     .op (.Dup ⟨3, by decide⟩),
     .op .XOR,
     .op .ADD,
     .op .ADD,
     .push 4 (constant),
     .op .ADD,
     .op (.Dup ⟨6 + shift.val, by omega⟩),
     .op .AND,
     .op (.Dup ⟨5, by decide⟩),
     .op .MUL,
     .push 1 (UInt256.ofNat (32 - r2)),
     .op .SHR,
     .op (.Dup ⟨4, by decide⟩),
     .op .ADD,
     .op (.Dup ⟨6 + shift.val, by omega⟩),
     .op .AND,
     .op (.Swap ⟨1, by decide⟩),
     .op (.Dup ⟨5, by decide⟩),
     .op .MUL,
     .push 1 (UInt256.ofNat 22),
     .op .SHR,
     .op (.Swap ⟨3, by decide⟩),
     .push 2 (p3),
     .op .MLOAD,
     .op (.Dup ⟨5, by decide⟩),
     .op .NOT,
     .op (.Dup ⟨3, by decide⟩),
     .op .OR,
     .op (.Dup ⟨4, by decide⟩),
     .op .XOR,
     .op .ADD,
     .op .ADD,
     .push 4 (constant),
     .op .ADD,
     .op (.Dup ⟨6 + shift.val, by omega⟩),
     .op .AND,
     .op (.Dup ⟨5, by decide⟩),
     .op .MUL,
     .push 1 (UInt256.ofNat (32 - r3)),
     .op .SHR,
     .op (.Dup ⟨3, by decide⟩),
     .op .ADD,
     .op (.Dup ⟨6 + shift.val, by omega⟩),
     .op .AND,
     .op (.Swap ⟨0, by decide⟩),
     .op (.Dup ⟨5, by decide⟩),
     .op .MUL,
     .push 1 (UInt256.ofNat 22),
     .op .SHR,
     .op (.Swap ⟨2, by decide⟩)]


set_option linter.unusedSimpArgs false in
theorem left_equiv (j : Nat) (hj : j < 5)
    (s : State) (startPC p0 p1 p2 p3 : UInt256)
    (r0 r1 r2 r3 : Nat) (constant : UInt256)
    (working : Compression.EvmWorking) (rho : List UInt256)
    (hstack : rho.length < 1006) (hrun : s.halt = .Running) :
    runInstrSeq (template 0 j p0 p1 p2 p3 r0 r1 r2 r3 constant)
      (roundEntry s startPC working.a working.b working.c working.d working.e
        (factor :: mask :: rho)) =
    Option.map
      (fun out => {out with pc := pcAfter startPC (template 0 j p0 p1 p2 p3 r0 r1 r2 r3 constant)})
      (runInstrSeq (CachedMaskInline.template 0 j p0 p1 p2 p3 r0 r1 r2 r3 constant)
        (roundEntry s startPC working.a working.b working.c working.d working.e
          (factor :: mask :: rho))) := by
  have hcap (m : Nat) (hm : m ≤ 17) : rho.length + m < 1024 := by omega
  have hadd (u v : UInt256) : u.add v = u + v := rfl
  have hassoc (u v w : UInt256) : (u + v) + w = u + (v + w) := by
    apply Word.word_ext
    change ((u.val + v.val) + w.val).val = (u.val + (v.val + w.val)).val
    simp [Fin.add_def, Nat.add_assoc]
  have hpc (u : UInt256) (a b : Nat) :
      (u + UInt256.ofNat a) + UInt256.ofNat b =
        u + UInt256.ofNat (a + b) := by
    rw [hassoc, Word.ofNat_add_mod]
  letI : Std.Associative (fun (u v : UInt256) => u + v) := ⟨hassoc⟩
  letI : Std.Commutative (fun (u v : UInt256) => u + v) := ⟨Word.word_add_comm⟩
  interval_cases j <;> simp (config := { maxSteps := 5000000 })
    [template, CachedMaskInline.template,
     roundEntry, roundWords, mask,
     runInstrSeq, Stepper.runInstr, pcAfter, List.exchange,
     hrun, hcap, UInt256.succ, Instr.size, Instr.size_op, Instr.size_push,
     State.activeWordsAfterUInt256, hadd, hpc,
     Word.ofNat_add_mod, Word.word_toNat_ofNat, Nat.add_assoc] <;>
    (repeat' apply And.intro) <;> ac_rfl

set_option linter.unusedSimpArgs false in
theorem right_equiv (j : Nat) (hj : j < 5)
    (s : State) (startPC p0 p1 p2 p3 : UInt256)
    (r0 r1 r2 r3 : Nat) (constant : UInt256)
    (working : Compression.EvmWorking) (a b c d e : UInt256)
    (rho : List UInt256)
    (hstack : rho.length < 1001) (hrun : s.halt = .Running) :
    runInstrSeq (template 5 j p0 p1 p2 p3 r0 r1 r2 r3 constant)
      (roundEntry s startPC working.a working.b working.c working.d working.e
        (factor :: a :: b :: c :: d :: e :: mask :: rho)) =
    Option.map
      (fun out => {out with pc := pcAfter startPC (template 5 j p0 p1 p2 p3 r0 r1 r2 r3 constant)})
      (runInstrSeq (CachedMaskInline.template 5 j p0 p1 p2 p3 r0 r1 r2 r3 constant)
        (roundEntry s startPC working.a working.b working.c working.d working.e
          (factor :: a :: b :: c :: d :: e :: mask :: rho))) := by
  have hcap (m : Nat) (hm : m ≤ 22) : rho.length + m < 1024 := by omega
  have hadd (u v : UInt256) : u.add v = u + v := rfl
  have hassoc (u v w : UInt256) : (u + v) + w = u + (v + w) := by
    apply Word.word_ext
    change ((u.val + v.val) + w.val).val = (u.val + (v.val + w.val)).val
    simp [Fin.add_def, Nat.add_assoc]
  have hpc (u : UInt256) (a b : Nat) :
      (u + UInt256.ofNat a) + UInt256.ofNat b =
        u + UInt256.ofNat (a + b) := by
    rw [hassoc, Word.ofNat_add_mod]
  letI : Std.Associative (fun (u v : UInt256) => u + v) := ⟨hassoc⟩
  letI : Std.Commutative (fun (u v : UInt256) => u + v) := ⟨Word.word_add_comm⟩
  interval_cases j <;> simp (config := { maxSteps := 5000000 })
    [template, CachedMaskInline.template,
     roundEntry, roundWords, mask,
     runInstrSeq, Stepper.runInstr, pcAfter, List.exchange,
     hrun, hcap, UInt256.succ, Instr.size, Instr.size_op, Instr.size_push,
     State.activeWordsAfterUInt256, hadd, hpc,
     Word.ofNat_add_mod, Word.word_toNat_ofNat, Nat.add_assoc] <;>
    (repeat' apply And.intro) <;> ac_rfl

theorem run_left (j : Nat) (hj : j < 5)
    (s : State) (startPC p0 p1 p2 p3 : UInt256) (r0 r1 r2 r3 : Nat)
    (working : Compression.EvmWorking) (constant : UInt256) (rho : List UInt256)
    (hzero : j = 0 → constant = 0)
    (hstack : rho.length < 1006) (hrun : s.halt = .Running)
    (hrot0 : r0 ≤ 32) (hrot1 : r1 ≤ 32)
    (hrot2 : r2 ≤ 32) (hrot3 : r3 ≤ 32) :
    runInstrSeq (template 0 j p0 p1 p2 p3 r0 r1 r2 r3 constant)
      (roundEntry s startPC working.a working.b working.c working.d working.e
        (factor :: mask :: rho)) =
      some {s with
        pc := pcAfter startPC (template 0 j p0 p1 p2 p3 r0 r1 r2 r3 constant)
        stack := roundWords (quadWorking s working j p0 p1 p2 p3
          r0 r1 r2 r3 constant) ++ [factor, mask] ++ rho
        activeWords := quadActiveWordsAfterUInt256_4 s
          p0.toNat p1.toNat p2.toNat p3.toNat} := by
  rw [left_equiv j hj s startPC p0 p1 p2 p3 r0 r1 r2 r3
    constant working rho hstack hrun]
  rw [CachedMaskInline.run_left j hj s startPC p0 p1 p2 p3 r0 r1 r2 r3
    working constant rho hzero hstack hrun hrot0 hrot1 hrot2 hrot3]
  rfl

theorem run_right (j : Nat) (hj : j < 5)
    (s : State) (startPC p0 p1 p2 p3 : UInt256) (r0 r1 r2 r3 : Nat)
    (working : Compression.EvmWorking) (constant a b c d e : UInt256)
    (rho : List UInt256) (hzero : j = 0 → constant = 0)
    (hstack : rho.length < 1001) (hrun : s.halt = .Running)
    (hrot0 : r0 ≤ 32) (hrot1 : r1 ≤ 32)
    (hrot2 : r2 ≤ 32) (hrot3 : r3 ≤ 32) :
    runInstrSeq (template 5 j p0 p1 p2 p3 r0 r1 r2 r3 constant)
      (roundEntry s startPC working.a working.b working.c working.d working.e
        (factor :: a :: b :: c :: d :: e :: mask :: rho)) =
      some {s with
        pc := pcAfter startPC (template 5 j p0 p1 p2 p3 r0 r1 r2 r3 constant)
        stack := roundWords (quadWorking s working j p0 p1 p2 p3
          r0 r1 r2 r3 constant) ++ [factor, a, b, c, d, e, mask] ++ rho
        activeWords := quadActiveWordsAfterUInt256_4 s
          p0.toNat p1.toNat p2.toNat p3.toNat} := by
  rw [right_equiv j hj s startPC p0 p1 p2 p3 r0 r1 r2 r3
    constant working a b c d e rho hstack hrun]
  rw [CachedMaskInline.run_right j hj s startPC p0 p1 p2 p3 r0 r1 r2 r3
    working constant a b c d e rho hzero hstack hrun hrot0 hrot1 hrot2 hrot3]
  rfl

set_option linter.unusedSimpArgs false in
theorem advances (shift : Fin 6) (j : Nat) (hj : j < 5)
    (p0 p1 p2 p3 : UInt256) (r0 r1 r2 r3 : Nat) (constant : UInt256) :
    ∀ instruction ∈ template shift j p0 p1 p2 p3 r0 r1 r2 r3 constant,
      PairMultiplyLift.Advances instruction := by
  intro instruction hmem
  interval_cases j <;> simp [template] at hmem <;>
    simp_all [PairMultiplyLift.Advances, SharedCallTrace.Advances] <;>
    aesop (add safe constructors StraightLine)

#print axioms left_equiv
#print axioms right_equiv
#print axioms run_left
#print axioms run_right
#print axioms advances

end Challenge.Ripemd160.Submission.Proofs.Bytecode.CachedMaskHoistInline
