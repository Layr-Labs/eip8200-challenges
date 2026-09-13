import Challenge.Ripemd160.Submission.Proofs.Bytecode.RawLocatedSequence

set_option warningAsError true
set_option maxRecDepth 100000
set_option maxHeartbeats 2000000

namespace Challenge.EvmProof.RawLocatedSequence
open EvmSemantics EvmSemantics.EVM YulEvmCompiler DataStepper

/-- Only the selected executable segment is modeled as instructions. The
preceding and following bytes may contain arbitrary data. Jump validity is
proved independently by the caller. -/
structure Segment where
  code : ByteArray
  preBytes : List UInt8
  instructions : List Instr
  data : List UInt8
  assembly_eq : mkCode (preBytes ++ assembleBytes instructions ++ data) = code

namespace Segment

def instructionPC (p : Segment) (index : Nat) : Nat :=
  (p.preBytes ++ assembleBytes (p.instructions.take index)).length

private theorem split_at_get {α : Type} {xs : List α} {index : Nat} {x : α}
    (hget : xs[index]? = some x) :
    xs = xs.take index ++ x :: xs.drop (index + 1) := by
  obtain ⟨hi, hx⟩ := List.getElem?_eq_some_iff.mp hget
  calc
    xs = xs.take index ++ xs.drop index := (List.take_append_drop index xs).symm
    _ = xs.take index ++ x :: xs.drop (index + 1) := by
      rw [List.drop_eq_getElem_cons hi, hx]

theorem decodeAt_op_index (p : Segment) (index : Nat) (o : Operation)
    (hget : p.instructions[index]? = some (.op o))
    (hopcode : Decode.opcodeOf (Instr.opByte o) = some o)
    (hplain : YulEvmCompiler.plainOp o) :
    Decode.decodeAt p.code (p.instructionPC index) = some (o, none) := by
  have hsplit := split_at_get hget
  rw [← p.assembly_eq]
  unfold instructionPC
  change Decode.decodeAt (mkCode (p.preBytes ++ assembleBytes p.instructions ++ p.data))
    (p.preBytes ++ assembleBytes (List.take index p.instructions)).length = _
  have hbytes : assembleBytes p.instructions =
      assembleBytes (p.instructions.take index) ++ (Instr.op o).bytes ++
        assembleBytes (p.instructions.drop (index + 1)) := by
    calc
      assembleBytes p.instructions = assembleBytes
          (p.instructions.take index ++
            Instr.op o :: p.instructions.drop (index + 1)) :=
        congrArg assembleBytes hsplit
      _ = _ := by
        rw [assembleBytes_append, assembleBytes_cons]
        simp [List.append_assoc]
  rw [hbytes]
  simp only [List.append_assoc]
  simpa only [List.append_assoc] using YulEvmCompiler.decodeAt_op
    (p.preBytes ++ assembleBytes (p.instructions.take index))
    (assembleBytes (p.instructions.drop (index + 1)) ++ p.data) o hopcode hplain

theorem decodeAt_push_index (p : Segment) (index : Nat)
    (width : Fin 33) (value : UInt256)
    (hget : p.instructions[index]? = some (.push width value))
    (hfit : value.toNat < 256 ^ width.val) :
    Decode.decodeAt p.code (p.instructionPC index) =
      some (.Push ⟨width⟩, some (value, width.val)) := by
  have hsplit := split_at_get hget
  rw [← p.assembly_eq]
  unfold instructionPC
  change Decode.decodeAt (mkCode (p.preBytes ++ assembleBytes p.instructions ++ p.data))
    (p.preBytes ++ assembleBytes (List.take index p.instructions)).length = _
  have hbytes : assembleBytes p.instructions =
      assembleBytes (p.instructions.take index) ++
        (Instr.push width value).bytes ++
          assembleBytes (p.instructions.drop (index + 1)) := by
    calc
      assembleBytes p.instructions = assembleBytes
          (p.instructions.take index ++
            Instr.push width value :: p.instructions.drop (index + 1)) :=
        congrArg assembleBytes hsplit
      _ = _ := by
        rw [assembleBytes_append, assembleBytes_cons]
        simp [List.append_assoc]
  rw [hbytes]
  simp only [List.append_assoc]
  simpa only [List.append_assoc] using YulEvmCompiler.decodeAt_push
    (p.preBytes ++ assembleBytes (p.instructions.take index))
    (assembleBytes (p.instructions.drop (index + 1)) ++ p.data) width value hfit


theorem decodes_of (p : Segment) (s : State) (index : Nat) (instruction : Instr)
    (hcode : s.executionEnv.code = p.code)
    (hpc : s.pc.toNat = p.instructionPC index)
    (hget : p.instructions[index]? = some instruction)
    (hwf : WellFormed s.fork instruction) : Decodes s instruction := by
  cases instruction with
  | push width value =>
    rcases hwf with ⟨hfit, havailable⟩
    have hd := p.decodeAt_push_index index width value hget hfit
    change s.decoded = _
    unfold State.decoded
    rw [hcode, hpc, hd]
    simp [havailable]
  | op op =>
    rcases hwf with ⟨hopcode, hplain, havailable⟩
    have hd := p.decodeAt_op_index index op hget hopcode hplain
    change s.decodedOp = _
    unfold State.decodedOp State.decoded
    rw [hcode, hpc, hd]
    simp [havailable]

def located (p : Segment) (fork : Fork) (index : Nat) (instruction : Instr)
    (hget : p.instructions[index]? = some instruction)
    (hwf : WellFormed fork instruction) : Located p.code fork where
  pc := p.instructionPC index
  instruction := instruction
  decodes := by
    intro s hc hf hp
    exact p.decodes_of s index instruction hc hp hget (hf ▸ hwf)

#print axioms located
end Segment
end Challenge.EvmProof.RawLocatedSequence
