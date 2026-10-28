import Challenge.Ripemd160.Submission.Proofs.Bytecode.Pc792Writer
set_option warningAsError true
namespace Challenge.Ripemd160.Submission.Proofs.Bytecode.FusedTerminalWriter
/-- The PC792 reorder writes exactly the existing masked schedule image. -/
abbrev writerTemplate := Pc792Writer.writerTemplate
abbrev run_writer := Pc792Writer.run_writer
abbrev run_writer_grow := Pc792Writer.run_writer_grow
end Challenge.Ripemd160.Submission.Proofs.Bytecode.FusedTerminalWriter
