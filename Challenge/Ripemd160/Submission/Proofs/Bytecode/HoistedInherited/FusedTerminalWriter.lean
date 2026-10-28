import Challenge.Ripemd160.Submission.Proofs.Bytecode.HoistedInherited.Pc792Writer
set_option warningAsError true
namespace Challenge.Ripemd160.Submission.Proofs.Bytecode.HoistedInherited.FusedTerminalWriter
/-- The PC792 reorder writes exactly the existing masked schedule image. -/
abbrev writerTemplate := HoistedInherited.Pc792Writer.writerTemplate
abbrev run_writer := HoistedInherited.Pc792Writer.run_writer
abbrev run_writer_grow := HoistedInherited.Pc792Writer.run_writer_grow
end Challenge.Ripemd160.Submission.Proofs.Bytecode.HoistedInherited.FusedTerminalWriter
