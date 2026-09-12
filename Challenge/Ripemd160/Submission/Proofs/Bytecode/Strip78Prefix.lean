import Challenge.Ripemd160.Submission.Proofs.Bytecode.PairedAllInlineCoreTrace
set_option warningAsError true
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000
namespace Challenge.Ripemd160.Submission.Proofs.Bytecode.Strip78Prefix
open EvmSemantics EvmSemantics.EVM YulEvmCompiler Challenge.EvmProof
open PairedHelperBooleanTrace (CoreFrame)
open PairedSynthCoreTrace (hoistedAlgorithmFold physicalKey)
open PairedAllInlineCoreTrace
def corePrefix77Chain : CoreChain 727 [.a, .b, .c, .d, .e, .factor, .pair, .upper, .lower] 4628 [.d, .k, .b, .c, .a, .e, .factor, .pair, .upper, .lower] :=
  .cons group0Block (
  .cons inline0Block (
  .cons inline1Block (
  .cons inline2Block (
  .cons inline3Block (
  .cons inline4Block (
  .cons inline5Block (
  .cons inline6Block (
  .cons inline7Block (
  .cons inline8Block (
  .cons inline9Block (
  .cons inline10Block (
  .cons inline11Block (
  .cons inline12Block (
  .cons inline13Block (
  .cons inline14Block (
  .cons inline15Block (
  .cons group16Block (
  .cons inline16Block (
  .cons inline17Block (
  .cons inline18Block (
  .cons inline19Block (
  .cons inline20Block (
  .cons inline21Block (
  .cons inline22Block (
  .cons inline23Block (
  .cons inline24Block (
  .cons inline25Block (
  .cons inline26Block (
  .cons inline27Block (
  .cons inline28Block (
  .cons inline29Block (
  .cons inline30Block (
  .cons inline31Block (
  .cons group32Block (
  .cons inline32Block (
  .cons inline33Block (
  .cons inline34Block (
  .cons inline35Block (
  .cons inline36Block (
  .cons inline37Block (
  .cons inline38Block (
  .cons inline39Block (
  .cons inline40Block (
  .cons inline41Block (
  .cons inline42Block (
  .cons inline43Block (
  .cons inline44Block (
  .cons inline45Block (
  .cons inline46Block (
  .cons inline47Block (
  .cons group48Block (
  .cons inline48Block (
  .cons inline49Block (
  .cons inline50Block (
  .cons inline51Block (
  .cons inline52Block (
  .cons inline53Block (
  .cons inline54Block (
  .cons inline55Block (
  .cons inline56Block (
  .cons inline57Block (
  .cons inline58Block (
  .cons inline59Block (
  .cons inline60Block (
  .cons inline61Block (
  .cons inline62Block (
  .cons inline63Block (
  .cons group64Block (
  .cons inline64Block (
  .cons inline65Block (
  .cons inline66Block (
  .cons inline67Block (
  .cons inline68Block (
  .cons inline69Block (
  .cons inline70Block (
  .cons inline71Block (
  .cons inline72Block (
  .cons inline73Block (
  .cons inline74Block (
  .cons inline75Block (
  .cons inline76Block (
  .cons inline77Block (
  .nil 4628 [.d, .k, .b, .c, .a, .e, .factor, .pair, .upper, .lower])))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))

theorem corePrefix77Chain_eval (memory : ByteArray) (f : CoreFrame) :
    corePrefix77Chain.eval memory f =
      ⟨hoistedAlgorithmFold memory 0 78 f.lane, physicalKey 4⟩ := by
  let f0 : CoreFrame := f
  let f1 : CoreFrame := ⟨hoistedAlgorithmFold memory 0 0 f.lane, physicalKey 0⟩
  let f2 : CoreFrame := ⟨hoistedAlgorithmFold memory 0 1 f.lane, physicalKey 0⟩
  let f3 : CoreFrame := ⟨hoistedAlgorithmFold memory 0 2 f.lane, physicalKey 0⟩
  let f4 : CoreFrame := ⟨hoistedAlgorithmFold memory 0 3 f.lane, physicalKey 0⟩
  let f5 : CoreFrame := ⟨hoistedAlgorithmFold memory 0 4 f.lane, physicalKey 0⟩
  let f6 : CoreFrame := ⟨hoistedAlgorithmFold memory 0 5 f.lane, physicalKey 0⟩
  let f7 : CoreFrame := ⟨hoistedAlgorithmFold memory 0 6 f.lane, physicalKey 0⟩
  let f8 : CoreFrame := ⟨hoistedAlgorithmFold memory 0 7 f.lane, physicalKey 0⟩
  let f9 : CoreFrame := ⟨hoistedAlgorithmFold memory 0 8 f.lane, physicalKey 0⟩
  let f10 : CoreFrame := ⟨hoistedAlgorithmFold memory 0 9 f.lane, physicalKey 0⟩
  let f11 : CoreFrame := ⟨hoistedAlgorithmFold memory 0 10 f.lane, physicalKey 0⟩
  let f12 : CoreFrame := ⟨hoistedAlgorithmFold memory 0 11 f.lane, physicalKey 0⟩
  let f13 : CoreFrame := ⟨hoistedAlgorithmFold memory 0 12 f.lane, physicalKey 0⟩
  let f14 : CoreFrame := ⟨hoistedAlgorithmFold memory 0 13 f.lane, physicalKey 0⟩
  let f15 : CoreFrame := ⟨hoistedAlgorithmFold memory 0 14 f.lane, physicalKey 0⟩
  let f16 : CoreFrame := ⟨hoistedAlgorithmFold memory 0 15 f.lane, physicalKey 0⟩
  let f17 : CoreFrame := ⟨hoistedAlgorithmFold memory 0 16 f.lane, physicalKey 0⟩
  let f18 : CoreFrame := ⟨hoistedAlgorithmFold memory 0 16 f.lane, physicalKey 1⟩
  let f19 : CoreFrame := ⟨hoistedAlgorithmFold memory 0 17 f.lane, physicalKey 1⟩
  let f20 : CoreFrame := ⟨hoistedAlgorithmFold memory 0 18 f.lane, physicalKey 1⟩
  let f21 : CoreFrame := ⟨hoistedAlgorithmFold memory 0 19 f.lane, physicalKey 1⟩
  let f22 : CoreFrame := ⟨hoistedAlgorithmFold memory 0 20 f.lane, physicalKey 1⟩
  let f23 : CoreFrame := ⟨hoistedAlgorithmFold memory 0 21 f.lane, physicalKey 1⟩
  let f24 : CoreFrame := ⟨hoistedAlgorithmFold memory 0 22 f.lane, physicalKey 1⟩
  let f25 : CoreFrame := ⟨hoistedAlgorithmFold memory 0 23 f.lane, physicalKey 1⟩
  let f26 : CoreFrame := ⟨hoistedAlgorithmFold memory 0 24 f.lane, physicalKey 1⟩
  let f27 : CoreFrame := ⟨hoistedAlgorithmFold memory 0 25 f.lane, physicalKey 1⟩
  let f28 : CoreFrame := ⟨hoistedAlgorithmFold memory 0 26 f.lane, physicalKey 1⟩
  let f29 : CoreFrame := ⟨hoistedAlgorithmFold memory 0 27 f.lane, physicalKey 1⟩
  let f30 : CoreFrame := ⟨hoistedAlgorithmFold memory 0 28 f.lane, physicalKey 1⟩
  let f31 : CoreFrame := ⟨hoistedAlgorithmFold memory 0 29 f.lane, physicalKey 1⟩
  let f32 : CoreFrame := ⟨hoistedAlgorithmFold memory 0 30 f.lane, physicalKey 1⟩
  let f33 : CoreFrame := ⟨hoistedAlgorithmFold memory 0 31 f.lane, physicalKey 1⟩
  let f34 : CoreFrame := ⟨hoistedAlgorithmFold memory 0 32 f.lane, physicalKey 1⟩
  let f35 : CoreFrame := ⟨hoistedAlgorithmFold memory 0 32 f.lane, physicalKey 2⟩
  let f36 : CoreFrame := ⟨hoistedAlgorithmFold memory 0 33 f.lane, physicalKey 2⟩
  let f37 : CoreFrame := ⟨hoistedAlgorithmFold memory 0 34 f.lane, physicalKey 2⟩
  let f38 : CoreFrame := ⟨hoistedAlgorithmFold memory 0 35 f.lane, physicalKey 2⟩
  let f39 : CoreFrame := ⟨hoistedAlgorithmFold memory 0 36 f.lane, physicalKey 2⟩
  let f40 : CoreFrame := ⟨hoistedAlgorithmFold memory 0 37 f.lane, physicalKey 2⟩
  let f41 : CoreFrame := ⟨hoistedAlgorithmFold memory 0 38 f.lane, physicalKey 2⟩
  let f42 : CoreFrame := ⟨hoistedAlgorithmFold memory 0 39 f.lane, physicalKey 2⟩
  let f43 : CoreFrame := ⟨hoistedAlgorithmFold memory 0 40 f.lane, physicalKey 2⟩
  let f44 : CoreFrame := ⟨hoistedAlgorithmFold memory 0 41 f.lane, physicalKey 2⟩
  let f45 : CoreFrame := ⟨hoistedAlgorithmFold memory 0 42 f.lane, physicalKey 2⟩
  let f46 : CoreFrame := ⟨hoistedAlgorithmFold memory 0 43 f.lane, physicalKey 2⟩
  let f47 : CoreFrame := ⟨hoistedAlgorithmFold memory 0 44 f.lane, physicalKey 2⟩
  let f48 : CoreFrame := ⟨hoistedAlgorithmFold memory 0 45 f.lane, physicalKey 2⟩
  let f49 : CoreFrame := ⟨hoistedAlgorithmFold memory 0 46 f.lane, physicalKey 2⟩
  let f50 : CoreFrame := ⟨hoistedAlgorithmFold memory 0 47 f.lane, physicalKey 2⟩
  let f51 : CoreFrame := ⟨hoistedAlgorithmFold memory 0 48 f.lane, physicalKey 2⟩
  let f52 : CoreFrame := ⟨hoistedAlgorithmFold memory 0 48 f.lane, physicalKey 3⟩
  let f53 : CoreFrame := ⟨hoistedAlgorithmFold memory 0 49 f.lane, physicalKey 3⟩
  let f54 : CoreFrame := ⟨hoistedAlgorithmFold memory 0 50 f.lane, physicalKey 3⟩
  let f55 : CoreFrame := ⟨hoistedAlgorithmFold memory 0 51 f.lane, physicalKey 3⟩
  let f56 : CoreFrame := ⟨hoistedAlgorithmFold memory 0 52 f.lane, physicalKey 3⟩
  let f57 : CoreFrame := ⟨hoistedAlgorithmFold memory 0 53 f.lane, physicalKey 3⟩
  let f58 : CoreFrame := ⟨hoistedAlgorithmFold memory 0 54 f.lane, physicalKey 3⟩
  let f59 : CoreFrame := ⟨hoistedAlgorithmFold memory 0 55 f.lane, physicalKey 3⟩
  let f60 : CoreFrame := ⟨hoistedAlgorithmFold memory 0 56 f.lane, physicalKey 3⟩
  let f61 : CoreFrame := ⟨hoistedAlgorithmFold memory 0 57 f.lane, physicalKey 3⟩
  let f62 : CoreFrame := ⟨hoistedAlgorithmFold memory 0 58 f.lane, physicalKey 3⟩
  let f63 : CoreFrame := ⟨hoistedAlgorithmFold memory 0 59 f.lane, physicalKey 3⟩
  let f64 : CoreFrame := ⟨hoistedAlgorithmFold memory 0 60 f.lane, physicalKey 3⟩
  let f65 : CoreFrame := ⟨hoistedAlgorithmFold memory 0 61 f.lane, physicalKey 3⟩
  let f66 : CoreFrame := ⟨hoistedAlgorithmFold memory 0 62 f.lane, physicalKey 3⟩
  let f67 : CoreFrame := ⟨hoistedAlgorithmFold memory 0 63 f.lane, physicalKey 3⟩
  let f68 : CoreFrame := ⟨hoistedAlgorithmFold memory 0 64 f.lane, physicalKey 3⟩
  let f69 : CoreFrame := ⟨hoistedAlgorithmFold memory 0 64 f.lane, physicalKey 4⟩
  let f70 : CoreFrame := ⟨hoistedAlgorithmFold memory 0 65 f.lane, physicalKey 4⟩
  let f71 : CoreFrame := ⟨hoistedAlgorithmFold memory 0 66 f.lane, physicalKey 4⟩
  let f72 : CoreFrame := ⟨hoistedAlgorithmFold memory 0 67 f.lane, physicalKey 4⟩
  let f73 : CoreFrame := ⟨hoistedAlgorithmFold memory 0 68 f.lane, physicalKey 4⟩
  let f74 : CoreFrame := ⟨hoistedAlgorithmFold memory 0 69 f.lane, physicalKey 4⟩
  let f75 : CoreFrame := ⟨hoistedAlgorithmFold memory 0 70 f.lane, physicalKey 4⟩
  let f76 : CoreFrame := ⟨hoistedAlgorithmFold memory 0 71 f.lane, physicalKey 4⟩
  let f77 : CoreFrame := ⟨hoistedAlgorithmFold memory 0 72 f.lane, physicalKey 4⟩
  let f78 : CoreFrame := ⟨hoistedAlgorithmFold memory 0 73 f.lane, physicalKey 4⟩
  let f79 : CoreFrame := ⟨hoistedAlgorithmFold memory 0 74 f.lane, physicalKey 4⟩
  let f80 : CoreFrame := ⟨hoistedAlgorithmFold memory 0 75 f.lane, physicalKey 4⟩
  let f81 : CoreFrame := ⟨hoistedAlgorithmFold memory 0 76 f.lane, physicalKey 4⟩
  let f82 : CoreFrame := ⟨hoistedAlgorithmFold memory 0 77 f.lane, physicalKey 4⟩
  let f83 : CoreFrame := ⟨hoistedAlgorithmFold memory 0 78 f.lane, physicalKey 4⟩
  let f84 : CoreFrame := ⟨hoistedAlgorithmFold memory 0 79 f.lane, physicalKey 4⟩
  let f86 : CoreFrame := ⟨hoistedAlgorithmFold memory 0 79 f.lane, physicalKey 4⟩
  have h0 : group0Block.eval memory f0 = f1 := by
    exact group0Block_eval memory f0
  have h1 : inline0Block.eval memory f1 = f2 := by
    exact inline0Block_eval memory (hoistedAlgorithmFold memory 0 0 f.lane)
  have h2 : inline1Block.eval memory f2 = f3 := by
    exact inline1Block_eval memory (hoistedAlgorithmFold memory 0 1 f.lane)
  have h3 : inline2Block.eval memory f3 = f4 := by
    exact inline2Block_eval memory (hoistedAlgorithmFold memory 0 2 f.lane)
  have h4 : inline3Block.eval memory f4 = f5 := by
    exact inline3Block_eval memory (hoistedAlgorithmFold memory 0 3 f.lane)
  have h5 : inline4Block.eval memory f5 = f6 := by
    exact inline4Block_eval memory (hoistedAlgorithmFold memory 0 4 f.lane)
  have h6 : inline5Block.eval memory f6 = f7 := by
    exact inline5Block_eval memory (hoistedAlgorithmFold memory 0 5 f.lane)
  have h7 : inline6Block.eval memory f7 = f8 := by
    exact inline6Block_eval memory (hoistedAlgorithmFold memory 0 6 f.lane)
  have h8 : inline7Block.eval memory f8 = f9 := by
    exact inline7Block_eval memory (hoistedAlgorithmFold memory 0 7 f.lane)
  have h9 : inline8Block.eval memory f9 = f10 := by
    exact inline8Block_eval memory (hoistedAlgorithmFold memory 0 8 f.lane)
  have h10 : inline9Block.eval memory f10 = f11 := by
    exact inline9Block_eval memory (hoistedAlgorithmFold memory 0 9 f.lane)
  have h11 : inline10Block.eval memory f11 = f12 := by
    exact inline10Block_eval memory (hoistedAlgorithmFold memory 0 10 f.lane)
  have h12 : inline11Block.eval memory f12 = f13 := by
    exact inline11Block_eval memory (hoistedAlgorithmFold memory 0 11 f.lane)
  have h13 : inline12Block.eval memory f13 = f14 := by
    exact inline12Block_eval memory (hoistedAlgorithmFold memory 0 12 f.lane)
  have h14 : inline13Block.eval memory f14 = f15 := by
    exact inline13Block_eval memory (hoistedAlgorithmFold memory 0 13 f.lane)
  have h15 : inline14Block.eval memory f15 = f16 := by
    exact inline14Block_eval memory (hoistedAlgorithmFold memory 0 14 f.lane)
  have h16 : inline15Block.eval memory f16 = f17 := by
    exact inline15Block_eval memory (hoistedAlgorithmFold memory 0 15 f.lane)
  have h17 : group16Block.eval memory f17 = f18 := by
    exact group16Block_eval memory f17
  have h18 : inline16Block.eval memory f18 = f19 := by
    exact inline16Block_eval memory (hoistedAlgorithmFold memory 0 16 f.lane)
  have h19 : inline17Block.eval memory f19 = f20 := by
    exact inline17Block_eval memory (hoistedAlgorithmFold memory 0 17 f.lane)
  have h20 : inline18Block.eval memory f20 = f21 := by
    exact inline18Block_eval memory (hoistedAlgorithmFold memory 0 18 f.lane)
  have h21 : inline19Block.eval memory f21 = f22 := by
    exact inline19Block_eval memory (hoistedAlgorithmFold memory 0 19 f.lane)
  have h22 : inline20Block.eval memory f22 = f23 := by
    exact inline20Block_eval memory (hoistedAlgorithmFold memory 0 20 f.lane)
  have h23 : inline21Block.eval memory f23 = f24 := by
    exact inline21Block_eval memory (hoistedAlgorithmFold memory 0 21 f.lane)
  have h24 : inline22Block.eval memory f24 = f25 := by
    exact inline22Block_eval memory (hoistedAlgorithmFold memory 0 22 f.lane)
  have h25 : inline23Block.eval memory f25 = f26 := by
    exact inline23Block_eval memory (hoistedAlgorithmFold memory 0 23 f.lane)
  have h26 : inline24Block.eval memory f26 = f27 := by
    exact inline24Block_eval memory (hoistedAlgorithmFold memory 0 24 f.lane)
  have h27 : inline25Block.eval memory f27 = f28 := by
    exact inline25Block_eval memory (hoistedAlgorithmFold memory 0 25 f.lane)
  have h28 : inline26Block.eval memory f28 = f29 := by
    exact inline26Block_eval memory (hoistedAlgorithmFold memory 0 26 f.lane)
  have h29 : inline27Block.eval memory f29 = f30 := by
    exact inline27Block_eval memory (hoistedAlgorithmFold memory 0 27 f.lane)
  have h30 : inline28Block.eval memory f30 = f31 := by
    exact inline28Block_eval memory (hoistedAlgorithmFold memory 0 28 f.lane)
  have h31 : inline29Block.eval memory f31 = f32 := by
    exact inline29Block_eval memory (hoistedAlgorithmFold memory 0 29 f.lane)
  have h32 : inline30Block.eval memory f32 = f33 := by
    exact inline30Block_eval memory (hoistedAlgorithmFold memory 0 30 f.lane)
  have h33 : inline31Block.eval memory f33 = f34 := by
    exact inline31Block_eval memory (hoistedAlgorithmFold memory 0 31 f.lane)
  have h34 : group32Block.eval memory f34 = f35 := by
    exact group32Block_eval memory f34
  have h35 : inline32Block.eval memory f35 = f36 := by
    exact inline32Block_eval memory (hoistedAlgorithmFold memory 0 32 f.lane)
  have h36 : inline33Block.eval memory f36 = f37 := by
    exact inline33Block_eval memory (hoistedAlgorithmFold memory 0 33 f.lane)
  have h37 : inline34Block.eval memory f37 = f38 := by
    exact inline34Block_eval memory (hoistedAlgorithmFold memory 0 34 f.lane)
  have h38 : inline35Block.eval memory f38 = f39 := by
    exact inline35Block_eval memory (hoistedAlgorithmFold memory 0 35 f.lane)
  have h39 : inline36Block.eval memory f39 = f40 := by
    exact inline36Block_eval memory (hoistedAlgorithmFold memory 0 36 f.lane)
  have h40 : inline37Block.eval memory f40 = f41 := by
    exact inline37Block_eval memory (hoistedAlgorithmFold memory 0 37 f.lane)
  have h41 : inline38Block.eval memory f41 = f42 := by
    exact inline38Block_eval memory (hoistedAlgorithmFold memory 0 38 f.lane)
  have h42 : inline39Block.eval memory f42 = f43 := by
    exact inline39Block_eval memory (hoistedAlgorithmFold memory 0 39 f.lane)
  have h43 : inline40Block.eval memory f43 = f44 := by
    exact inline40Block_eval memory (hoistedAlgorithmFold memory 0 40 f.lane)
  have h44 : inline41Block.eval memory f44 = f45 := by
    exact inline41Block_eval memory (hoistedAlgorithmFold memory 0 41 f.lane)
  have h45 : inline42Block.eval memory f45 = f46 := by
    exact inline42Block_eval memory (hoistedAlgorithmFold memory 0 42 f.lane)
  have h46 : inline43Block.eval memory f46 = f47 := by
    exact inline43Block_eval memory (hoistedAlgorithmFold memory 0 43 f.lane)
  have h47 : inline44Block.eval memory f47 = f48 := by
    exact inline44Block_eval memory (hoistedAlgorithmFold memory 0 44 f.lane)
  have h48 : inline45Block.eval memory f48 = f49 := by
    exact inline45Block_eval memory (hoistedAlgorithmFold memory 0 45 f.lane)
  have h49 : inline46Block.eval memory f49 = f50 := by
    exact inline46Block_eval memory (hoistedAlgorithmFold memory 0 46 f.lane)
  have h50 : inline47Block.eval memory f50 = f51 := by
    exact inline47Block_eval memory (hoistedAlgorithmFold memory 0 47 f.lane)
  have h51 : group48Block.eval memory f51 = f52 := by
    exact group48Block_eval memory f51
  have h52 : inline48Block.eval memory f52 = f53 := by
    exact inline48Block_eval memory (hoistedAlgorithmFold memory 0 48 f.lane)
  have h53 : inline49Block.eval memory f53 = f54 := by
    exact inline49Block_eval memory (hoistedAlgorithmFold memory 0 49 f.lane)
  have h54 : inline50Block.eval memory f54 = f55 := by
    exact inline50Block_eval memory (hoistedAlgorithmFold memory 0 50 f.lane)
  have h55 : inline51Block.eval memory f55 = f56 := by
    exact inline51Block_eval memory (hoistedAlgorithmFold memory 0 51 f.lane)
  have h56 : inline52Block.eval memory f56 = f57 := by
    exact inline52Block_eval memory (hoistedAlgorithmFold memory 0 52 f.lane)
  have h57 : inline53Block.eval memory f57 = f58 := by
    exact inline53Block_eval memory (hoistedAlgorithmFold memory 0 53 f.lane)
  have h58 : inline54Block.eval memory f58 = f59 := by
    exact inline54Block_eval memory (hoistedAlgorithmFold memory 0 54 f.lane)
  have h59 : inline55Block.eval memory f59 = f60 := by
    exact inline55Block_eval memory (hoistedAlgorithmFold memory 0 55 f.lane)
  have h60 : inline56Block.eval memory f60 = f61 := by
    exact inline56Block_eval memory (hoistedAlgorithmFold memory 0 56 f.lane)
  have h61 : inline57Block.eval memory f61 = f62 := by
    exact inline57Block_eval memory (hoistedAlgorithmFold memory 0 57 f.lane)
  have h62 : inline58Block.eval memory f62 = f63 := by
    exact inline58Block_eval memory (hoistedAlgorithmFold memory 0 58 f.lane)
  have h63 : inline59Block.eval memory f63 = f64 := by
    exact inline59Block_eval memory (hoistedAlgorithmFold memory 0 59 f.lane)
  have h64 : inline60Block.eval memory f64 = f65 := by
    exact inline60Block_eval memory (hoistedAlgorithmFold memory 0 60 f.lane)
  have h65 : inline61Block.eval memory f65 = f66 := by
    exact inline61Block_eval memory (hoistedAlgorithmFold memory 0 61 f.lane)
  have h66 : inline62Block.eval memory f66 = f67 := by
    exact inline62Block_eval memory (hoistedAlgorithmFold memory 0 62 f.lane)
  have h67 : inline63Block.eval memory f67 = f68 := by
    exact inline63Block_eval memory (hoistedAlgorithmFold memory 0 63 f.lane)
  have h68 : group64Block.eval memory f68 = f69 := by
    exact group64Block_eval memory f68
  have h69 : inline64Block.eval memory f69 = f70 := by
    exact inline64Block_eval memory (hoistedAlgorithmFold memory 0 64 f.lane)
  have h70 : inline65Block.eval memory f70 = f71 := by
    exact inline65Block_eval memory (hoistedAlgorithmFold memory 0 65 f.lane)
  have h71 : inline66Block.eval memory f71 = f72 := by
    exact inline66Block_eval memory (hoistedAlgorithmFold memory 0 66 f.lane)
  have h72 : inline67Block.eval memory f72 = f73 := by
    exact inline67Block_eval memory (hoistedAlgorithmFold memory 0 67 f.lane)
  have h73 : inline68Block.eval memory f73 = f74 := by
    exact inline68Block_eval memory (hoistedAlgorithmFold memory 0 68 f.lane)
  have h74 : inline69Block.eval memory f74 = f75 := by
    exact inline69Block_eval memory (hoistedAlgorithmFold memory 0 69 f.lane)
  have h75 : inline70Block.eval memory f75 = f76 := by
    exact inline70Block_eval memory (hoistedAlgorithmFold memory 0 70 f.lane)
  have h76 : inline71Block.eval memory f76 = f77 := by
    exact inline71Block_eval memory (hoistedAlgorithmFold memory 0 71 f.lane)
  have h77 : inline72Block.eval memory f77 = f78 := by
    exact inline72Block_eval memory (hoistedAlgorithmFold memory 0 72 f.lane)
  have h78 : inline73Block.eval memory f78 = f79 := by
    exact inline73Block_eval memory (hoistedAlgorithmFold memory 0 73 f.lane)
  have h79 : inline74Block.eval memory f79 = f80 := by
    exact inline74Block_eval memory (hoistedAlgorithmFold memory 0 74 f.lane)
  have h80 : inline75Block.eval memory f80 = f81 := by
    exact inline75Block_eval memory (hoistedAlgorithmFold memory 0 75 f.lane)
  have h81 : inline76Block.eval memory f81 = f82 := by
    exact inline76Block_eval memory (hoistedAlgorithmFold memory 0 76 f.lane)
  have h82 : inline77Block.eval memory f82 = f83 := by
    exact inline77Block_eval memory (hoistedAlgorithmFold memory 0 77 f.lane)
  have hc : CoreEvalCert corePrefix77Chain memory f0 f83 :=
    .cons group0Block _ h0 (
    .cons inline0Block _ h1 (
    .cons inline1Block _ h2 (
    .cons inline2Block _ h3 (
    .cons inline3Block _ h4 (
    .cons inline4Block _ h5 (
    .cons inline5Block _ h6 (
    .cons inline6Block _ h7 (
    .cons inline7Block _ h8 (
    .cons inline8Block _ h9 (
    .cons inline9Block _ h10 (
    .cons inline10Block _ h11 (
    .cons inline11Block _ h12 (
    .cons inline12Block _ h13 (
    .cons inline13Block _ h14 (
    .cons inline14Block _ h15 (
    .cons inline15Block _ h16 (
    .cons group16Block _ h17 (
    .cons inline16Block _ h18 (
    .cons inline17Block _ h19 (
    .cons inline18Block _ h20 (
    .cons inline19Block _ h21 (
    .cons inline20Block _ h22 (
    .cons inline21Block _ h23 (
    .cons inline22Block _ h24 (
    .cons inline23Block _ h25 (
    .cons inline24Block _ h26 (
    .cons inline25Block _ h27 (
    .cons inline26Block _ h28 (
    .cons inline27Block _ h29 (
    .cons inline28Block _ h30 (
    .cons inline29Block _ h31 (
    .cons inline30Block _ h32 (
    .cons inline31Block _ h33 (
    .cons group32Block _ h34 (
    .cons inline32Block _ h35 (
    .cons inline33Block _ h36 (
    .cons inline34Block _ h37 (
    .cons inline35Block _ h38 (
    .cons inline36Block _ h39 (
    .cons inline37Block _ h40 (
    .cons inline38Block _ h41 (
    .cons inline39Block _ h42 (
    .cons inline40Block _ h43 (
    .cons inline41Block _ h44 (
    .cons inline42Block _ h45 (
    .cons inline43Block _ h46 (
    .cons inline44Block _ h47 (
    .cons inline45Block _ h48 (
    .cons inline46Block _ h49 (
    .cons inline47Block _ h50 (
    .cons group48Block _ h51 (
    .cons inline48Block _ h52 (
    .cons inline49Block _ h53 (
    .cons inline50Block _ h54 (
    .cons inline51Block _ h55 (
    .cons inline52Block _ h56 (
    .cons inline53Block _ h57 (
    .cons inline54Block _ h58 (
    .cons inline55Block _ h59 (
    .cons inline56Block _ h60 (
    .cons inline57Block _ h61 (
    .cons inline58Block _ h62 (
    .cons inline59Block _ h63 (
    .cons inline60Block _ h64 (
    .cons inline61Block _ h65 (
    .cons inline62Block _ h66 (
    .cons inline63Block _ h67 (
    .cons group64Block _ h68 (
    .cons inline64Block _ h69 (
    .cons inline65Block _ h70 (
    .cons inline66Block _ h71 (
    .cons inline67Block _ h72 (
    .cons inline68Block _ h73 (
    .cons inline69Block _ h74 (
    .cons inline70Block _ h75 (
    .cons inline71Block _ h76 (
    .cons inline72Block _ h77 (
    .cons inline73Block _ h78 (
    .cons inline74Block _ h79 (
    .cons inline75Block _ h80 (
    .cons inline76Block _ h81 (
    .cons inline77Block _ h82 (
    .nil)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  exact hc.sound


theorem prefix78_eq (memory : ByteArray) (f : CoreFrame) :
    inline78Block.eval memory (corePrefix77Chain.eval memory f) =
      corePrefixChain.eval memory f := by
  rw [corePrefix77Chain_eval, inline78Block_eval, corePrefixChain_eval]
  rfl

#print axioms corePrefix77Chain_eval
end Challenge.Ripemd160.Submission.Proofs.Bytecode.Strip78Prefix
