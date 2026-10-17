import Challenge.Ripemd160.Submission.Proofs.Bytecode.PatternedWordData
import YulEvmCompiler.Instr
set_option warningAsError true
set_option maxRecDepth 100000
set_option maxHeartbeats 2000000
set_option linter.unusedSimpArgs false
namespace RetainedIntegration105.LiteralBindings
open EvmSemantics EvmSemantics.EVM YulEvmCompiler
open Challenge.Ripemd160.Submission.Proofs.Bytecode
def bytes0 : List UInt8 := [127, 7, 44, 81, 118, 155, 192, 229, 10, 47, 84, 121, 158, 195, 232, 13, 50, 87, 124, 161, 198, 235, 16, 53, 90, 127, 164, 201, 238, 19, 56, 93, 130, 24]
def template0 : List Instr := [.push ⟨32, by decide⟩ (PatternedWordData.expectedWordAt 0), .op .XOR]
theorem binding0 : assembleBytes template0 = bytes0 := by
  simp only [template0, PatternedWordData.expectedWordAt_0]
  decide

def bytes31 : List UInt8 := [127, 136, 173, 210, 247, 28, 65, 102, 139, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 97, 3, 224, 53, 24, 23]
def template31 : List Instr := [.push ⟨32, by decide⟩ (PatternedWordData.expectedWordAt 31), .push ⟨2, by decide⟩ (UInt256.ofNat 992), .op .CALLDATALOAD, .op .XOR, .op .OR]
theorem binding31 : assembleBytes template31 = bytes31 := by
  simp only [template31, PatternedWordData.expectedWordAt_31]
  decide

def bytes30 : List UInt8 := [127, 232, 13, 50, 87, 124, 161, 198, 235, 16, 53, 90, 127, 164, 201, 238, 19, 56, 93, 130, 167, 204, 241, 22, 59, 96, 133, 170, 207, 244, 25, 62, 99, 97, 3, 192, 53, 24, 23]
def template30 : List Instr := [.push ⟨32, by decide⟩ (PatternedWordData.expectedWordAt 30), .push ⟨2, by decide⟩ (UInt256.ofNat 960), .op .CALLDATALOAD, .op .XOR, .op .OR]
theorem binding30 : assembleBytes template30 = bytes30 := by
  simp only [template30, PatternedWordData.expectedWordAt_30]
  decide

def bytes29 : List UInt8 := [127, 72, 109, 146, 183, 220, 1, 38, 75, 112, 149, 186, 223, 4, 41, 78, 115, 152, 189, 226, 7, 44, 81, 118, 155, 192, 229, 10, 47, 84, 121, 158, 195, 97, 3, 160, 53, 24, 23]
def template29 : List Instr := [.push ⟨32, by decide⟩ (PatternedWordData.expectedWordAt 29), .push ⟨2, by decide⟩ (UInt256.ofNat 928), .op .CALLDATALOAD, .op .XOR, .op .OR]
theorem binding29 : assembleBytes template29 = bytes29 := by
  simp only [template29, PatternedWordData.expectedWordAt_29]
  decide

def bytes28 : List UInt8 := [127, 168, 205, 242, 23, 60, 97, 134, 171, 208, 245, 26, 63, 100, 137, 174, 211, 248, 29, 66, 103, 140, 177, 214, 251, 32, 69, 106, 143, 180, 217, 254, 35, 97, 3, 128, 53, 24, 23]
def template28 : List Instr := [.push ⟨32, by decide⟩ (PatternedWordData.expectedWordAt 28), .push ⟨2, by decide⟩ (UInt256.ofNat 896), .op .CALLDATALOAD, .op .XOR, .op .OR]
theorem binding28 : assembleBytes template28 = bytes28 := by
  simp only [template28, PatternedWordData.expectedWordAt_28]
  decide

def bytes27 : List UInt8 := [127, 8, 45, 82, 119, 156, 193, 230, 11, 48, 85, 122, 159, 196, 233, 14, 51, 88, 125, 162, 199, 236, 17, 54, 91, 128, 165, 202, 239, 20, 57, 94, 131, 97, 3, 96, 53, 24, 23]
def template27 : List Instr := [.push ⟨32, by decide⟩ (PatternedWordData.expectedWordAt 27), .push ⟨2, by decide⟩ (UInt256.ofNat 864), .op .CALLDATALOAD, .op .XOR, .op .OR]
theorem binding27 : assembleBytes template27 = bytes27 := by
  simp only [template27, PatternedWordData.expectedWordAt_27]
  decide

def bytes26 : List UInt8 := [127, 104, 141, 178, 215, 252, 33, 70, 107, 144, 181, 218, 255, 36, 73, 110, 147, 184, 221, 2, 39, 76, 113, 150, 187, 224, 5, 42, 79, 116, 153, 190, 227, 97, 3, 64, 53, 24, 23]
def template26 : List Instr := [.push ⟨32, by decide⟩ (PatternedWordData.expectedWordAt 26), .push ⟨2, by decide⟩ (UInt256.ofNat 832), .op .CALLDATALOAD, .op .XOR, .op .OR]
theorem binding26 : assembleBytes template26 = bytes26 := by
  simp only [template26, PatternedWordData.expectedWordAt_26]
  decide

def bytes25 : List UInt8 := [127, 200, 237, 18, 55, 92, 129, 166, 203, 240, 21, 58, 95, 132, 169, 206, 243, 24, 61, 98, 135, 172, 209, 246, 27, 64, 101, 138, 175, 212, 249, 30, 67, 97, 3, 32, 53, 24, 23]
def template25 : List Instr := [.push ⟨32, by decide⟩ (PatternedWordData.expectedWordAt 25), .push ⟨2, by decide⟩ (UInt256.ofNat 800), .op .CALLDATALOAD, .op .XOR, .op .OR]
theorem binding25 : assembleBytes template25 = bytes25 := by
  simp only [template25, PatternedWordData.expectedWordAt_25]
  decide

def bytes24 : List UInt8 := [127, 40, 77, 114, 151, 188, 225, 6, 43, 80, 117, 154, 191, 228, 9, 46, 83, 120, 157, 194, 231, 12, 49, 86, 123, 160, 197, 234, 15, 52, 89, 126, 163, 97, 3, 0, 53, 24, 23]
def template24 : List Instr := [.push ⟨32, by decide⟩ (PatternedWordData.expectedWordAt 24), .push ⟨2, by decide⟩ (UInt256.ofNat 768), .op .CALLDATALOAD, .op .XOR, .op .OR]
theorem binding24 : assembleBytes template24 = bytes24 := by
  simp only [template24, PatternedWordData.expectedWordAt_24]
  decide

def bytes23 : List UInt8 := [127, 125, 162, 199, 236, 17, 54, 91, 128, 165, 202, 239, 20, 57, 94, 131, 168, 205, 253, 34, 71, 108, 145, 182, 219, 0, 37, 74, 111, 148, 185, 222, 3, 97, 2, 224, 53, 24, 23]
def template23 : List Instr := [.push ⟨32, by decide⟩ (PatternedWordData.expectedWordAt 23), .push ⟨2, by decide⟩ (UInt256.ofNat 736), .op .CALLDATALOAD, .op .XOR, .op .OR]
theorem binding23 : assembleBytes template23 = bytes23 := by
  simp only [template23, PatternedWordData.expectedWordAt_23]
  decide

def bytes22 : List UInt8 := [127, 221, 2, 39, 76, 113, 150, 187, 224, 5, 42, 79, 116, 153, 190, 227, 8, 45, 82, 119, 156, 193, 230, 11, 48, 85, 122, 159, 196, 233, 14, 51, 88, 97, 2, 192, 53, 24, 23]
def template22 : List Instr := [.push ⟨32, by decide⟩ (PatternedWordData.expectedWordAt 22), .push ⟨2, by decide⟩ (UInt256.ofNat 704), .op .CALLDATALOAD, .op .XOR, .op .OR]
theorem binding22 : assembleBytes template22 = bytes22 := by
  simp only [template22, PatternedWordData.expectedWordAt_22]
  decide

def bytes21 : List UInt8 := [127, 61, 98, 135, 172, 209, 246, 27, 64, 101, 138, 175, 212, 249, 30, 67, 104, 141, 178, 215, 252, 33, 70, 107, 144, 181, 218, 255, 36, 73, 110, 147, 184, 97, 2, 160, 53, 24, 23]
def template21 : List Instr := [.push ⟨32, by decide⟩ (PatternedWordData.expectedWordAt 21), .push ⟨2, by decide⟩ (UInt256.ofNat 672), .op .CALLDATALOAD, .op .XOR, .op .OR]
theorem binding21 : assembleBytes template21 = bytes21 := by
  simp only [template21, PatternedWordData.expectedWordAt_21]
  decide

def bytes20 : List UInt8 := [127, 157, 194, 231, 12, 49, 86, 123, 160, 197, 234, 15, 52, 89, 126, 163, 200, 237, 18, 55, 92, 129, 166, 203, 240, 21, 58, 95, 132, 169, 206, 243, 24, 97, 2, 128, 53, 24, 23]
def template20 : List Instr := [.push ⟨32, by decide⟩ (PatternedWordData.expectedWordAt 20), .push ⟨2, by decide⟩ (UInt256.ofNat 640), .op .CALLDATALOAD, .op .XOR, .op .OR]
theorem binding20 : assembleBytes template20 = bytes20 := by
  simp only [template20, PatternedWordData.expectedWordAt_20]
  decide

def bytes19 : List UInt8 := [127, 253, 34, 71, 108, 145, 182, 219, 0, 37, 74, 111, 148, 185, 222, 3, 40, 77, 114, 151, 188, 225, 6, 43, 80, 117, 154, 191, 228, 9, 46, 83, 120, 97, 2, 96, 53, 24, 23]
def template19 : List Instr := [.push ⟨32, by decide⟩ (PatternedWordData.expectedWordAt 19), .push ⟨2, by decide⟩ (UInt256.ofNat 608), .op .CALLDATALOAD, .op .XOR, .op .OR]
theorem binding19 : assembleBytes template19 = bytes19 := by
  simp only [template19, PatternedWordData.expectedWordAt_19]
  decide

def bytes18 : List UInt8 := [127, 93, 130, 167, 204, 241, 22, 59, 96, 133, 170, 207, 244, 25, 62, 99, 136, 173, 210, 247, 28, 65, 102, 139, 176, 213, 250, 31, 68, 105, 142, 179, 216, 97, 2, 64, 53, 24, 23]
def template18 : List Instr := [.push ⟨32, by decide⟩ (PatternedWordData.expectedWordAt 18), .push ⟨2, by decide⟩ (UInt256.ofNat 576), .op .CALLDATALOAD, .op .XOR, .op .OR]
theorem binding18 : assembleBytes template18 = bytes18 := by
  simp only [template18, PatternedWordData.expectedWordAt_18]
  decide

def bytes17 : List UInt8 := [127, 189, 226, 7, 44, 81, 118, 155, 192, 229, 10, 47, 84, 121, 158, 195, 232, 13, 50, 87, 124, 161, 198, 235, 16, 53, 90, 127, 164, 201, 238, 19, 56, 97, 2, 32, 53, 24, 23]
def template17 : List Instr := [.push ⟨32, by decide⟩ (PatternedWordData.expectedWordAt 17), .push ⟨2, by decide⟩ (UInt256.ofNat 544), .op .CALLDATALOAD, .op .XOR, .op .OR]
theorem binding17 : assembleBytes template17 = bytes17 := by
  simp only [template17, PatternedWordData.expectedWordAt_17]
  decide

def bytes16 : List UInt8 := [127, 29, 66, 103, 140, 177, 214, 251, 32, 69, 106, 143, 180, 217, 254, 35, 72, 109, 146, 183, 220, 1, 38, 75, 112, 149, 186, 223, 4, 41, 78, 115, 152, 97, 2, 0, 53, 24, 23]
def template16 : List Instr := [.push ⟨32, by decide⟩ (PatternedWordData.expectedWordAt 16), .push ⟨2, by decide⟩ (UInt256.ofNat 512), .op .CALLDATALOAD, .op .XOR, .op .OR]
theorem binding16 : assembleBytes template16 = bytes16 := by
  simp only [template16, PatternedWordData.expectedWordAt_16]
  decide

def bytes15 : List UInt8 := [127, 114, 151, 188, 225, 6, 43, 80, 117, 154, 191, 228, 9, 46, 83, 120, 157, 194, 231, 12, 49, 86, 123, 171, 208, 245, 26, 63, 100, 137, 174, 211, 248, 97, 1, 224, 53, 24, 23]
def template15 : List Instr := [.push ⟨32, by decide⟩ (PatternedWordData.expectedWordAt 15), .push ⟨2, by decide⟩ (UInt256.ofNat 480), .op .CALLDATALOAD, .op .XOR, .op .OR]
theorem binding15 : assembleBytes template15 = bytes15 := by
  simp only [template15, PatternedWordData.expectedWordAt_15]
  decide

def bytes14 : List UInt8 := [127, 210, 247, 28, 65, 102, 139, 176, 213, 250, 31, 68, 105, 142, 179, 216, 253, 34, 71, 108, 145, 182, 219, 0, 37, 74, 111, 148, 185, 222, 3, 40, 77, 97, 1, 192, 53, 24, 23]
def template14 : List Instr := [.push ⟨32, by decide⟩ (PatternedWordData.expectedWordAt 14), .push ⟨2, by decide⟩ (UInt256.ofNat 448), .op .CALLDATALOAD, .op .XOR, .op .OR]
theorem binding14 : assembleBytes template14 = bytes14 := by
  simp only [template14, PatternedWordData.expectedWordAt_14]
  decide

def bytes13 : List UInt8 := [127, 50, 87, 124, 161, 198, 235, 16, 53, 90, 127, 164, 201, 238, 19, 56, 93, 130, 167, 204, 241, 22, 59, 96, 133, 170, 207, 244, 25, 62, 99, 136, 173, 97, 1, 160, 53, 24, 23]
def template13 : List Instr := [.push ⟨32, by decide⟩ (PatternedWordData.expectedWordAt 13), .push ⟨2, by decide⟩ (UInt256.ofNat 416), .op .CALLDATALOAD, .op .XOR, .op .OR]
theorem binding13 : assembleBytes template13 = bytes13 := by
  simp only [template13, PatternedWordData.expectedWordAt_13]
  decide

def bytes12 : List UInt8 := [127, 146, 183, 220, 1, 38, 75, 112, 149, 186, 223, 4, 41, 78, 115, 152, 189, 226, 7, 44, 81, 118, 155, 192, 229, 10, 47, 84, 121, 158, 195, 232, 13, 97, 1, 128, 53, 24, 23]
def template12 : List Instr := [.push ⟨32, by decide⟩ (PatternedWordData.expectedWordAt 12), .push ⟨2, by decide⟩ (UInt256.ofNat 384), .op .CALLDATALOAD, .op .XOR, .op .OR]
theorem binding12 : assembleBytes template12 = bytes12 := by
  simp only [template12, PatternedWordData.expectedWordAt_12]
  decide

def bytes11 : List UInt8 := [127, 242, 23, 60, 97, 134, 171, 208, 245, 26, 63, 100, 137, 174, 211, 248, 29, 66, 103, 140, 177, 214, 251, 32, 69, 106, 143, 180, 217, 254, 35, 72, 109, 97, 1, 96, 53, 24, 23]
def template11 : List Instr := [.push ⟨32, by decide⟩ (PatternedWordData.expectedWordAt 11), .push ⟨2, by decide⟩ (UInt256.ofNat 352), .op .CALLDATALOAD, .op .XOR, .op .OR]
theorem binding11 : assembleBytes template11 = bytes11 := by
  simp only [template11, PatternedWordData.expectedWordAt_11]
  decide

def bytes10 : List UInt8 := [127, 82, 119, 156, 193, 230, 11, 48, 85, 122, 159, 196, 233, 14, 51, 88, 125, 162, 199, 236, 17, 54, 91, 128, 165, 202, 239, 20, 57, 94, 131, 168, 205, 97, 1, 64, 53, 24, 23]
def template10 : List Instr := [.push ⟨32, by decide⟩ (PatternedWordData.expectedWordAt 10), .push ⟨2, by decide⟩ (UInt256.ofNat 320), .op .CALLDATALOAD, .op .XOR, .op .OR]
theorem binding10 : assembleBytes template10 = bytes10 := by
  simp only [template10, PatternedWordData.expectedWordAt_10]
  decide

def bytes9 : List UInt8 := [127, 178, 215, 252, 33, 70, 107, 144, 181, 218, 255, 36, 73, 110, 147, 184, 221, 2, 39, 76, 113, 150, 187, 224, 5, 42, 79, 116, 153, 190, 227, 8, 45, 97, 1, 32, 53, 24, 23]
def template9 : List Instr := [.push ⟨32, by decide⟩ (PatternedWordData.expectedWordAt 9), .push ⟨2, by decide⟩ (UInt256.ofNat 288), .op .CALLDATALOAD, .op .XOR, .op .OR]
theorem binding9 : assembleBytes template9 = bytes9 := by
  simp only [template9, PatternedWordData.expectedWordAt_9]
  decide

def bytes8 : List UInt8 := [127, 18, 55, 92, 129, 166, 203, 240, 21, 58, 95, 132, 169, 206, 243, 24, 61, 98, 135, 172, 209, 246, 27, 64, 101, 138, 175, 212, 249, 30, 67, 104, 141, 97, 1, 0, 53, 24, 23]
def template8 : List Instr := [.push ⟨32, by decide⟩ (PatternedWordData.expectedWordAt 8), .push ⟨2, by decide⟩ (UInt256.ofNat 256), .op .CALLDATALOAD, .op .XOR, .op .OR]
theorem binding8 : assembleBytes template8 = bytes8 := by
  simp only [template8, PatternedWordData.expectedWordAt_8]
  decide

def bytes7 : List UInt8 := [127, 103, 140, 177, 214, 251, 32, 69, 106, 143, 180, 217, 254, 35, 72, 109, 146, 183, 220, 1, 38, 75, 112, 149, 186, 223, 4, 41, 89, 126, 163, 200, 237, 96, 224, 53, 24, 23]
def template7 : List Instr := [.push ⟨32, by decide⟩ (PatternedWordData.expectedWordAt 7), .push ⟨1, by decide⟩ (UInt256.ofNat 224), .op .CALLDATALOAD, .op .XOR, .op .OR]
theorem binding7 : assembleBytes template7 = bytes7 := by
  simp only [template7, PatternedWordData.expectedWordAt_7]
  decide

def bytes6 : List UInt8 := [127, 199, 236, 17, 54, 91, 128, 165, 202, 239, 20, 57, 94, 131, 168, 205, 242, 23, 60, 97, 134, 171, 208, 245, 26, 63, 100, 137, 174, 211, 248, 29, 66, 96, 192, 53, 24, 23]
def template6 : List Instr := [.push ⟨32, by decide⟩ (PatternedWordData.expectedWordAt 6), .push ⟨1, by decide⟩ (UInt256.ofNat 192), .op .CALLDATALOAD, .op .XOR, .op .OR]
theorem binding6 : assembleBytes template6 = bytes6 := by
  simp only [template6, PatternedWordData.expectedWordAt_6]
  decide

def bytes5 : List UInt8 := [127, 39, 76, 113, 150, 187, 224, 5, 42, 79, 116, 153, 190, 227, 8, 45, 82, 119, 156, 193, 230, 11, 48, 85, 122, 159, 196, 233, 14, 51, 88, 125, 162, 96, 160, 53, 24, 23]
def template5 : List Instr := [.push ⟨32, by decide⟩ (PatternedWordData.expectedWordAt 5), .push ⟨1, by decide⟩ (UInt256.ofNat 160), .op .CALLDATALOAD, .op .XOR, .op .OR]
theorem binding5 : assembleBytes template5 = bytes5 := by
  simp only [template5, PatternedWordData.expectedWordAt_5]
  decide

def bytes4 : List UInt8 := [127, 135, 172, 209, 246, 27, 64, 101, 138, 175, 212, 249, 30, 67, 104, 141, 178, 215, 252, 33, 70, 107, 144, 181, 218, 255, 36, 73, 110, 147, 184, 221, 2, 96, 128, 53, 24, 23]
def template4 : List Instr := [.push ⟨32, by decide⟩ (PatternedWordData.expectedWordAt 4), .push ⟨1, by decide⟩ (UInt256.ofNat 128), .op .CALLDATALOAD, .op .XOR, .op .OR]
theorem binding4 : assembleBytes template4 = bytes4 := by
  simp only [template4, PatternedWordData.expectedWordAt_4]
  decide

def bytes3 : List UInt8 := [127, 231, 12, 49, 86, 123, 160, 197, 234, 15, 52, 89, 126, 163, 200, 237, 18, 55, 92, 129, 166, 203, 240, 21, 58, 95, 132, 169, 206, 243, 24, 61, 98, 96, 96, 53, 24, 23]
def template3 : List Instr := [.push ⟨32, by decide⟩ (PatternedWordData.expectedWordAt 3), .push ⟨1, by decide⟩ (UInt256.ofNat 96), .op .CALLDATALOAD, .op .XOR, .op .OR]
theorem binding3 : assembleBytes template3 = bytes3 := by
  simp only [template3, PatternedWordData.expectedWordAt_3]
  decide

def bytes2 : List UInt8 := [127, 71, 108, 145, 182, 219, 0, 37, 74, 111, 148, 185, 222, 3, 40, 77, 114, 151, 188, 225, 6, 43, 80, 117, 154, 191, 228, 9, 46, 83, 120, 157, 194, 96, 64, 53, 24, 23]
def template2 : List Instr := [.push ⟨32, by decide⟩ (PatternedWordData.expectedWordAt 2), .push ⟨1, by decide⟩ (UInt256.ofNat 64), .op .CALLDATALOAD, .op .XOR, .op .OR]
theorem binding2 : assembleBytes template2 = bytes2 := by
  simp only [template2, PatternedWordData.expectedWordAt_2]
  decide

def bytes1 : List UInt8 := [127, 167, 204, 241, 22, 59, 96, 133, 170, 207, 244, 25, 62, 99, 136, 173, 210, 247, 28, 65, 102, 139, 176, 213, 250, 31, 68, 105, 142, 179, 216, 253, 34, 89, 53, 24, 23]
def template1 : List Instr := [.push ⟨32, by decide⟩ (PatternedWordData.expectedWordAt 1), .op .MSIZE, .op .CALLDATALOAD, .op .XOR, .op .OR]
theorem binding1 : assembleBytes template1 = bytes1 := by
  simp only [template1, PatternedWordData.expectedWordAt_1]
  decide

#print axioms binding0
#print axioms binding31
#print axioms binding1
end RetainedIntegration105.LiteralBindings
