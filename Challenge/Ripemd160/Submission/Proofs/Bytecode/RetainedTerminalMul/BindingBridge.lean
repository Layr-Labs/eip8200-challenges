import Challenge.Ripemd160.Submission.Proofs.Bytecode.RetainedTerminalMul.ExactBindings
import Challenge.Ripemd160.Submission.Proofs.Bytecode.RetainedTerminalMul.LiteralBindings
set_option warningAsError true
set_option maxRecDepth 100000
set_option maxHeartbeats 2000000
set_option linter.unusedSimpArgs false
namespace RetainedIntegration105.BindingBridge
open EvmSemantics EvmSemantics.EVM YulEvmCompiler
open Challenge.Ripemd160.Submission.Proofs.Bytecode
open RetainedIntegration105 ExactBindings LiteralBindings
theorem seed_binding : assembleBytes RetainedFirstWordResearch.seedTemplate = bytes0 := by exact binding0
theorem step31 : assembleBytes (positiveStep 31) = bytes31 := by exact binding31
theorem step30 : assembleBytes (positiveStep 30) = bytes30 := by exact binding30
theorem step29 : assembleBytes (positiveStep 29) = bytes29 := by exact binding29
theorem step28 : assembleBytes (positiveStep 28) = bytes28 := by exact binding28
theorem step27 : assembleBytes (positiveStep 27) = bytes27 := by exact binding27
theorem step26 : assembleBytes (positiveStep 26) = bytes26 := by exact binding26
theorem step25 : assembleBytes (positiveStep 25) = bytes25 := by exact binding25
theorem step24 : assembleBytes (positiveStep 24) = bytes24 := by exact binding24
theorem step23 : assembleBytes (positiveStep 23) = bytes23 := by exact binding23
theorem step22 : assembleBytes (positiveStep 22) = bytes22 := by exact binding22
theorem step21 : assembleBytes (positiveStep 21) = bytes21 := by exact binding21
theorem step20 : assembleBytes (positiveStep 20) = bytes20 := by exact binding20
theorem step19 : assembleBytes (positiveStep 19) = bytes19 := by exact binding19
theorem step18 : assembleBytes (positiveStep 18) = bytes18 := by exact binding18
theorem step17 : assembleBytes (positiveStep 17) = bytes17 := by exact binding17
theorem step16 : assembleBytes (positiveStep 16) = bytes16 := by exact binding16
theorem step15 : assembleBytes (positiveStep 15) = bytes15 := by exact binding15
theorem step14 : assembleBytes (positiveStep 14) = bytes14 := by exact binding14
theorem step13 : assembleBytes (positiveStep 13) = bytes13 := by exact binding13
theorem step12 : assembleBytes (positiveStep 12) = bytes12 := by exact binding12
theorem step11 : assembleBytes (positiveStep 11) = bytes11 := by exact binding11
theorem step10 : assembleBytes (positiveStep 10) = bytes10 := by exact binding10
theorem step9 : assembleBytes (positiveStep 9) = bytes9 := by exact binding9
theorem step8 : assembleBytes (positiveStep 8) = bytes8 := by exact binding8
theorem step7 : assembleBytes (positiveStep 7) = bytes7 := by exact binding7
theorem step6 : assembleBytes (positiveStep 6) = bytes6 := by exact binding6
theorem step5 : assembleBytes (positiveStep 5) = bytes5 := by exact binding5
theorem step4 : assembleBytes (positiveStep 4) = bytes4 := by exact binding4
theorem step3 : assembleBytes (positiveStep 3) = bytes3 := by exact binding3
theorem step2 : assembleBytes (positiveStep 2) = bytes2 := by exact binding2
theorem step1 : assembleBytes (positiveStep 1) = bytes1 := by exact binding1
def comparisonBytes : List UInt8 := (storeBytes ++ bytes0) ++ (bytes31 ++ bytes30 ++ bytes29 ++ bytes28 ++ bytes27 ++ bytes26 ++ bytes25 ++ bytes24 ++ bytes23 ++ bytes22 ++ bytes21 ++ bytes20 ++ bytes19 ++ bytes18 ++ bytes17 ++ bytes16 ++ bytes15 ++ bytes14 ++ bytes13 ++ bytes12 ++ bytes11 ++ bytes10 ++ bytes9 ++ bytes8 ++ bytes7 ++ bytes6 ++ bytes5 ++ bytes4 ++ bytes3 ++ bytes2 ++ bytes1)
theorem whole_comparison_binding : assembleBytes (literalTemplate digest) = comparisonBytes := by
  simp only [literalTemplate, positiveScan, assembleBytes_append,
    assembleBytes_nil, List.append_nil, store_binding, seed_binding, Nat.reduceAdd, comparisonBytes, List.append_assoc,
    step31, step30, step29, step28, step27, step26, step25, step24, step23, step22, step21, step20, step19, step18, step17, step16, step15, step14, step13, step12, step11, step10, step9, step8, step7, step6, step5, step4, step3, step2, step1]
#print axioms whole_comparison_binding
end RetainedIntegration105.BindingBridge
