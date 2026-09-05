import Challenge.Ripemd160.Submission.H39Memo.DigestBridge

set_option warningAsError true
set_option maxRecDepth 1000000
set_option maxHeartbeats 10000000

namespace Challenge.Ripemd160.Submission.H39Memo

open Proofs.Bytecode

theorem scheduleP1000_0 :
    CompressionCorrect.schedule (Padding.paddedMessage inputP1000) 0 = B10 := by
  norm_num (config := { maxSteps := 1000000 })
    [CompressionCorrect.schedule, EvmSemantics.Crypto.Ripemd160.readLE32,
      Padding.paddedMessage, Padding.zeroBytes, Padding.zeroCount,
      Padding.paddedLength, Padding.lengthBytes, inputP1000,
      List.range', List.foldl, Array.setIfInBounds,
      ByteArray.getElem_eq_getElem_data, ByteArray.data_append]
  decide

theorem scheduleP1000_1 :
    CompressionCorrect.schedule (Padding.paddedMessage inputP1000) 64 = B16 := by
  norm_num (config := { maxSteps := 1000000 })
    [CompressionCorrect.schedule, EvmSemantics.Crypto.Ripemd160.readLE32,
      Padding.paddedMessage, Padding.zeroBytes, Padding.zeroCount,
      Padding.paddedLength, Padding.lengthBytes, inputP1000,
      List.range', List.foldl, Array.setIfInBounds,
      ByteArray.getElem_eq_getElem_data, ByteArray.data_append]
  decide

theorem scheduleP1000_2 :
    CompressionCorrect.schedule (Padding.paddedMessage inputP1000) 128 = B18 := by
  norm_num (config := { maxSteps := 1000000 })
    [CompressionCorrect.schedule, EvmSemantics.Crypto.Ripemd160.readLE32,
      Padding.paddedMessage, Padding.zeroBytes, Padding.zeroCount,
      Padding.paddedLength, Padding.lengthBytes, inputP1000,
      List.range', List.foldl, Array.setIfInBounds,
      ByteArray.getElem_eq_getElem_data, ByteArray.data_append]
  decide

theorem scheduleP1000_3 :
    CompressionCorrect.schedule (Padding.paddedMessage inputP1000) 192 = B19 := by
  norm_num (config := { maxSteps := 1000000 })
    [CompressionCorrect.schedule, EvmSemantics.Crypto.Ripemd160.readLE32,
      Padding.paddedMessage, Padding.zeroBytes, Padding.zeroCount,
      Padding.paddedLength, Padding.lengthBytes, inputP1000,
      List.range', List.foldl, Array.setIfInBounds,
      ByteArray.getElem_eq_getElem_data, ByteArray.data_append]
  decide

theorem scheduleP1000_4 :
    CompressionCorrect.schedule (Padding.paddedMessage inputP1000) 256 = B21 := by
  norm_num (config := { maxSteps := 1000000 })
    [CompressionCorrect.schedule, EvmSemantics.Crypto.Ripemd160.readLE32,
      Padding.paddedMessage, Padding.zeroBytes, Padding.zeroCount,
      Padding.paddedLength, Padding.lengthBytes, inputP1000,
      List.range', List.foldl, Array.setIfInBounds,
      ByteArray.getElem_eq_getElem_data, ByteArray.data_append]
  decide

theorem scheduleP1000_5 :
    CompressionCorrect.schedule (Padding.paddedMessage inputP1000) 320 = B24 := by
  norm_num (config := { maxSteps := 1000000 })
    [CompressionCorrect.schedule, EvmSemantics.Crypto.Ripemd160.readLE32,
      Padding.paddedMessage, Padding.zeroBytes, Padding.zeroCount,
      Padding.paddedLength, Padding.lengthBytes, inputP1000,
      List.range', List.foldl, Array.setIfInBounds,
      ByteArray.getElem_eq_getElem_data, ByteArray.data_append]
  decide

theorem scheduleP1000_6 :
    CompressionCorrect.schedule (Padding.paddedMessage inputP1000) 384 = B25 := by
  norm_num (config := { maxSteps := 1000000 })
    [CompressionCorrect.schedule, EvmSemantics.Crypto.Ripemd160.readLE32,
      Padding.paddedMessage, Padding.zeroBytes, Padding.zeroCount,
      Padding.paddedLength, Padding.lengthBytes, inputP1000,
      List.range', List.foldl, Array.setIfInBounds,
      ByteArray.getElem_eq_getElem_data, ByteArray.data_append]
  decide

theorem scheduleP1000_7 :
    CompressionCorrect.schedule (Padding.paddedMessage inputP1000) 448 = B26 := by
  norm_num (config := { maxSteps := 1000000 })
    [CompressionCorrect.schedule, EvmSemantics.Crypto.Ripemd160.readLE32,
      Padding.paddedMessage, Padding.zeroBytes, Padding.zeroCount,
      Padding.paddedLength, Padding.lengthBytes, inputP1000,
      List.range', List.foldl, Array.setIfInBounds,
      ByteArray.getElem_eq_getElem_data, ByteArray.data_append]
  decide

theorem scheduleP1000_8 :
    CompressionCorrect.schedule (Padding.paddedMessage inputP1000) 512 = B27 := by
  norm_num (config := { maxSteps := 1000000 })
    [CompressionCorrect.schedule, EvmSemantics.Crypto.Ripemd160.readLE32,
      Padding.paddedMessage, Padding.zeroBytes, Padding.zeroCount,
      Padding.paddedLength, Padding.lengthBytes, inputP1000,
      List.range', List.foldl, Array.setIfInBounds,
      ByteArray.getElem_eq_getElem_data, ByteArray.data_append]
  decide

theorem scheduleP1000_9 :
    CompressionCorrect.schedule (Padding.paddedMessage inputP1000) 576 = B28 := by
  norm_num (config := { maxSteps := 1000000 })
    [CompressionCorrect.schedule, EvmSemantics.Crypto.Ripemd160.readLE32,
      Padding.paddedMessage, Padding.zeroBytes, Padding.zeroCount,
      Padding.paddedLength, Padding.lengthBytes, inputP1000,
      List.range', List.foldl, Array.setIfInBounds,
      ByteArray.getElem_eq_getElem_data, ByteArray.data_append]
  decide

theorem scheduleP1000_10 :
    CompressionCorrect.schedule (Padding.paddedMessage inputP1000) 640 = B29 := by
  norm_num (config := { maxSteps := 1000000 })
    [CompressionCorrect.schedule, EvmSemantics.Crypto.Ripemd160.readLE32,
      Padding.paddedMessage, Padding.zeroBytes, Padding.zeroCount,
      Padding.paddedLength, Padding.lengthBytes, inputP1000,
      List.range', List.foldl, Array.setIfInBounds,
      ByteArray.getElem_eq_getElem_data, ByteArray.data_append]
  decide

theorem scheduleP1000_11 :
    CompressionCorrect.schedule (Padding.paddedMessage inputP1000) 704 = B30 := by
  norm_num (config := { maxSteps := 1000000 })
    [CompressionCorrect.schedule, EvmSemantics.Crypto.Ripemd160.readLE32,
      Padding.paddedMessage, Padding.zeroBytes, Padding.zeroCount,
      Padding.paddedLength, Padding.lengthBytes, inputP1000,
      List.range', List.foldl, Array.setIfInBounds,
      ByteArray.getElem_eq_getElem_data, ByteArray.data_append]
  decide

theorem scheduleP1000_12 :
    CompressionCorrect.schedule (Padding.paddedMessage inputP1000) 768 = B31 := by
  norm_num (config := { maxSteps := 1000000 })
    [CompressionCorrect.schedule, EvmSemantics.Crypto.Ripemd160.readLE32,
      Padding.paddedMessage, Padding.zeroBytes, Padding.zeroCount,
      Padding.paddedLength, Padding.lengthBytes, inputP1000,
      List.range', List.foldl, Array.setIfInBounds,
      ByteArray.getElem_eq_getElem_data, ByteArray.data_append]
  decide

theorem scheduleP1000_13 :
    CompressionCorrect.schedule (Padding.paddedMessage inputP1000) 832 = B32 := by
  norm_num (config := { maxSteps := 1000000 })
    [CompressionCorrect.schedule, EvmSemantics.Crypto.Ripemd160.readLE32,
      Padding.paddedMessage, Padding.zeroBytes, Padding.zeroCount,
      Padding.paddedLength, Padding.lengthBytes, inputP1000,
      List.range', List.foldl, Array.setIfInBounds,
      ByteArray.getElem_eq_getElem_data, ByteArray.data_append]
  decide

theorem scheduleP1000_14 :
    CompressionCorrect.schedule (Padding.paddedMessage inputP1000) 896 = B33 := by
  norm_num (config := { maxSteps := 1000000 })
    [CompressionCorrect.schedule, EvmSemantics.Crypto.Ripemd160.readLE32,
      Padding.paddedMessage, Padding.zeroBytes, Padding.zeroCount,
      Padding.paddedLength, Padding.lengthBytes, inputP1000,
      List.range', List.foldl, Array.setIfInBounds,
      ByteArray.getElem_eq_getElem_data, ByteArray.data_append]
  decide

theorem scheduleP1000_15 :
    CompressionCorrect.schedule (Padding.paddedMessage inputP1000) 960 = B34 := by
  norm_num (config := { maxSteps := 1000000 })
    [CompressionCorrect.schedule, EvmSemantics.Crypto.Ripemd160.readLE32,
      Padding.paddedMessage, Padding.zeroBytes, Padding.zeroCount,
      Padding.paddedLength, Padding.lengthBytes, inputP1000,
      List.range', List.foldl, Array.setIfInBounds,
      ByteArray.getElem_eq_getElem_data, ByteArray.data_append]
  decide

end Challenge.Ripemd160.Submission.H39Memo
