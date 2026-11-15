import Challenge.Modexp.Submission.Proofs.Prepared.StackArgs
import Challenge.Modexp.Submission.Proofs.CycleGlobal.Binding
import Challenge.Modexp.Submission.Proofs.CycleGlobal.FastDefs
open CycleSubmission.SharedStackArgs
noncomputable section
set_option warningAsError true
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000
namespace CycleSubmission.Global.Fast
private abbrev runtimeArtifact := CycleSubmission.Artifact.artifact
open Challenge.Modexp
open Challenge.Modexp.Submission.Proofs
open Challenge.Modexp.Submission.Proofs.Bytecode
open Challenge.Modexp.Submission.Proofs.Fast
open EvmSemantics
open EvmSemantics.EVM
open Challenge.Modexp.Submission.Proofs.Bytecode
def blk2862 :
    List (Challenge.EvmProof.Stepper.Located runtimeArtifact .Osaka) :=
  [opAt 672 (.Dup ⟨0,by decide⟩),
   opAt 673 (.Dup ⟨3,by decide⟩),
   opAt 674 .XOR,
   pushAt 675 1 172,
   opAt 676 .JUMPI]
def blk2874 :
    List (Challenge.EvmProof.Stepper.Located runtimeArtifact .Osaka) :=
  [opAt 677 (.Dup ⟨0,by decide⟩),
   pushAt 678 1 96,
   pushAt 679 2 2112,
   opAt 680 .CALLDATACOPY]
def blkNegW :
    List (Challenge.EvmProof.Stepper.Located runtimeArtifact .Osaka) :=
  [opAt 7918 (.Dup ⟨0,by decide⟩),
   pushAt 7919 1 128,
   opAt 7920 .EQ,
   pushAt 7921 2 6642,
   opAt 7922 .JUMPI]
def negS8 :
    List (Challenge.EvmProof.Stepper.Located runtimeArtifact .Osaka) :=
  [pushAt 7923 1 224,
   opAt 7924 .MLOAD,
   pushAt 7925 0 0,
   opAt 7926 .SUB,
   pushAt 7927 2 1504,
   opAt 7928 .MSTORE]
def negN8a :
    List (Challenge.EvmProof.Stepper.Located runtimeArtifact .Osaka) :=
  [pushAt 7929 1 192,
   opAt 7930 .MLOAD,
   opAt 7931 .NOT,
   pushAt 7932 2 1472,
   opAt 7933 .MSTORE]
def negN8b :
    List (Challenge.EvmProof.Stepper.Located runtimeArtifact .Osaka) :=
  [pushAt 7934 1 160,
   opAt 7935 .MLOAD,
   opAt 7936 .NOT,
   pushAt 7937 2 1440,
   opAt 7938 .MSTORE]
def negN8c :
    List (Challenge.EvmProof.Stepper.Located runtimeArtifact .Osaka) :=
  [pushAt 7939 1 128,
   opAt 7940 .MLOAD,
   opAt 7941 .NOT,
   pushAt 7942 2 1408,
   opAt 7943 .MSTORE]
def negN8d :
    List (Challenge.EvmProof.Stepper.Located runtimeArtifact .Osaka) :=
  [pushAt 7944 1 96,
   opAt 7945 .MLOAD,
   opAt 7946 .NOT,
   pushAt 7947 2 1376,
   opAt 7948 .MSTORE]
def negS4 :
    List (Challenge.EvmProof.Stepper.Located runtimeArtifact .Osaka) :=
  [pushAt 4865 1 96,
   opAt 4866 .MLOAD,
   pushAt 4867 0 0,
   opAt 4868 .SUB,
   pushAt 4869 2 1376,
   opAt 4870 .MSTORE]
def negJ4 :
    List (Challenge.EvmProof.Stepper.Located runtimeArtifact .Osaka) :=
  [opAt 4864 .JUMPDEST]
def negJ4b :
    List (Challenge.EvmProof.Stepper.Located runtimeArtifact .Osaka) :=
  [pushAt 4871 2 10524,
   opAt 4872 .JUMP]
def negJT :
    List (Challenge.EvmProof.Stepper.Located runtimeArtifact .Osaka) :=
  [opAt 7949 .JUMPDEST]
def blkNeg8 :
    List (Challenge.EvmProof.Stepper.Located runtimeArtifact .Osaka) :=
  negS8++negN8a++negN8b++negN8c++negN8d
def blkNeg4 :
    List (Challenge.EvmProof.Stepper.Located runtimeArtifact .Osaka) :=
  negJ4++negS4++negJ4b
def blkNegT :
    List (Challenge.EvmProof.Stepper.Located runtimeArtifact .Osaka) :=
  [opAt 7949 .JUMPDEST,
   pushAt 7950 1 64,
   opAt 7951 .MLOAD,
   opAt 7952 .NOT,
   pushAt 7953 2 1344,
   opAt 7954 .MSTORE,
   pushAt 7955 1 32,
   opAt 7956 .MLOAD,
   opAt 7957 .NOT,
   pushAt 7958 2 1312,
   opAt 7959 .MSTORE,
   pushAt 7960 0 0,
   opAt 7961 .MLOAD,
   opAt 7962 (.Dup ⟨0,by decide⟩),
   opAt 7963 .NOT,
   pushAt 7964 2 1280,
   opAt 7965 .MSTORE]
def blk2919a :
    List (Challenge.EvmProof.Stepper.Located runtimeArtifact .Osaka) :=
  [opAt 7966 (.Dup ⟨0,by decide⟩),
   pushAt 7967 0 0,
   opAt 7968 .SUB,
   opAt 7969 (.Dup ⟨1,by decide⟩),
   opAt 7970 .AND]
def blk2919b :
    List (Challenge.EvmProof.Stepper.Located runtimeArtifact .Osaka) :=
  [opAt 7972 (.Dup ⟨0,by decide⟩),
   pushAt 7973 1 1,
   opAt 7974 .ADD,
   pushAt 7975 2 1600,
   opAt 7976 .MSTORE,
   pushAt 7977 1 255,
   opAt 7978 .SUB,
   opAt 7979 (.Dup ⟨0,by decide⟩),
   pushAt 7980 2 1536,
   opAt 7981 .MSTORE,
   opAt 7982 .SHR,
   opAt 7983 (.Dup ⟨0,by decide⟩),
   pushAt 7984 2 1568,
   opAt 7985 .MSTORE,
   opAt 7986 (.Dup ⟨0,by decide⟩),
   opAt 7987 (.Dup ⟨0,by decide⟩),
   pushAt 7988 0 0,
   opAt 7989 .SUB,
   opAt 7990 .MOD,
   pushAt 7991 2 1632,
   opAt 7992 .MSTORE]
def blkNbHead :
    List (Challenge.EvmProof.Stepper.Located runtimeArtifact .Osaka) :=
  [pushAt 7993 2 2752,
   opAt 7994 .MLOAD,
   opAt 7995 .MLOAD,
   opAt 7996 (.Dup ⟨0,by decide⟩),
   opAt 7997 (.Dup ⟨2,by decide⟩),
   opAt 7998 .MUL]
def blkNbSub :
    List (Challenge.EvmProof.Stepper.Located runtimeArtifact .Osaka) :=
  [opAt 7999 (.Dup ⟨0,by decide⟩),
   pushAt 8000 1 3,
   opAt 8001 .MUL,
   pushAt 8002 1 2,
   opAt 8003 .XOR,
   opAt 8004 (.Dup ⟨0,by decide⟩),
   opAt 8005 (.Dup ⟨2,by decide⟩),
   opAt 8006 .MUL,
   pushAt 8007 1 2,
   opAt 8008 .SUB,
   opAt 8009 .MUL,
   opAt 8010 (.Dup ⟨0,by decide⟩),
   opAt 8011 (.Dup ⟨2,by decide⟩),
   opAt 8012 .MUL,
   pushAt 8013 1 2,
   opAt 8014 .SUB,
   opAt 8015 .MUL,
   opAt 8016 (.Dup ⟨0,by decide⟩),
   opAt 8017 (.Dup ⟨2,by decide⟩),
   opAt 8018 .MUL,
   pushAt 8019 1 2,
   opAt 8020 .SUB,
   opAt 8021 .MUL,
   opAt 8022 (.Dup ⟨0,by decide⟩),
   opAt 8023 (.Dup ⟨2,by decide⟩),
   opAt 8024 .MUL,
   pushAt 8025 1 2,
   opAt 8026 .SUB,
   opAt 8027 .MUL,
   opAt 8028 (.Dup ⟨0,by decide⟩),
   opAt 8029 (.Dup ⟨2,by decide⟩),
   opAt 8030 .MUL,
   pushAt 8031 1 2,
   opAt 8032 .SUB,
   opAt 8033 .MUL,
   opAt 8034 (.Dup ⟨0,by decide⟩),
   opAt 8035 (.Swap ⟨1,by decide⟩),
   opAt 8036 .MUL,
   pushAt 8037 1 2,
   opAt 8038 .SUB,
   opAt 8039 .MUL]
def blkNbTailHead : List (Challenge.EvmProof.Stepper.Located runtimeArtifact .Osaka) :=
  [opAt 8040 (.Dup ⟨0,by decide⟩),
   opAt 8041 (.Swap ⟨1,by decide⟩),
   opAt 8042 .MUL,
   pushAt 8043 2 1664,
   opAt 8044 .MSTORE,
   opAt 8045 .MUL,
   pushAt 8046 0 0,
   opAt 8047 .SUB,
   pushAt 8048 2 2720,
   opAt 8049 .MSTORE,
   pushAt 8050 2 8388,
   opAt 8051 (.Dup ⟨4,by decide⟩),
   pushAt 8052 1 1,
   opAt 8053 .XOR,
   pushAt 8054 2 10683,
   opAt 8055 .JUMPI]
def blkNbTailByte : List (Challenge.EvmProof.Stepper.Located runtimeArtifact .Osaka) :=
  [pushAt 8056 2 2656,
   opAt 8057 .MLOAD,
   opAt 8058 .CALLDATALOAD,
   pushAt 8059 0 0,
   opAt 8060 .BYTE,
   pushAt 8061 1 3,
   opAt 8062 .EQ,
   pushAt 8063 2 2051,
   opAt 8064 .MUL,
   opAt 8065 .ADD]
def blkNbTailJoin : List (Challenge.EvmProof.Stepper.Located runtimeArtifact .Osaka) :=
  [opAt 8066 .JUMPDEST,
   pushAt 8067 1 32,
   opAt 8068 .MLOAD,
   pushAt 8069 1 128,
   opAt 8070 .SHR,
   pushAt 8071 2 1536,
   opAt 8072 .MLOAD,
   pushAt 8073 2 1568,
   opAt 8074 .MLOAD,
   pushAt 8075 2 1664,
   opAt 8076 .MLOAD,
   pushAt 8077 2 1632,
   opAt 8078 .MLOAD,
   pushAt 8079 2 1504,
   opAt 8080 .MLOAD,
   pushAt 8081 2 1472,
   opAt 8082 .MLOAD,
   pushAt 8083 2 1440,
   opAt 8084 .MLOAD,
   pushAt 8085 2 1408,
   opAt 8086 .MLOAD,
   pushAt 8087 2 1376,
   opAt 8088 .MLOAD,
   pushAt 8089 2 1344,
   opAt 8090 .MLOAD,
   pushAt 8091 2 1312,
   opAt 8092 .MLOAD,
   opAt 8093 (.Dup ⟨14,by decide⟩)]
def blkNbTail (esize : Nat) : List (Challenge.EvmProof.Stepper.Located runtimeArtifact .Osaka) :=
  blkNbTailHead++(if UInt256.ofNat esize = UInt256.ofNat 1 then blkNbTailByte else [])++blkNbTailJoin
theorem jumpDestNbJoin : Decode.isValidJumpDest CycleSubmission.Artifact.bytecode 10683 = true := by
  have h := CycleSubmission.Global.Binding.jumpDest 8066 (by rw [CycleSubmission.Artifact.instruction_get]; rfl)
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)] at h
  exact h
def blkZero8 : List (Challenge.EvmProof.Stepper.Located runtimeArtifact .Osaka) :=
  [opAt 4873 .JUMPDEST,
   opAt 4874 (.Dup ⟨15,by decide⟩),
   pushAt 4875 2 2112,
   pushAt 4876 2 2080,
   opAt 4877 .MCOPY,
   pushAt 4878 2 2080,
   opAt 4879 .MLOAD,
   opAt 4880 (.Dup ⟨14,by decide⟩),
   pushAt 4881 2 2112,
   opAt 4882 .MLOAD,
   opAt 4883 (.Dup ⟨14,by decide⟩),
   opAt 4884 (.Dup ⟨0,by decide⟩),
   opAt 4885 (.Dup ⟨14,by decide⟩),
   opAt 4886 (.Dup ⟨5,by decide⟩),
   opAt 4887 .MULMOD,
   opAt 4888 (.Dup ⟨2,by decide⟩),
   opAt 4889 .ADDMOD,
   opAt 4890 (.Dup ⟨0,by decide⟩),
   opAt 4891 (.Swap ⟨1,by decide⟩),
   opAt 4892 .SUB,
   opAt 4893 (.Dup ⟨14,by decide⟩),
   opAt 4894 .MUL,
   opAt 4895 (.Swap ⟨1,by decide⟩),
   opAt 4896 (.Dup ⟨2,by decide⟩),
   pushAt 4897 1 128,
   opAt 4898 .SHR,
   opAt 4899 .MUL,
   opAt 4900 .GT,
   opAt 4901 (.Swap ⟨0,by decide⟩),
   opAt 4902 .SUB,
   pushAt 4903 2 8506,
   opAt 4904 .JUMP]
def blkZero4 : List (Challenge.EvmProof.Stepper.Located runtimeArtifact .Osaka) :=
  [opAt 299 .JUMPDEST,
   opAt 300 (.Dup ⟨15,by decide⟩),
   pushAt 301 2 2112,
   pushAt 302 2 2080,
   opAt 303 .MCOPY,
   pushAt 304 2 2080,
   opAt 305 .MLOAD,
   opAt 306 (.Dup ⟨14,by decide⟩),
   pushAt 307 2 2112,
   opAt 308 .MLOAD,
   opAt 309 (.Dup ⟨14,by decide⟩),
   opAt 310 (.Dup ⟨0,by decide⟩),
   opAt 311 (.Dup ⟨14,by decide⟩),
   opAt 312 (.Dup ⟨5,by decide⟩),
   opAt 313 .MULMOD,
   opAt 314 (.Dup ⟨2,by decide⟩),
   opAt 315 .ADDMOD,
   opAt 316 (.Dup ⟨0,by decide⟩),
   opAt 317 (.Swap ⟨1,by decide⟩),
   opAt 318 .SUB,
   opAt 319 (.Dup ⟨14,by decide⟩),
   opAt 320 .MUL,
   opAt 321 (.Swap ⟨1,by decide⟩),
   opAt 322 (.Dup ⟨2,by decide⟩),
   pushAt 323 1 128,
   opAt 324 .SHR,
   opAt 325 .MUL,
   opAt 326 .GT,
   opAt 327 (.Swap ⟨0,by decide⟩),
   opAt 328 .SUB,
   pushAt 329 2 586,
   opAt 330 .JUMP]
def blkEstimateSuffix8 : List (Challenge.EvmProof.Stepper.Located runtimeArtifact .Osaka) :=
  [opAt 6405 .JUMPDEST,
   pushAt 6406 32 115792089237316195423570985008687907853269984665640564039457584007913129639935,
   opAt 6407 (.Swap ⟨1,by decide⟩),
   opAt 6408 (.Dup ⟨14,by decide⟩),
   opAt 6409 .GT,
   opAt 6410 (.Dup ⟨2,by decide⟩),
   opAt 6411 .ADD,
   opAt 6412 .OR]
def blkEstimateSuffix4 : List (Challenge.EvmProof.Stepper.Located runtimeArtifact .Osaka) :=
  [opAt 432 .JUMPDEST,
   pushAt 433 32 115792089237316195423570985008687907853269984665640564039457584007913129639935,
   opAt 434 (.Swap ⟨1,by decide⟩),
   opAt 435 (.Dup ⟨14,by decide⟩),
   opAt 436 .GT,
   opAt 437 (.Dup ⟨2,by decide⟩),
   opAt 438 .ADD,
   opAt 439 .OR]
def blk3013 :
    List (Challenge.EvmProof.Stepper.Located runtimeArtifact .Osaka) :=
  [opAt 6360 .JUMPDEST]
def blk3018 :
    List (Challenge.EvmProof.Stepper.Located runtimeArtifact .Osaka) :=
  [opAt 6361 (.Dup ⟨15,by decide⟩),
   pushAt 6362 2 2112,
   pushAt 6363 2 2080,
   opAt 6364 .MCOPY]
def blk3026 :
    List (Challenge.EvmProof.Stepper.Located runtimeArtifact .Osaka) :=
  [pushAt 6365 2 2080,
   opAt 6366 .MLOAD,
   opAt 6367 (.Dup ⟨0,by decide⟩),
   opAt 6368 (.Dup ⟨14,by decide⟩),
   opAt 6369 .SHR,
   opAt 6370 (.Swap ⟨0,by decide⟩),
   pushAt 6371 2 1600,
   opAt 6372 .MLOAD,
   opAt 6373 .SHL,
   pushAt 6374 2 2112,
   opAt 6375 .MLOAD,
   opAt 6376 (.Dup ⟨15,by decide⟩),
   opAt 6377 .SHR,
   opAt 6378 .ADD,
   opAt 6379 (.Dup ⟨13,by decide⟩),
   opAt 6380 (.Dup ⟨0,by decide⟩),
   opAt 6381 (.Dup ⟨13,by decide⟩),
   opAt 6382 (.Dup ⟨4,by decide⟩),
   opAt 6383 .MULMOD,
   opAt 6384 (.Dup ⟨2,by decide⟩),
   opAt 6385 .ADDMOD,
   opAt 6386 (.Swap ⟨0,by decide⟩),
   opAt 6387 .SUB,
   opAt 6388 (.Dup ⟨12,by decide⟩),
   opAt 6389 .MUL,
   opAt 6390 (.Dup ⟨15,by decide⟩),
   opAt 6391 (.Dup ⟨1,by decide⟩),
   pushAt 6392 1 128,
   opAt 6393 .SHR,
   opAt 6394 .MUL,
   opAt 6395 (.Dup ⟨1,by decide⟩),
   pushAt 6396 0 0,
   opAt 6397 .MLOAD,
   opAt 6398 .MUL,
   pushAt 6399 2 2112,
   opAt 6400 .MLOAD,
   opAt 6401 .SUB,
   opAt 6402 .LT,
   opAt 6403 (.Swap ⟨0,by decide⟩),
   opAt 6404 .SUB,
   opAt 6405 .JUMPDEST,
   pushAt 6406 32 115792089237316195423570985008687907853269984665640564039457584007913129639935,
   opAt 6407 (.Swap ⟨1,by decide⟩),
   opAt 6408 (.Dup ⟨14,by decide⟩),
   opAt 6409 .GT,
   opAt 6410 (.Dup ⟨2,by decide⟩),
   opAt 6411 .ADD,
   opAt 6412 .OR]
def blk3013h :
    List (Challenge.EvmProof.Stepper.Located runtimeArtifact .Osaka) :=
  [opAt 387 .JUMPDEST]
def blk3018h :
    List (Challenge.EvmProof.Stepper.Located runtimeArtifact .Osaka) :=
  [opAt 388 (.Dup ⟨15,by decide⟩),
   pushAt 389 2 2112,
   pushAt 390 2 2080,
   opAt 391 .MCOPY]
def blk3026h :
    List (Challenge.EvmProof.Stepper.Located runtimeArtifact .Osaka) :=
  [pushAt 392 2 2080,
   opAt 393 .MLOAD,
   opAt 394 (.Dup ⟨0,by decide⟩),
   opAt 395 (.Dup ⟨14,by decide⟩),
   opAt 396 .SHR,
   opAt 397 (.Swap ⟨0,by decide⟩),
   pushAt 398 2 1600,
   opAt 399 .MLOAD,
   opAt 400 .SHL,
   pushAt 401 2 2112,
   opAt 402 .MLOAD,
   opAt 403 (.Dup ⟨15,by decide⟩),
   opAt 404 .SHR,
   opAt 405 .ADD,
   opAt 406 (.Dup ⟨13,by decide⟩),
   opAt 407 (.Dup ⟨0,by decide⟩),
   opAt 408 (.Dup ⟨13,by decide⟩),
   opAt 409 (.Dup ⟨4,by decide⟩),
   opAt 410 .MULMOD,
   opAt 411 (.Dup ⟨2,by decide⟩),
   opAt 412 .ADDMOD,
   opAt 413 (.Swap ⟨0,by decide⟩),
   opAt 414 .SUB,
   opAt 415 (.Dup ⟨12,by decide⟩),
   opAt 416 .MUL,
   opAt 417 (.Dup ⟨15,by decide⟩),
   opAt 418 (.Dup ⟨1,by decide⟩),
   pushAt 419 1 128,
   opAt 420 .SHR,
   opAt 421 .MUL,
   opAt 422 (.Dup ⟨1,by decide⟩),
   pushAt 423 0 0,
   opAt 424 .MLOAD,
   opAt 425 .MUL,
   pushAt 426 2 2112,
   opAt 427 .MLOAD,
   opAt 428 .SUB,
   opAt 429 .LT,
   opAt 430 (.Swap ⟨0,by decide⟩),
   opAt 431 .SUB,
   opAt 432 .JUMPDEST,
   pushAt 433 32 115792089237316195423570985008687907853269984665640564039457584007913129639935,
   opAt 434 (.Swap ⟨1,by decide⟩),
   opAt 435 (.Dup ⟨14,by decide⟩),
   opAt 436 .GT,
   opAt 437 (.Dup ⟨2,by decide⟩),
   opAt 438 .ADD,
   opAt 439 .OR]
def blk3125Unc :
    List (Challenge.EvmProof.Stepper.Located runtimeArtifact .Osaka) :=
  [pushAt 6627 2 2080,
   opAt 6628 .MLOAD,
   opAt 6629 .ADD,
   opAt 6630 .SUB,
   pushAt 6631 2 1223,
   opAt 6632 .JUMPI,
   opAt 863 .JUMPDEST,
   pushAt 864 2 2080,
   opAt 865 .MSTORE]
def blk3125hUnc :
    List (Challenge.EvmProof.Stepper.Located runtimeArtifact .Osaka) :=
  [pushAt 542 2 2080,
   opAt 543 .MLOAD,
   opAt 544 .ADD,
   opAt 545 .SUB,
   pushAt 546 2 1223,
   opAt 547 .JUMPI,
   opAt 863 .JUMPDEST,
   pushAt 864 2 2080,
   opAt 865 .MSTORE]
def blk3125 :
    List (Challenge.EvmProof.Stepper.Located runtimeArtifact .Osaka) :=
  [pushAt 6627 2 2080,
   opAt 6628 .MLOAD,
   opAt 6629 .ADD,
   opAt 6630 .SUB,
   pushAt 6631 2 1223,
   opAt 6632 .JUMPI]
def blkUnc :
    List (Challenge.EvmProof.Stepper.Located runtimeArtifact .Osaka) :=
  []
def blk3153 :
    List (Challenge.EvmProof.Stepper.Located runtimeArtifact .Osaka) :=
  [opAt 866 .JUMPDEST,
   pushAt 867 0 0,
   pushAt 868 2 2784,
   opAt 869 .MLOAD]
def blk3157 :
    List (Challenge.EvmProof.Stepper.Located runtimeArtifact .Osaka) :=
  [opAt 870 .JUMPDEST,
   opAt 871 (.Dup ⟨0,by decide⟩),
   opAt 872 .MLOAD,
   pushAt 873 2 2112,
   opAt 874 (.Dup ⟨2,by decide⟩),
   opAt 875 .SUB,
   opAt 876 .MLOAD,
   opAt 877 (.Dup ⟨1,by decide⟩),
   opAt 878 .ADD,
   opAt 879 (.Swap ⟨0,by decide⟩),
   opAt 880 (.Dup ⟨1,by decide⟩),
   opAt 881 .LT,
   opAt 882 (.Swap ⟨0,by decide⟩),
   opAt 883 (.Dup ⟨3,by decide⟩),
   opAt 884 .ADD,
   opAt 885 (.Swap ⟨2,by decide⟩),
   opAt 886 (.Dup ⟨3,by decide⟩),
   opAt 887 .LT,
   opAt 888 .OR,
   opAt 889 (.Swap ⟨1,by decide⟩),
   opAt 890 (.Dup ⟨1,by decide⟩),
   opAt 891 .MSTORE,
   pushAt 892 1 31,
   opAt 893 .NOT,
   opAt 894 .ADD,
   pushAt 895 2 2111,
   opAt 896 (.Dup ⟨1,by decide⟩),
   opAt 897 .GT,
   pushAt 898 2 1234,
   opAt 899 .JUMPI]
def blk3192 :
    List (Challenge.EvmProof.Stepper.Located runtimeArtifact .Osaka) :=
  [opAt 900 .POP,
   pushAt 901 2 2080,
   opAt 902 .MLOAD,
   opAt 903 (.Dup ⟨1,by decide⟩),
   opAt 904 .ADD,
   opAt 905 (.Dup ⟨0,by decide⟩),
   pushAt 906 2 2080,
   opAt 907 .MSTORE,
   opAt 908 .LT,
   opAt 909 .ISZERO,
   pushAt 910 2 1228,
   opAt 911 .JUMPI]
def blk3204 :
    List (Challenge.EvmProof.Stepper.Located runtimeArtifact .Osaka) :=
  [pushAt 912 2 2080,
   opAt 913 .MLOAD,
   opAt 914 (.Dup ⟨0,by decide⟩),
   opAt 915 .ISZERO,
   opAt 916 (.Swap ⟨0,by decide⟩),
   opAt 917 .NOT,
   opAt 918 (.Swap ⟨0,by decide⟩),
   pushAt 919 2 10991,
   opAt 920 .JUMPI]
def blk3253 :
    List (Challenge.EvmProof.Stepper.Located runtimeArtifact .Osaka) :=
  [opAt 6633 .ADD,
   opAt 6634 (.Dup ⟨0,by decide⟩),
   opAt 6635 (.Dup ⟨2,by decide⟩),
   opAt 6636 .JUMPI]
def blk3253x :
    List (Challenge.EvmProof.Stepper.Located runtimeArtifact .Osaka) :=
  []
def blk3125h :
    List (Challenge.EvmProof.Stepper.Located runtimeArtifact .Osaka) :=
  [pushAt 542 2 2080,
   opAt 543 .MLOAD,
   opAt 544 .ADD,
   opAt 545 .SUB,
   pushAt 546 2 1223,
   opAt 547 .JUMPI]
def blk3253h :
    List (Challenge.EvmProof.Stepper.Located runtimeArtifact .Osaka) :=
  [opAt 548 .ADD,
   opAt 549 (.Dup ⟨0,by decide⟩),
   opAt 550 (.Dup ⟨2,by decide⟩),
   opAt 551 .JUMPI]
theorem jumpDestBigC : Decode.isValidJumpDest CycleSubmission.Artifact.bytecode 172 = true := by
  have h := CycleSubmission.Global.Binding.jumpDest 131 (by rw [CycleSubmission.Artifact.instruction_get]; rfl)
  have hp : runtimeArtifact.instructionPC 131 = 172 := by
    rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
  simpa only [hp] using h
theorem jumpDest4657 : Decode.isValidJumpDest CycleSubmission.Artifact.bytecode 10466 = true := by
  have h := CycleSubmission.Global.Binding.jumpDest 7913 (by rw [CycleSubmission.Artifact.instruction_get]; rfl)
  have hp : runtimeArtifact.instructionPC 7913 = 10466 := by
    rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
  simpa only [hp] using h
theorem jumpDestNeg4 : Decode.isValidJumpDest CycleSubmission.Artifact.bytecode 6642 = true := by
  have h := CycleSubmission.Global.Binding.jumpDest 4864 (by rw [CycleSubmission.Artifact.instruction_get]; rfl)
  have hp : runtimeArtifact.instructionPC 4864 = 6642 := by
    rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
  simpa only [hp] using h
theorem jumpDestNegT : Decode.isValidJumpDest CycleSubmission.Artifact.bytecode 10524 = true := by
  have h := CycleSubmission.Global.Binding.jumpDest 7949 (by rw [CycleSubmission.Artifact.instruction_get]; rfl)
  have hp : runtimeArtifact.instructionPC 7949 = 10524 := by
    rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
  simpa only [hp] using h
theorem jumpDest4839 : Decode.isValidJumpDest CycleSubmission.Artifact.bytecode 8448 = true := by
  have h := CycleSubmission.Global.Binding.jumpDest 6360 (by rw [CycleSubmission.Artifact.instruction_get]; rfl)
  have hp : runtimeArtifact.instructionPC 6360 = 8448 := by
    rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
  simpa only [hp] using h
theorem jumpDestHead4 : Decode.isValidJumpDest CycleSubmission.Artifact.bytecode 528 = true := by
  have h := CycleSubmission.Global.Binding.jumpDest 387 (by rw [CycleSubmission.Artifact.instruction_get]; rfl)
  have hp : runtimeArtifact.instructionPC 387 = 528 := by
    rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
  simpa only [hp] using h
theorem jumpDest5115 : Decode.isValidJumpDest CycleSubmission.Artifact.bytecode 1228 = true := by
  have h := CycleSubmission.Global.Binding.jumpDest 866 (by rw [CycleSubmission.Artifact.instruction_get]; rfl)
  have hp : runtimeArtifact.instructionPC 866 = 1228 := by
    rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
  simpa only [hp] using h
theorem jumpDest5121 : Decode.isValidJumpDest CycleSubmission.Artifact.bytecode 1234 = true := by
  have h := CycleSubmission.Global.Binding.jumpDest 870 (by rw [CycleSubmission.Artifact.instruction_get]; rfl)
  have hp : runtimeArtifact.instructionPC 870 = 1234 := by
    rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
  simpa only [hp] using h
theorem jumpDestLazyStore : Decode.isValidJumpDest CycleSubmission.Artifact.bytecode 1223 = true := by
  have h := CycleSubmission.Global.Binding.jumpDest 863 (by rw [CycleSubmission.Artifact.instruction_get]; rfl)
  have hp : runtimeArtifact.instructionPC 863 = 1223 := by
    rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
  simpa only [hp] using h
theorem jumpDestUnc : Decode.isValidJumpDest CycleSubmission.Artifact.bytecode 1223 = true := by
  have h := CycleSubmission.Global.Binding.jumpDest 863 (by rw [CycleSubmission.Artifact.instruction_get]; rfl)
  have hp : runtimeArtifact.instructionPC 863 = 1223 := by
    rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
  simpa only [hp] using h
theorem jumpDest5311 : Decode.isValidJumpDest CycleSubmission.Artifact.bytecode 10991 = true := by
  have h := CycleSubmission.Global.Binding.jumpDest 8286 (by rw [CycleSubmission.Artifact.instruction_get]; rfl)
  have hp : CycleSubmission.Artifact.artifact.instructionPC 8286 = 10991 := by
    rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
  simpa only [hp] using h
theorem jumpDest2471 : Decode.isValidJumpDest CycleSubmission.Artifact.bytecode 10459 = true := by
  have h := CycleSubmission.Global.Binding.jumpDest 7908 (by rw [CycleSubmission.Artifact.instruction_get]; rfl)
  have hp : runtimeArtifact.instructionPC 7908 = 10459 := by
    rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
  simpa only [hp] using h
end CycleSubmission.Global.Fast
namespace CycleSubmission.Global.Fast
open EvmSemantics EvmSemantics.EVM
end CycleSubmission.Global.Fast
