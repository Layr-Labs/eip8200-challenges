import Challenge.Modexp.Submission.Proofs.Bytecode.MainDefs
set_option warningAsError true
set_option maxRecDepth 40000
set_option maxHeartbeats 4000000

namespace Challenge.Modexp.Submission.Proofs.Fast.GuardPaths

open EvmSemantics
open EvmSemantics.EVM
open Challenge.Modexp.Submission.Proofs.Bytecode

def preludePath :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [
   Main.opAt 1913 (EvmSemantics.Operation.StackMemFlow (EvmSemantics.Operation.StackMemFlowOps.JUMPDEST)),
   Main.pushAt 1914 0 0,
   Main.pushAt 1915 2 611,
   Main.opAt 1916 (EvmSemantics.Operation.Env (EvmSemantics.Operation.EnvOps.CALLDATASIZE)),
   Main.opAt 1917 (EvmSemantics.Operation.CompBit (EvmSemantics.Operation.CompareBitwiseOps.XOR)),
   Main.opAt 1918 (EvmSemantics.Operation.CompBit (EvmSemantics.Operation.CompareBitwiseOps.OR))
  ]

def check0Path :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [
   Main.pushAt 1919 32 256,
   Main.pushAt 1920 0 0,
   Main.opAt 1921 (EvmSemantics.Operation.Env (EvmSemantics.Operation.EnvOps.CALLDATALOAD)),
   Main.opAt 1922 (EvmSemantics.Operation.CompBit (EvmSemantics.Operation.CompareBitwiseOps.XOR)),
   Main.opAt 1923 (EvmSemantics.Operation.CompBit (EvmSemantics.Operation.CompareBitwiseOps.OR)),
   Main.pushAt 1924 32 3,
   Main.pushAt 1925 1 32,
   Main.opAt 1926 (EvmSemantics.Operation.Env (EvmSemantics.Operation.EnvOps.CALLDATALOAD)),
   Main.opAt 1927 (EvmSemantics.Operation.CompBit (EvmSemantics.Operation.CompareBitwiseOps.XOR)),
   Main.opAt 1928 (EvmSemantics.Operation.CompBit (EvmSemantics.Operation.CompareBitwiseOps.OR)),
   Main.pushAt 1929 32 256,
   Main.pushAt 1930 1 64,
   Main.opAt 1931 (EvmSemantics.Operation.Env (EvmSemantics.Operation.EnvOps.CALLDATALOAD)),
   Main.opAt 1932 (EvmSemantics.Operation.CompBit (EvmSemantics.Operation.CompareBitwiseOps.XOR)),
   Main.opAt 1933 (EvmSemantics.Operation.CompBit (EvmSemantics.Operation.CompareBitwiseOps.OR)),
   Main.pushAt 1934 32 5204757502602156741860927903554486215631002020034533658579986437169090367113,
   Main.pushAt 1935 1 96,
   Main.opAt 1936 (EvmSemantics.Operation.Env (EvmSemantics.Operation.EnvOps.CALLDATALOAD)),
   Main.opAt 1937 (EvmSemantics.Operation.CompBit (EvmSemantics.Operation.CompareBitwiseOps.XOR)),
   Main.opAt 1938 (EvmSemantics.Operation.CompBit (EvmSemantics.Operation.CompareBitwiseOps.OR))
  ]

def check1Path :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [
   Main.pushAt 1939 32 63281855121729576028135952504278109029469994387028540079769462288734980692379,
   Main.pushAt 1940 1 128,
   Main.opAt 1941 (EvmSemantics.Operation.Env (EvmSemantics.Operation.EnvOps.CALLDATALOAD)),
   Main.opAt 1942 (EvmSemantics.Operation.CompBit (EvmSemantics.Operation.CompareBitwiseOps.XOR)),
   Main.opAt 1943 (EvmSemantics.Operation.CompBit (EvmSemantics.Operation.CompareBitwiseOps.OR)),
   Main.pushAt 1944 32 43955854185733434782678024279111821513371604761470886693064552075468003969770,
   Main.pushAt 1945 1 160,
   Main.opAt 1946 (EvmSemantics.Operation.Env (EvmSemantics.Operation.EnvOps.CALLDATALOAD)),
   Main.opAt 1947 (EvmSemantics.Operation.CompBit (EvmSemantics.Operation.CompareBitwiseOps.XOR)),
   Main.opAt 1948 (EvmSemantics.Operation.CompBit (EvmSemantics.Operation.CompareBitwiseOps.OR)),
   Main.pushAt 1949 32 85909128446909059588316066171361083131937545499049077817722168959598184821777,
   Main.pushAt 1950 1 192,
   Main.opAt 1951 (EvmSemantics.Operation.Env (EvmSemantics.Operation.EnvOps.CALLDATALOAD)),
   Main.opAt 1952 (EvmSemantics.Operation.CompBit (EvmSemantics.Operation.CompareBitwiseOps.XOR)),
   Main.opAt 1953 (EvmSemantics.Operation.CompBit (EvmSemantics.Operation.CompareBitwiseOps.OR)),
   Main.pushAt 1954 32 69825330230688921115527317574359630961253013696483226710135179334297009575826,
   Main.pushAt 1955 1 224,
   Main.opAt 1956 (EvmSemantics.Operation.Env (EvmSemantics.Operation.EnvOps.CALLDATALOAD)),
   Main.opAt 1957 (EvmSemantics.Operation.CompBit (EvmSemantics.Operation.CompareBitwiseOps.XOR)),
   Main.opAt 1958 (EvmSemantics.Operation.CompBit (EvmSemantics.Operation.CompareBitwiseOps.OR))
  ]

def check2Path :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [
   Main.pushAt 1959 32 19202660333895461906736249453977813469536985895555090982420583257661385454895,
   Main.pushAt 1960 2 256,
   Main.opAt 1961 (EvmSemantics.Operation.Env (EvmSemantics.Operation.EnvOps.CALLDATALOAD)),
   Main.opAt 1962 (EvmSemantics.Operation.CompBit (EvmSemantics.Operation.CompareBitwiseOps.XOR)),
   Main.opAt 1963 (EvmSemantics.Operation.CompBit (EvmSemantics.Operation.CompareBitwiseOps.OR)),
   Main.pushAt 1964 32 26054233372445659190091871567197130036051646819490296855113304995001464273605,
   Main.pushAt 1965 2 288,
   Main.opAt 1966 (EvmSemantics.Operation.Env (EvmSemantics.Operation.EnvOps.CALLDATALOAD)),
   Main.opAt 1967 (EvmSemantics.Operation.CompBit (EvmSemantics.Operation.CompareBitwiseOps.XOR)),
   Main.opAt 1968 (EvmSemantics.Operation.CompBit (EvmSemantics.Operation.CompareBitwiseOps.OR)),
   Main.pushAt 1969 32 76441194212611082221067249017375818798609081338753921089749826938651926500820,
   Main.pushAt 1970 2 320,
   Main.opAt 1971 (EvmSemantics.Operation.Env (EvmSemantics.Operation.EnvOps.CALLDATALOAD)),
   Main.opAt 1972 (EvmSemantics.Operation.CompBit (EvmSemantics.Operation.CompareBitwiseOps.XOR)),
   Main.opAt 1973 (EvmSemantics.Operation.CompBit (EvmSemantics.Operation.CompareBitwiseOps.OR)),
   Main.pushAt 1974 32 452324521598467085373558698738785274637982913208579633907898081764202740992,
   Main.pushAt 1975 2 352,
   Main.opAt 1976 (EvmSemantics.Operation.Env (EvmSemantics.Operation.EnvOps.CALLDATALOAD)),
   Main.opAt 1977 (EvmSemantics.Operation.CompBit (EvmSemantics.Operation.CompareBitwiseOps.XOR)),
   Main.opAt 1978 (EvmSemantics.Operation.CompBit (EvmSemantics.Operation.CompareBitwiseOps.OR))
  ]

def check3Path :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [
   Main.pushAt 1979 32 9627517346447367618050140505607668160680553384609730874378977357693307294624,
   Main.pushAt 1980 2 384,
   Main.opAt 1981 (EvmSemantics.Operation.Env (EvmSemantics.Operation.EnvOps.CALLDATALOAD)),
   Main.opAt 1982 (EvmSemantics.Operation.CompBit (EvmSemantics.Operation.CompareBitwiseOps.XOR)),
   Main.opAt 1983 (EvmSemantics.Operation.CompBit (EvmSemantics.Operation.CompareBitwiseOps.OR)),
   Main.pushAt 1984 32 23914626403865118422549393746198425187271253124650140704454329390959559138920,
   Main.pushAt 1985 2 416,
   Main.opAt 1986 (EvmSemantics.Operation.Env (EvmSemantics.Operation.EnvOps.CALLDATALOAD)),
   Main.opAt 1987 (EvmSemantics.Operation.CompBit (EvmSemantics.Operation.CompareBitwiseOps.XOR)),
   Main.opAt 1988 (EvmSemantics.Operation.CompBit (EvmSemantics.Operation.CompareBitwiseOps.OR)),
   Main.pushAt 1989 32 38311713511462522110458585356116005585671870710873149374701065632428634475996,
   Main.pushAt 1990 2 448,
   Main.opAt 1991 (EvmSemantics.Operation.Env (EvmSemantics.Operation.EnvOps.CALLDATALOAD)),
   Main.opAt 1992 (EvmSemantics.Operation.CompBit (EvmSemantics.Operation.CompareBitwiseOps.XOR)),
   Main.opAt 1993 (EvmSemantics.Operation.CompBit (EvmSemantics.Operation.CompareBitwiseOps.OR)),
   Main.pushAt 1994 32 48151510786387428585737698962956619369166187671466117465503171502731926895950,
   Main.pushAt 1995 2 480,
   Main.opAt 1996 (EvmSemantics.Operation.Env (EvmSemantics.Operation.EnvOps.CALLDATALOAD)),
   Main.opAt 1997 (EvmSemantics.Operation.CompBit (EvmSemantics.Operation.CompareBitwiseOps.XOR)),
   Main.opAt 1998 (EvmSemantics.Operation.CompBit (EvmSemantics.Operation.CompareBitwiseOps.OR))
  ]

def check4Path :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [
   Main.pushAt 1999 32 61739249361961769659166632957096972008755669043881026467845481882835731896669,
   Main.pushAt 2000 2 512,
   Main.opAt 2001 (EvmSemantics.Operation.Env (EvmSemantics.Operation.EnvOps.CALLDATALOAD)),
   Main.opAt 2002 (EvmSemantics.Operation.CompBit (EvmSemantics.Operation.CompareBitwiseOps.XOR)),
   Main.opAt 2003 (EvmSemantics.Operation.CompBit (EvmSemantics.Operation.CompareBitwiseOps.OR)),
   Main.pushAt 2004 32 92675087986974552283256406722435621174918856095734773600019478320879083557616,
   Main.pushAt 2005 2 544,
   Main.opAt 2006 (EvmSemantics.Operation.Env (EvmSemantics.Operation.EnvOps.CALLDATALOAD)),
   Main.opAt 2007 (EvmSemantics.Operation.CompBit (EvmSemantics.Operation.CompareBitwiseOps.XOR)),
   Main.opAt 2008 (EvmSemantics.Operation.CompBit (EvmSemantics.Operation.CompareBitwiseOps.OR)),
   Main.pushAt 2009 32 54145282474824214972220247004005524167635414539690773466529844265217144481216,
   Main.pushAt 2010 2 576,
   Main.opAt 2011 (EvmSemantics.Operation.Env (EvmSemantics.Operation.EnvOps.CALLDATALOAD)),
   Main.opAt 2012 (EvmSemantics.Operation.CompBit (EvmSemantics.Operation.CompareBitwiseOps.XOR)),
   Main.opAt 2013 (EvmSemantics.Operation.CompBit (EvmSemantics.Operation.CompareBitwiseOps.OR)),
   Main.pushAt 2014 32 64827516786964288457452729860119806527709808231333806429784401219587764387840,
   Main.pushAt 2015 2 608,
   Main.opAt 2016 (EvmSemantics.Operation.Env (EvmSemantics.Operation.EnvOps.CALLDATALOAD)),
   Main.opAt 2017 (EvmSemantics.Operation.CompBit (EvmSemantics.Operation.CompareBitwiseOps.XOR)),
   Main.opAt 2018 (EvmSemantics.Operation.CompBit (EvmSemantics.Operation.CompareBitwiseOps.OR))
  ]

def branchIsZeroLocated :
    Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka :=
  Main.opAt 2019
    (EvmSemantics.Operation.CompBit (EvmSemantics.Operation.CompareBitwiseOps.ISZERO))

def branchPushLocated :
    Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka :=
  Main.pushAt 2020 2 3921

def branchJumpLocated :
    Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka :=
  Main.opAt 2021
    (EvmSemantics.Operation.StackMemFlow (EvmSemantics.Operation.StackMemFlowOps.JUMPI))

def branchPath :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [
   branchIsZeroLocated,
   branchPushLocated,
   branchJumpLocated
  ]

def branchIsZeroPath :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [branchIsZeroLocated]

def branchJumpPath :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [
   branchPushLocated,
   branchJumpLocated
  ]

theorem branchPath_eq : branchPath = branchIsZeroPath ++ branchJumpPath := by rfl

def fallbackPushLocated := Main.pushAt 2022 2 1314
def fallbackJumpLocated := Main.opAt 2023
  (EvmSemantics.Operation.StackMemFlow (EvmSemantics.Operation.StackMemFlowOps.JUMP))

def fallbackPath :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [fallbackPushLocated, fallbackJumpLocated]

@[simp] theorem fallbackPush_index : fallbackPushLocated.index = 2022 := rfl
@[simp] theorem fallbackPush_instruction :
    fallbackPushLocated.instruction = .push 2 (UInt256.ofNat 1314) := rfl
@[simp] theorem fallbackJump_index : fallbackJumpLocated.index = 2023 := rfl
@[simp] theorem fallbackJump_instruction : fallbackJumpLocated.instruction = .op .JUMP := rfl

def returnPath :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [
   Main.opAt 2024 (EvmSemantics.Operation.StackMemFlow (EvmSemantics.Operation.StackMemFlowOps.JUMPDEST)),
   Main.pushAt 2025 32 36457779276215628618107628175862952880503802480134169461413915661242852128650,
   Main.pushAt 2026 0 0,
   Main.opAt 2027 (EvmSemantics.Operation.StackMemFlow (EvmSemantics.Operation.StackMemFlowOps.MSTORE)),
   Main.pushAt 2028 32 87049543137291641647099327099349755118393366951315864702186066057471381150321,
   Main.pushAt 2029 1 32,
   Main.opAt 2030 (EvmSemantics.Operation.StackMemFlow (EvmSemantics.Operation.StackMemFlowOps.MSTORE)),
   Main.pushAt 2031 32 100461675459921706400033383628344108228127659798054063115947067974792041444897,
   Main.pushAt 2032 1 64,
   Main.opAt 2033 (EvmSemantics.Operation.StackMemFlow (EvmSemantics.Operation.StackMemFlowOps.MSTORE)),
   Main.pushAt 2034 32 92652640243433598898841338411780137466704615812747125847068622118856402577117,
   Main.pushAt 2035 1 96,
   Main.opAt 2036 (EvmSemantics.Operation.StackMemFlow (EvmSemantics.Operation.StackMemFlowOps.MSTORE)),
   Main.pushAt 2037 32 14159211218075883537326960255904060289806489979180585240426546259839689087273,
   Main.pushAt 2038 1 128,
   Main.opAt 2039 (EvmSemantics.Operation.StackMemFlow (EvmSemantics.Operation.StackMemFlowOps.MSTORE)),
   Main.pushAt 2040 32 67818750046613989747287612287447883644842343144736888277507620664030220336931,
   Main.pushAt 2041 1 160,
   Main.opAt 2042 (EvmSemantics.Operation.StackMemFlow (EvmSemantics.Operation.StackMemFlowOps.MSTORE)),
   Main.pushAt 2043 32 2618339351906218248436954888076772231186051744572579598192995074227528865064,
   Main.pushAt 2044 1 192,
   Main.opAt 2045 (EvmSemantics.Operation.StackMemFlow (EvmSemantics.Operation.StackMemFlowOps.MSTORE)),
   Main.pushAt 2046 32 9746032139171987504721760760529593857951721070820754662511731733855650243837,
   Main.pushAt 2047 1 224,
   Main.opAt 2048 (EvmSemantics.Operation.StackMemFlow (EvmSemantics.Operation.StackMemFlowOps.MSTORE)),
   Main.pushAt 2049 2 256,
   Main.pushAt 2050 0 0,
   Main.opAt 2051 (EvmSemantics.Operation.System (EvmSemantics.Operation.SystemOps.RETURN))
  ]

@[simp] theorem guardPC0 (i : Nat) (hlo : 1913 ≤ i) (hhi : i ≤ 1947) :
    Artifact.submissionArtifact.instructionPC i =
      [3133,3134,3135,3138,3139,3140,3141,3174,3175,3176,3177,3178,3211,3213,3214,3215,3216,3249,3251,3252,3253,3254,3287,3289,3290,3291,3292,3325,3327,3328,3329,3330,3363,3365,3366][i - 1913]! := by
  interval_cases i <;> decide

@[simp] theorem guardPC1 (i : Nat) (hlo : 1948 ≤ i) (hhi : i ≤ 1982) :
    Artifact.submissionArtifact.instructionPC i =
      [3367,3368,3401,3403,3404,3405,3406,3439,3441,3442,3443,3444,3477,3480,3481,3482,3483,3516,3519,3520,3521,3522,3555,3558,3559,3560,3561,3594,3597,3598,3599,3600,3633,3636,3637][i - 1948]! := by
  interval_cases i <;> decide

@[simp] theorem guardPC2 (i : Nat) (hlo : 1983 ≤ i) (hhi : i ≤ 2017) :
    Artifact.submissionArtifact.instructionPC i =
      [3638,3639,3672,3675,3676,3677,3678,3711,3714,3715,3716,3717,3750,3753,3754,3755,3756,3789,3792,3793,3794,3795,3828,3831,3832,3833,3834,3867,3870,3871,3872,3873,3906,3909,3910][i - 1983]! := by
  interval_cases i <;> decide

@[simp] theorem guardPC3 (i : Nat) (hlo : 2018 ≤ i) (hhi : i ≤ 2051) :
    Artifact.submissionArtifact.instructionPC i =
      [3911,3912,3913,3916,3917,3920,3921,3922,3955,3956,3957,3990,3992,3993,4026,4028,4029,4062,4064,4065,4098,4100,4101,4134,4136,4137,4170,4172,4173,4206,4208,4209,4212,4213][i - 2018]! := by
  interval_cases i <;> decide

end Challenge.Modexp.Submission.Proofs.Fast.GuardPaths
