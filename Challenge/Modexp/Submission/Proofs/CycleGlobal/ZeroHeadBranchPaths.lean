import Challenge.Modexp.Submission.Proofs.CycleGlobal.ShiftPaths
import Challenge.Modexp.Submission.Proofs.CycleGlobal.PCCertificate
noncomputable section
set_option maxRecDepth 40000
namespace CycleSubmission.Global.Fast.Shift
open Challenge.Modexp.Submission.Proofs.Bytecode
open EvmSemantics EvmSemantics.EVM
def blkCacheChoose : List (Challenge.EvmProof.Stepper.Located CycleSubmission.Artifact.artifact .Osaka) :=
  [opAt 8094 (.Dup ⟨11,by decide⟩),
   pushAt 8095 2 8420,
   opAt 8096 .JUMPI]
def blkCacheNormal : List (Challenge.EvmProof.Stepper.Located CycleSubmission.Artifact.artifact .Osaka) :=
  [opAt 6336 .JUMPDEST,
   pushAt 6337 1 33,
   opAt 6338 (.Dup ⟨1,by decide⟩),
   opAt 6339 .SHL,
   opAt 6340 (.Swap ⟨0,by decide⟩),
   opAt 6341 (.Dup ⟨14,by decide⟩),
   pushAt 6342 1 1,
   opAt 6343 .AND,
   opAt 6344 .SHR,
   opAt 6345 (.Dup ⟨1,by decide⟩),
   opAt 6346 .JUMP]
def blkCacheZero : List (Challenge.EvmProof.Stepper.Located CycleSubmission.Artifact.artifact .Osaka) :=
  [pushAt 8097 1 26,
   opAt 8098 (.Dup ⟨1,by decide⟩),
   opAt 8099 .SHL,
   opAt 8100 (.Swap ⟨0,by decide⟩),
   opAt 8101 (.Dup ⟨14,by decide⟩),
   pushAt 8102 1 1,
   opAt 8103 .AND,
   opAt 8104 .SHR,
   opAt 8105 (.Dup ⟨1,by decide⟩),
   opAt 8106 .JUMP]
@[simp] theorem rhoCachePC2065 : CycleSubmission.Artifact.artifact.instructionPC 8094 = 10735 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem rhoCachePC2066 : CycleSubmission.Artifact.artifact.instructionPC 8095 = 10736 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem rhoCachePC2067 : CycleSubmission.Artifact.artifact.instructionPC 8095 = 10736 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem rhoCachePC2068 : CycleSubmission.Artifact.artifact.instructionPC 8096 = 10739 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem rhoCachePC2069 : CycleSubmission.Artifact.artifact.instructionPC 8097 = 10740 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem rhoCachePC2070 : CycleSubmission.Artifact.artifact.instructionPC 8098 = 10742 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem rhoCachePC2071 : CycleSubmission.Artifact.artifact.instructionPC 8099 = 10743 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem rhoCachePC2072 : CycleSubmission.Artifact.artifact.instructionPC 8100 = 10744 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem rhoCachePC2073 : CycleSubmission.Artifact.artifact.instructionPC 8100 = 10744 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem rhoCachePC2074 : CycleSubmission.Artifact.artifact.instructionPC 8100 = 10744 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem rhoCachePC2075 : CycleSubmission.Artifact.artifact.instructionPC 8101 = 10745 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem rhoCachePC2076 : CycleSubmission.Artifact.artifact.instructionPC 8102 = 10746 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem rhoCachePC2077 : CycleSubmission.Artifact.artifact.instructionPC 8103 = 10748 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem rhoCachePC2078 : CycleSubmission.Artifact.artifact.instructionPC 8104 = 10749 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem rhoCachePC2079 : CycleSubmission.Artifact.artifact.instructionPC 8105 = 10750 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem rhoCachePC2080 : CycleSubmission.Artifact.artifact.instructionPC 8106 = 10751 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem rhoCachePC2081 : CycleSubmission.Artifact.artifact.instructionPC 6336 = 8420 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem rhoCachePC2082 : CycleSubmission.Artifact.artifact.instructionPC 6337 = 8421 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem rhoCachePC2083 : CycleSubmission.Artifact.artifact.instructionPC 6337 = 8421 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem rhoCachePC2084 : CycleSubmission.Artifact.artifact.instructionPC 6337 = 8421 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem rhoCachePC2085 : CycleSubmission.Artifact.artifact.instructionPC 6337 = 8421 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem rhoCachePC2086 : CycleSubmission.Artifact.artifact.instructionPC 6338 = 8423 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem rhoCachePC2087 : CycleSubmission.Artifact.artifact.instructionPC 6339 = 8424 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem rhoCachePC2088 : CycleSubmission.Artifact.artifact.instructionPC 6340 = 8425 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem rhoCachePC2089 : CycleSubmission.Artifact.artifact.instructionPC 6340 = 8425 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem rhoCachePC2090 : CycleSubmission.Artifact.artifact.instructionPC 6340 = 8425 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem rhoCachePC2091 : CycleSubmission.Artifact.artifact.instructionPC 6341 = 8426 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem rhoCachePC2092 : CycleSubmission.Artifact.artifact.instructionPC 6342 = 8427 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem rhoCachePC2093 : CycleSubmission.Artifact.artifact.instructionPC 6343 = 8429 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem rhoCachePC2094 : CycleSubmission.Artifact.artifact.instructionPC 6344 = 8430 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem rhoCachePC2095 : CycleSubmission.Artifact.artifact.instructionPC 6345 = 8431 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem rhoCachePC2096 : CycleSubmission.Artifact.artifact.instructionPC 6346 = 8432 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
def cacheBlock (mem : ByteArray) : List (Challenge.EvmProof.Stepper.Located CycleSubmission.Artifact.artifact .Osaka) :=
  blkCacheChoose++if (MachineState.readWord mem 1536).toNat = 0 then blkCacheZero else blkCacheNormal
@[simp] theorem readyPC2009 : CycleSubmission.Artifact.artifact.instructionPC 8040 = 10643 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem readyPC2010 : CycleSubmission.Artifact.artifact.instructionPC 8041 = 10644 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem readyPC2011 : CycleSubmission.Artifact.artifact.instructionPC 8042 = 10645 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem readyPC2012 : CycleSubmission.Artifact.artifact.instructionPC 8043 = 10646 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem readyPC2013 : CycleSubmission.Artifact.artifact.instructionPC 8044 = 10649 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem readyPC2014 : CycleSubmission.Artifact.artifact.instructionPC 8045 = 10650 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem readyPC2015 : CycleSubmission.Artifact.artifact.instructionPC 8046 = 10651 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem readyPC2016 : CycleSubmission.Artifact.artifact.instructionPC 8047 = 10652 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem readyPC2017 : CycleSubmission.Artifact.artifact.instructionPC 8048 = 10653 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem readyPC2018 : CycleSubmission.Artifact.artifact.instructionPC 8049 = 10656 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem readyPC2019 : CycleSubmission.Artifact.artifact.instructionPC 8050 = 10657 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem readyPC2020 : CycleSubmission.Artifact.artifact.instructionPC 8051 = 10660 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem readyPC2021 : CycleSubmission.Artifact.artifact.instructionPC 8052 = 10661 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem readyPC2022 : CycleSubmission.Artifact.artifact.instructionPC 8053 = 10663 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem readyPC2023 : CycleSubmission.Artifact.artifact.instructionPC 8054 = 10664 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem readyPC2024 : CycleSubmission.Artifact.artifact.instructionPC 8054 = 10664 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem readyPC2025 : CycleSubmission.Artifact.artifact.instructionPC 8055 = 10667 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem readyPC2026 : CycleSubmission.Artifact.artifact.instructionPC 8056 = 10668 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem readyPC2027 : CycleSubmission.Artifact.artifact.instructionPC 8057 = 10671 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem readyPC2028 : CycleSubmission.Artifact.artifact.instructionPC 8058 = 10672 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem readyPC2029 : CycleSubmission.Artifact.artifact.instructionPC 8059 = 10673 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem readyPC2030 : CycleSubmission.Artifact.artifact.instructionPC 8060 = 10674 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem readyPC2031 : CycleSubmission.Artifact.artifact.instructionPC 8061 = 10675 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem readyPC2032 : CycleSubmission.Artifact.artifact.instructionPC 8062 = 10677 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem readyPC2033 : CycleSubmission.Artifact.artifact.instructionPC 8063 = 10678 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem readyPC2034 : CycleSubmission.Artifact.artifact.instructionPC 8064 = 10681 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem readyPC2035 : CycleSubmission.Artifact.artifact.instructionPC 8065 = 10682 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem readyPC2036 : CycleSubmission.Artifact.artifact.instructionPC 8066 = 10683 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem readyPC2037 : CycleSubmission.Artifact.artifact.instructionPC 8067 = 10684 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem readyPC2038 : CycleSubmission.Artifact.artifact.instructionPC 8067 = 10684 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem readyPC2039 : CycleSubmission.Artifact.artifact.instructionPC 8068 = 10686 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem readyPC2040 : CycleSubmission.Artifact.artifact.instructionPC 8069 = 10687 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem readyPC2041 : CycleSubmission.Artifact.artifact.instructionPC 8070 = 10689 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem readyPC2042 : CycleSubmission.Artifact.artifact.instructionPC 8071 = 10690 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem readyPC2043 : CycleSubmission.Artifact.artifact.instructionPC 8072 = 10693 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem readyPC2044 : CycleSubmission.Artifact.artifact.instructionPC 8073 = 10694 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem readyPC2045 : CycleSubmission.Artifact.artifact.instructionPC 8074 = 10697 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem readyPC2046 : CycleSubmission.Artifact.artifact.instructionPC 8075 = 10698 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem readyPC2047 : CycleSubmission.Artifact.artifact.instructionPC 8076 = 10701 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem readyPC2048 : CycleSubmission.Artifact.artifact.instructionPC 8077 = 10702 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem readyPC2049 : CycleSubmission.Artifact.artifact.instructionPC 8078 = 10705 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem readyPC2050 : CycleSubmission.Artifact.artifact.instructionPC 8079 = 10706 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem readyPC2051 : CycleSubmission.Artifact.artifact.instructionPC 8080 = 10709 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem readyPC2052 : CycleSubmission.Artifact.artifact.instructionPC 8081 = 10710 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem readyPC2053 : CycleSubmission.Artifact.artifact.instructionPC 8082 = 10713 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem readyPC2054 : CycleSubmission.Artifact.artifact.instructionPC 8083 = 10714 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem readyPC2055 : CycleSubmission.Artifact.artifact.instructionPC 8084 = 10717 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem readyPC2056 : CycleSubmission.Artifact.artifact.instructionPC 8085 = 10718 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem readyPC2057 : CycleSubmission.Artifact.artifact.instructionPC 8086 = 10721 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem readyPC2058 : CycleSubmission.Artifact.artifact.instructionPC 8087 = 10722 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem readyPC2059 : CycleSubmission.Artifact.artifact.instructionPC 8088 = 10725 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem readyPC2060 : CycleSubmission.Artifact.artifact.instructionPC 8089 = 10726 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem readyPC2061 : CycleSubmission.Artifact.artifact.instructionPC 8090 = 10729 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem readyPC2062 : CycleSubmission.Artifact.artifact.instructionPC 8091 = 10730 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem readyPC2063 : CycleSubmission.Artifact.artifact.instructionPC 8092 = 10733 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem readyPC2064 : CycleSubmission.Artifact.artifact.instructionPC 8093 = 10734 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem readyPC2065 : CycleSubmission.Artifact.artifact.instructionPC 8094 = 10735 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem readyPC2066 : CycleSubmission.Artifact.artifact.instructionPC 8095 = 10736 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem readyPC2067 : CycleSubmission.Artifact.artifact.instructionPC 8095 = 10736 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem readyPC2068 : CycleSubmission.Artifact.artifact.instructionPC 8096 = 10739 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem readyPC2069 : CycleSubmission.Artifact.artifact.instructionPC 8097 = 10740 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem readyPC2070 : CycleSubmission.Artifact.artifact.instructionPC 8098 = 10742 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem readyPC2071 : CycleSubmission.Artifact.artifact.instructionPC 8099 = 10743 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem readyPC2072 : CycleSubmission.Artifact.artifact.instructionPC 8100 = 10744 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem readyPC2073 : CycleSubmission.Artifact.artifact.instructionPC 8100 = 10744 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem readyPC2074 : CycleSubmission.Artifact.artifact.instructionPC 8100 = 10744 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem readyPC2075 : CycleSubmission.Artifact.artifact.instructionPC 8101 = 10745 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem readyPC2076 : CycleSubmission.Artifact.artifact.instructionPC 8102 = 10746 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem readyPC2077 : CycleSubmission.Artifact.artifact.instructionPC 8103 = 10748 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem readyPC2078 : CycleSubmission.Artifact.artifact.instructionPC 8104 = 10749 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem readyPC2079 : CycleSubmission.Artifact.artifact.instructionPC 8105 = 10750 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem readyPC2080 : CycleSubmission.Artifact.artifact.instructionPC 8106 = 10751 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem readyPC2081 : CycleSubmission.Artifact.artifact.instructionPC 6336 = 8420 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem readyPC2082 : CycleSubmission.Artifact.artifact.instructionPC 6337 = 8421 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem readyPC2083 : CycleSubmission.Artifact.artifact.instructionPC 6338 = 8423 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem readyPC2084 : CycleSubmission.Artifact.artifact.instructionPC 6339 = 8424 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem readyPC2085 : CycleSubmission.Artifact.artifact.instructionPC 6340 = 8425 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem readyPC2086 : CycleSubmission.Artifact.artifact.instructionPC 6340 = 8425 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem readyPC2087 : CycleSubmission.Artifact.artifact.instructionPC 6340 = 8425 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem readyPC2088 : CycleSubmission.Artifact.artifact.instructionPC 6341 = 8426 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem readyPC2089 : CycleSubmission.Artifact.artifact.instructionPC 6342 = 8427 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem readyPC2090 : CycleSubmission.Artifact.artifact.instructionPC 6343 = 8429 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem readyPC2091 : CycleSubmission.Artifact.artifact.instructionPC 6344 = 8430 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem readyPC2092 : CycleSubmission.Artifact.artifact.instructionPC 6345 = 8431 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem readyPC2093 : CycleSubmission.Artifact.artifact.instructionPC 6346 = 8432 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
theorem jumpDestCacheNormal : Decode.isValidJumpDest CycleSubmission.Artifact.bytecode 8420 = true := by
  have h := CycleSubmission.Global.Binding.jumpDest 6336 (by rw [CycleSubmission.Artifact.instruction_get]; rfl)
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)] at h
  exact h
end CycleSubmission.Global.Fast.Shift
