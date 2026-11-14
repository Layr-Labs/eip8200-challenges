import Challenge.Modexp.Submission.Proofs.CycleGlobal.ShiftTrace2
import Challenge.Modexp.Submission.Proofs.CycleGlobal.ZeroRemainderMath
import Challenge.Modexp.Submission.Proofs.CycleGlobal.ZeroShiftWords
noncomputable section
set_option maxRecDepth 40000
set_option maxHeartbeats 8000000
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
namespace CycleSubmission.Global.Fast.Shift
open Challenge.Modexp.Submission.Proofs
open Challenge.Modexp.Submission.Proofs.Fast
open Challenge.Modexp.Submission.Proofs.Fast.Shift
open Challenge.Modexp.Submission.Proofs.Bytecode
open EvmSemantics EvmSemantics.EVM
open CycleSubmission.Global.ZeroShiftMath
open CycleSubmission.Global.ZeroRemainderMath
abbrev zeroJoinState := estimate40
@[simp] theorem preloadGTWord (a b : UInt256) : UInt256.gt a b = UInt256.lt b a := rfl
@[simp] theorem preloadHDGTPC2851 : CycleSubmission.Artifact.artifact.instructionPC 7836 = 10352 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem preloadHDGTPC2852 : CycleSubmission.Artifact.artifact.instructionPC 7837 = 10353 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem preloadHDGTPC2853 : CycleSubmission.Artifact.artifact.instructionPC 7838 = 10354 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem preloadHDGTPC2854 : CycleSubmission.Artifact.artifact.instructionPC 7839 = 10357 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem preloadHDGTPC2855 : CycleSubmission.Artifact.artifact.instructionPC 7840 = 10360 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem preloadHDGTPC2856 : CycleSubmission.Artifact.artifact.instructionPC 7841 = 10361 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem preloadHDGTPC2857 : CycleSubmission.Artifact.artifact.instructionPC 7842 = 10364 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem preloadHDGTPC2858 : CycleSubmission.Artifact.artifact.instructionPC 7843 = 10365 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem preloadHDGTPC2859 : CycleSubmission.Artifact.artifact.instructionPC 7844 = 10366 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem preloadHDGTPC2860 : CycleSubmission.Artifact.artifact.instructionPC 7845 = 10369 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem preloadHDGTPC2861 : CycleSubmission.Artifact.artifact.instructionPC 7846 = 10370 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem preloadHDGTPC2862 : CycleSubmission.Artifact.artifact.instructionPC 7847 = 10371 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem preloadHDGTPC2863 : CycleSubmission.Artifact.artifact.instructionPC 7848 = 10372 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem preloadHDGTPC2864 : CycleSubmission.Artifact.artifact.instructionPC 7849 = 10373 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem preloadHDGTPC2865 : CycleSubmission.Artifact.artifact.instructionPC 7850 = 10374 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem preloadHDGTPC2866 : CycleSubmission.Artifact.artifact.instructionPC 7851 = 10375 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem preloadHDGTPC2867 : CycleSubmission.Artifact.artifact.instructionPC 7852 = 10376 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem preloadHDGTPC2868 : CycleSubmission.Artifact.artifact.instructionPC 7853 = 10377 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem preloadHDGTPC2869 : CycleSubmission.Artifact.artifact.instructionPC 7854 = 10378 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem preloadHDGTPC2870 : CycleSubmission.Artifact.artifact.instructionPC 7855 = 10379 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem preloadHDGTPC2871 : CycleSubmission.Artifact.artifact.instructionPC 7856 = 10380 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem preloadHDGTPC2872 : CycleSubmission.Artifact.artifact.instructionPC 7857 = 10381 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem preloadHDGTPC2873 : CycleSubmission.Artifact.artifact.instructionPC 7858 = 10382 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem preloadHDGTPC2874 : CycleSubmission.Artifact.artifact.instructionPC 7859 = 10383 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem preloadHDGTPC2875 : CycleSubmission.Artifact.artifact.instructionPC 7860 = 10384 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem preloadHDGTPC2876 : CycleSubmission.Artifact.artifact.instructionPC 7861 = 10386 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem preloadHDGTPC2877 : CycleSubmission.Artifact.artifact.instructionPC 7862 = 10387 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem preloadHDGTPC2878 : CycleSubmission.Artifact.artifact.instructionPC 7863 = 10388 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem preloadHDGTPC2879 : CycleSubmission.Artifact.artifact.instructionPC 7864 = 10389 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem preloadHDGTPC2880 : CycleSubmission.Artifact.artifact.instructionPC 7865 = 10390 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem preloadHDGTPC2881 : CycleSubmission.Artifact.artifact.instructionPC 7866 = 10391 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem preloadHDGTPC2882 : CycleSubmission.Artifact.artifact.instructionPC 7867 = 10394 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem preloadHDGTPC2998 : CycleSubmission.Artifact.artifact.instructionPC 7869 = 10396 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem preloadHDGTPC2999 : CycleSubmission.Artifact.artifact.instructionPC 7870 = 10397 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem preloadHDGTPC3000 : CycleSubmission.Artifact.artifact.instructionPC 7871 = 10398 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem preloadHDGTPC3001 : CycleSubmission.Artifact.artifact.instructionPC 7872 = 10401 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem preloadHDGTPC3002 : CycleSubmission.Artifact.artifact.instructionPC 7873 = 10404 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem preloadHDGTPC3003 : CycleSubmission.Artifact.artifact.instructionPC 7874 = 10405 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem preloadHDGTPC3004 : CycleSubmission.Artifact.artifact.instructionPC 7875 = 10408 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem preloadHDGTPC3005 : CycleSubmission.Artifact.artifact.instructionPC 7876 = 10409 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem preloadHDGTPC3006 : CycleSubmission.Artifact.artifact.instructionPC 7877 = 10410 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem preloadHDGTPC3007 : CycleSubmission.Artifact.artifact.instructionPC 7878 = 10413 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem preloadHDGTPC3008 : CycleSubmission.Artifact.artifact.instructionPC 7879 = 10414 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem preloadHDGTPC3009 : CycleSubmission.Artifact.artifact.instructionPC 7880 = 10415 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem preloadHDGTPC3010 : CycleSubmission.Artifact.artifact.instructionPC 7881 = 10416 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem preloadHDGTPC3011 : CycleSubmission.Artifact.artifact.instructionPC 7882 = 10417 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem preloadHDGTPC3012 : CycleSubmission.Artifact.artifact.instructionPC 7883 = 10418 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem preloadHDGTPC3013 : CycleSubmission.Artifact.artifact.instructionPC 7884 = 10419 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem preloadHDGTPC3014 : CycleSubmission.Artifact.artifact.instructionPC 7885 = 10420 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem preloadHDGTPC3015 : CycleSubmission.Artifact.artifact.instructionPC 7886 = 10421 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem preloadHDGTPC3016 : CycleSubmission.Artifact.artifact.instructionPC 7887 = 10422 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem preloadHDGTPC3017 : CycleSubmission.Artifact.artifact.instructionPC 7888 = 10423 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem preloadHDGTPC3018 : CycleSubmission.Artifact.artifact.instructionPC 7889 = 10424 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem preloadHDGTPC3019 : CycleSubmission.Artifact.artifact.instructionPC 7890 = 10425 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem preloadHDGTPC3020 : CycleSubmission.Artifact.artifact.instructionPC 7891 = 10426 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem preloadHDGTPC3021 : CycleSubmission.Artifact.artifact.instructionPC 7892 = 10427 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem preloadHDGTPC3022 : CycleSubmission.Artifact.artifact.instructionPC 7893 = 10428 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem preloadHDGTPC3023 : CycleSubmission.Artifact.artifact.instructionPC 7894 = 10430 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem preloadHDGTPC3024 : CycleSubmission.Artifact.artifact.instructionPC 7895 = 10431 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem preloadHDGTPC3025 : CycleSubmission.Artifact.artifact.instructionPC 7896 = 10432 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem preloadHDGTPC3026 : CycleSubmission.Artifact.artifact.instructionPC 7897 = 10433 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem preloadHDGTPC3027 : CycleSubmission.Artifact.artifact.instructionPC 7898 = 10434 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem preloadHDGTPC3028 : CycleSubmission.Artifact.artifact.instructionPC 7899 = 10435 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem preloadHDGTPC3029 : CycleSubmission.Artifact.artifact.instructionPC 7900 = 10438 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem rhoPC2142 : CycleSubmission.Artifact.artifact.instructionPC 2261 = 2932 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem rhoPC2854 : CycleSubmission.Artifact.artifact.instructionPC 7836 = 10352 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem rhoPC2855 : CycleSubmission.Artifact.artifact.instructionPC 7837 = 10353 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem rhoPC2856 : CycleSubmission.Artifact.artifact.instructionPC 7838 = 10354 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem rhoPC2857 : CycleSubmission.Artifact.artifact.instructionPC 7839 = 10357 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem rhoPC2858 : CycleSubmission.Artifact.artifact.instructionPC 7840 = 10360 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem rhoPC2859 : CycleSubmission.Artifact.artifact.instructionPC 7841 = 10361 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem rhoPC2860 : CycleSubmission.Artifact.artifact.instructionPC 7842 = 10364 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem rhoPC2861 : CycleSubmission.Artifact.artifact.instructionPC 7844 = 10366 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem rhoPC2862 : CycleSubmission.Artifact.artifact.instructionPC 7845 = 10369 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem rhoPC2863 : CycleSubmission.Artifact.artifact.instructionPC 7846 = 10370 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem rhoPC2864 : CycleSubmission.Artifact.artifact.instructionPC 7847 = 10371 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem rhoPC2865 : CycleSubmission.Artifact.artifact.instructionPC 7848 = 10372 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem rhoPC2866 : CycleSubmission.Artifact.artifact.instructionPC 7849 = 10373 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem rhoPC2867 : CycleSubmission.Artifact.artifact.instructionPC 7850 = 10374 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem rhoPC2868 : CycleSubmission.Artifact.artifact.instructionPC 7851 = 10375 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem rhoPC2869 : CycleSubmission.Artifact.artifact.instructionPC 7852 = 10376 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem rhoPC2870 : CycleSubmission.Artifact.artifact.instructionPC 7853 = 10377 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem rhoPC2871 : CycleSubmission.Artifact.artifact.instructionPC 7854 = 10378 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem rhoPC2872 : CycleSubmission.Artifact.artifact.instructionPC 7855 = 10379 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem rhoPC2873 : CycleSubmission.Artifact.artifact.instructionPC 7856 = 10380 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem rhoPC2874 : CycleSubmission.Artifact.artifact.instructionPC 7857 = 10381 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem rhoPC2875 : CycleSubmission.Artifact.artifact.instructionPC 7858 = 10382 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem rhoPC2876 : CycleSubmission.Artifact.artifact.instructionPC 7859 = 10383 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem rhoPC2877 : CycleSubmission.Artifact.artifact.instructionPC 7860 = 10384 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem rhoPC2878 : CycleSubmission.Artifact.artifact.instructionPC 7861 = 10386 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem rhoPC2879 : CycleSubmission.Artifact.artifact.instructionPC 7862 = 10387 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem rhoPC2880 : CycleSubmission.Artifact.artifact.instructionPC 7863 = 10388 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem rhoPC2881 : CycleSubmission.Artifact.artifact.instructionPC 7863 = 10388 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem rhoPC2882 : CycleSubmission.Artifact.artifact.instructionPC 7863 = 10388 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem rhoPC2883 : CycleSubmission.Artifact.artifact.instructionPC 7864 = 10389 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem rhoPC2884 : CycleSubmission.Artifact.artifact.instructionPC 7865 = 10390 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem rhoPC2885 : CycleSubmission.Artifact.artifact.instructionPC 7866 = 10391 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem rhoPC2886 : CycleSubmission.Artifact.artifact.instructionPC 7867 = 10394 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem rhoPC3002 : CycleSubmission.Artifact.artifact.instructionPC 7869 = 10396 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem rhoPC3003 : CycleSubmission.Artifact.artifact.instructionPC 7870 = 10397 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem rhoPC3004 : CycleSubmission.Artifact.artifact.instructionPC 7871 = 10398 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem rhoPC3005 : CycleSubmission.Artifact.artifact.instructionPC 7872 = 10401 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem rhoPC3006 : CycleSubmission.Artifact.artifact.instructionPC 7873 = 10404 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem rhoPC3007 : CycleSubmission.Artifact.artifact.instructionPC 7874 = 10405 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem rhoPC3008 : CycleSubmission.Artifact.artifact.instructionPC 7875 = 10408 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem rhoPC3009 : CycleSubmission.Artifact.artifact.instructionPC 7877 = 10410 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem rhoPC3010 : CycleSubmission.Artifact.artifact.instructionPC 7878 = 10413 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem rhoPC3011 : CycleSubmission.Artifact.artifact.instructionPC 7879 = 10414 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem rhoPC3012 : CycleSubmission.Artifact.artifact.instructionPC 7880 = 10415 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem rhoPC3013 : CycleSubmission.Artifact.artifact.instructionPC 7881 = 10416 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem rhoPC3014 : CycleSubmission.Artifact.artifact.instructionPC 7882 = 10417 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem rhoPC3015 : CycleSubmission.Artifact.artifact.instructionPC 7883 = 10418 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem rhoPC3016 : CycleSubmission.Artifact.artifact.instructionPC 7884 = 10419 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem rhoPC3017 : CycleSubmission.Artifact.artifact.instructionPC 7885 = 10420 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem rhoPC3018 : CycleSubmission.Artifact.artifact.instructionPC 7886 = 10421 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem rhoPC3019 : CycleSubmission.Artifact.artifact.instructionPC 7887 = 10422 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem rhoPC3020 : CycleSubmission.Artifact.artifact.instructionPC 7888 = 10423 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem rhoPC3021 : CycleSubmission.Artifact.artifact.instructionPC 7889 = 10424 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem rhoPC3022 : CycleSubmission.Artifact.artifact.instructionPC 7890 = 10425 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem rhoPC3023 : CycleSubmission.Artifact.artifact.instructionPC 7891 = 10426 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem rhoPC3024 : CycleSubmission.Artifact.artifact.instructionPC 7892 = 10427 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem rhoPC3025 : CycleSubmission.Artifact.artifact.instructionPC 7893 = 10428 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem rhoPC3026 : CycleSubmission.Artifact.artifact.instructionPC 7894 = 10430 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem rhoPC3027 : CycleSubmission.Artifact.artifact.instructionPC 7895 = 10431 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem rhoPC3028 : CycleSubmission.Artifact.artifact.instructionPC 7896 = 10432 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem rhoPC3029 : CycleSubmission.Artifact.artifact.instructionPC 7896 = 10432 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem rhoPC3030 : CycleSubmission.Artifact.artifact.instructionPC 7896 = 10432 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem rhoPC3031 : CycleSubmission.Artifact.artifact.instructionPC 7897 = 10433 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem rhoPC3032 : CycleSubmission.Artifact.artifact.instructionPC 7898 = 10434 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem rhoPC3033 : CycleSubmission.Artifact.artifact.instructionPC 7899 = 10435 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem rhoPC3034 : CycleSubmission.Artifact.artifact.instructionPC 7900 = 10438 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem rhoPC8318 : CycleSubmission.Artifact.artifact.instructionPC 8155 = 10796 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
theorem jumpDestZeroJoin8 : Decode.isValidJumpDest CycleSubmission.Artifact.bytecode 2932 = true := by
  have h := CycleSubmission.Global.Binding.jumpDest 2261 (by rw [CycleSubmission.Artifact.instruction_get]; rfl)
  simpa only [rhoPC2142] using h
theorem run_zeroPrefix8 (z : UInt256) (s : State) (mem : ByteArray)
    (n bsize esize msize k : Nat) (hn : n = 8)
    (hpre : PreOK mem) (hd : (MachineState.readWord mem 0).toNat ≠ 0)
    (hshift : (MachineState.readWord mem 1536).toNat = 0)
    (hbs : bsize = 32*n) (hact : 88 ≤ s.activeWords.toNat)
    (hcode : s.executionEnv.code = CycleSubmission.Artifact.bytecode)
    (hrun : s.halt = .Running) :
    Challenge.EvmProof.Stepper.runLocatedBlock blkZero8
      (shiftLoopState z s mem n bsize esize msize k) =
      some (zeroJoinState z s mem n bsize esize msize k) := by
  have hkw : MachineState.readWord mem 1536 = UInt256.ofNat 0 := by
    apply Challenge.EvmProof.Word.word_ext
    exact hshift
  have hsw := zero_complement mem hpre hd hkw
  have hfix := Exp.activeWords_fix2 s 2080 (32*n) 2112 (32*n)
    (by omega) (by omega) (by omega) (by omega) hact
  have h2080 := Monpro.activeWords_fix s 2080 32 (by decide) (by omega) hact
  have h2112 := Monpro.activeWords_fix s 2112 32 (by decide) (by omega) hact
  have huv : ∀ a,a + 32 ≤ 2080 → MachineState.readWord (uMem mem n) a =
      MachineState.readWord mem a := by
    intro a ha; exact Shift.uMem_readWord_disjoint mem n a (Or.inl ha)
  have hr2080 := uMem0_readWord mem n 2080 (by omega)
  have hr2112 := uMem0_readWord mem n 2112 (by omega)
  have hu1312 := huv 1312 (by omega)
  have hu1344 := huv 1344 (by omega)
  have hu1376 := huv 1376 (by omega)
  have hu1408 := huv 1408 (by omega)
  have hu1440 := huv 1440 (by omega)
  have hu1472 := huv 1472 (by omega)
  have hu1504 := huv 1504 (by omega)
  have hu1632 := huv 1632 (by omega)
  have hu1664 := huv 1664 (by omega)
  have hu1568 := huv 1568 (by omega)
  have hu1536 := huv 1536 (by omega)
  have hu32 := huv 32 (by omega)
  have hkU : MachineState.readWord (uMem mem n) 1536 = UInt256.ofNat 0 := hu1536.trans hkw
  have hxU : MachineState.readWord (uMem mem n) 1600 = UInt256.ofNat 256 :=
    (huv 1600 (by omega)).trans hsw
  have hpreU := PreOK_uMem mem n (by omega) hpre
  have hdU : (MachineState.readWord (uMem mem n) 0).toNat ≠ 0 := by
    rw [huv 0 (by omega)]; exact hd
  have hinv := (divisor_and_inverse (uMem mem n) hpreU hdU hkU).2
  let rho := UInt256.addMod (MachineState.readWord (uMem mem n) 2112)
    (UInt256.mulMod (MachineState.readWord (uMem mem n) 2080)
      (MachineState.readWord (uMem mem n) 1632) (MachineState.readWord (uMem mem n) 1568))
    (MachineState.readWord (uMem mem n) 1568)
  have hres := residual (MachineState.readWord (uMem mem n) 0)
    (MachineState.readWord (uMem mem n) 1664)
    (MachineState.readWord (uMem mem n) 2112) rho hinv
  have hu0 := huv 0 (by omega)
  dsimp only [rho] at hres
  simp only [← hr2080,← hr2112,hu0,hu1664,hu1632,hu1568] at hres
  subst n
  simp (config := {maxSteps := 900000})
    [blkZero8,zeroJoinState,estimate40,shiftLoopState,slotKState,entrySlots,aprevSlot,hdSlot,
      headWord,loopPC,headPC,opAt,pushAt,wfOp,hshift,hkw,hsw,
      CycleSubmission.Global.ZeroShiftMath.head,CycleSubmission.Global.ZeroShiftMath.zeroHead,
      CycleSubmission.Global.ZeroShiftMath.normalHead,
      Challenge.EvmProof.Stepper.runLocatedBlock,Challenge.EvmProof.Stepper.runLocated,
      Challenge.EvmProof.Stepper.runInstr,hcode,hrun,hbs,
      outer,Exp.outer,uMem0,Exp.mcopyMem,
      State.activeWordsAfterUInt256,State.activeWordsAfterUInt256_2,
      hfix,h2080,h2112,hr2080,hr2112,
      hu1312,hu1344,hu1376,hu1408,hu1440,hu1472,hu1504,hu1632,hu1664,hu1568,hu1536,hu32,
      hkU,hxU,shr_zero,shl_256,add_ofNat_zero,
      jumpDestZeroJoin8,Challenge.EvmProof.Word.literal_eq_ofNat,
      Challenge.EvmProof.Word.word_toNat_ofNat,Challenge.EvmProof.Word.succ_ofNat_mod,
      Challenge.EvmProof.Word.ofNat_add_mod,List.exchange,CycleSubmission.Prepared.Arithmetic.amC,
      CycleSubmission.Prepared.Arithmetic.mulC,rho] at hres ⊢
  simp only [← hr2080,← hr2112,hu0,uMem0,Exp.mcopyMem,hres]
  trivial
#print axioms run_zeroPrefix8
theorem jumpDestZeroJoin4 : Decode.isValidJumpDest CycleSubmission.Artifact.bytecode 10796 = true := by
  have h := CycleSubmission.Global.Binding.jumpDest 8155 (by rw [CycleSubmission.Artifact.instruction_get]; rfl)
  simpa only [rhoPC8318] using h
theorem run_zeroPrefix4 (z : UInt256) (s : State) (mem : ByteArray)
    (n bsize esize msize k : Nat) (hn : n = 4)
    (hpre : PreOK mem) (hd : (MachineState.readWord mem 0).toNat ≠ 0)
    (hshift : (MachineState.readWord mem 1536).toNat = 0)
    (hbs : bsize = 32*n) (hact : 88 ≤ s.activeWords.toNat)
    (hcode : s.executionEnv.code = CycleSubmission.Artifact.bytecode)
    (hrun : s.halt = .Running) :
    Challenge.EvmProof.Stepper.runLocatedBlock blkZero4
      (shiftLoopState z s mem n bsize esize msize k) =
      some (zeroJoinState z s mem n bsize esize msize k) := by
  have hkw : MachineState.readWord mem 1536 = UInt256.ofNat 0 := by
    apply Challenge.EvmProof.Word.word_ext
    exact hshift
  have hsw := zero_complement mem hpre hd hkw
  have hfix := Exp.activeWords_fix2 s 2080 (32*n) 2112 (32*n)
    (by omega) (by omega) (by omega) (by omega) hact
  have h2080 := Monpro.activeWords_fix s 2080 32 (by decide) (by omega) hact
  have h2112 := Monpro.activeWords_fix s 2112 32 (by decide) (by omega) hact
  have huv : ∀ a,a + 32 ≤ 2080 → MachineState.readWord (uMem mem n) a =
      MachineState.readWord mem a := by
    intro a ha; exact Shift.uMem_readWord_disjoint mem n a (Or.inl ha)
  have hr2080 := uMem0_readWord mem n 2080 (by omega)
  have hr2112 := uMem0_readWord mem n 2112 (by omega)
  have hu1312 := huv 1312 (by omega)
  have hu1344 := huv 1344 (by omega)
  have hu1376 := huv 1376 (by omega)
  have hu1408 := huv 1408 (by omega)
  have hu1440 := huv 1440 (by omega)
  have hu1472 := huv 1472 (by omega)
  have hu1504 := huv 1504 (by omega)
  have hu1632 := huv 1632 (by omega)
  have hu1664 := huv 1664 (by omega)
  have hu1568 := huv 1568 (by omega)
  have hu1536 := huv 1536 (by omega)
  have hu32 := huv 32 (by omega)
  have hkU : MachineState.readWord (uMem mem n) 1536 = UInt256.ofNat 0 := hu1536.trans hkw
  have hxU : MachineState.readWord (uMem mem n) 1600 = UInt256.ofNat 256 :=
    (huv 1600 (by omega)).trans hsw
  have hpreU := PreOK_uMem mem n (by omega) hpre
  have hdU : (MachineState.readWord (uMem mem n) 0).toNat ≠ 0 := by
    rw [huv 0 (by omega)]; exact hd
  have hinv := (divisor_and_inverse (uMem mem n) hpreU hdU hkU).2
  let rho := UInt256.addMod (MachineState.readWord (uMem mem n) 2112)
    (UInt256.mulMod (MachineState.readWord (uMem mem n) 2080)
      (MachineState.readWord (uMem mem n) 1632) (MachineState.readWord (uMem mem n) 1568))
    (MachineState.readWord (uMem mem n) 1568)
  have hres := residual (MachineState.readWord (uMem mem n) 0)
    (MachineState.readWord (uMem mem n) 1664)
    (MachineState.readWord (uMem mem n) 2112) rho hinv
  have hu0 := huv 0 (by omega)
  dsimp only [rho] at hres
  simp only [← hr2080,← hr2112,hu0,hu1664,hu1632,hu1568] at hres
  subst n
  simp (config := {maxSteps := 900000})
    [blkZero4,zeroJoinState,estimate40,shiftLoopState,slotKState,entrySlots,aprevSlot,hdSlot,
      headWord,loopPC,headPC,opAt,pushAt,wfOp,hshift,hkw,hsw,
      CycleSubmission.Global.ZeroShiftMath.head,CycleSubmission.Global.ZeroShiftMath.zeroHead,
      CycleSubmission.Global.ZeroShiftMath.normalHead,
      Challenge.EvmProof.Stepper.runLocatedBlock,Challenge.EvmProof.Stepper.runLocated,
      Challenge.EvmProof.Stepper.runInstr,hcode,hrun,hbs,
      outer,Exp.outer,uMem0,Exp.mcopyMem,
      State.activeWordsAfterUInt256,State.activeWordsAfterUInt256_2,
      hfix,h2080,h2112,hr2080,hr2112,
      hu1312,hu1344,hu1376,hu1408,hu1440,hu1472,hu1504,hu1632,hu1664,hu1568,hu1536,hu32,
      hkU,hxU,shr_zero,shl_256,add_ofNat_zero,
      jumpDestZeroJoin4,Challenge.EvmProof.Word.literal_eq_ofNat,
      Challenge.EvmProof.Word.word_toNat_ofNat,Challenge.EvmProof.Word.succ_ofNat_mod,
      Challenge.EvmProof.Word.ofNat_add_mod,List.exchange,CycleSubmission.Prepared.Arithmetic.amC,
      CycleSubmission.Prepared.Arithmetic.mulC,rho] at hres ⊢
  simp only [← hr2080,← hr2112,hu0,uMem0,Exp.mcopyMem,hres]
  trivial
#print axioms run_zeroPrefix4
theorem jumpDestLoop2684 : Decode.isValidJumpDest CycleSubmission.Artifact.bytecode 2874 = true := by
  have h := CycleSubmission.Global.Binding.jumpDest 2216 (by rw [CycleSubmission.Artifact.instruction_get]; rfl)
  have hp : CycleSubmission.Artifact.artifact.instructionPC 2216 = 2874 := by
    rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
  simpa only [hp] using h
theorem jumpDestLoop10692 : Decode.isValidJumpDest CycleSubmission.Artifact.bytecode 10738 = true := by
  have h := CycleSubmission.Global.Binding.jumpDest 8110 (by rw [CycleSubmission.Artifact.instruction_get]; rfl)
  have hp : CycleSubmission.Artifact.artifact.instructionPC 8110 = 10738 := by
    rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
  simpa only [hp] using h
theorem jumpDestLoop3711 : Decode.isValidJumpDest CycleSubmission.Artifact.bytecode 10352 = true := by
  have h := CycleSubmission.Global.Binding.jumpDest 7836 (by rw [CycleSubmission.Artifact.instruction_get]; rfl)
  have hp : CycleSubmission.Artifact.artifact.instructionPC 7836 = 10352 := by
    rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
  simpa only [hp] using h
theorem jumpDestLoop3879 : Decode.isValidJumpDest CycleSubmission.Artifact.bytecode 10396 = true := by
  have h := CycleSubmission.Global.Binding.jumpDest 7869 (by rw [CycleSubmission.Artifact.instruction_get]; rfl)
  have hp : CycleSubmission.Artifact.artifact.instructionPC 7869 = 10396 := by
    rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
  simpa only [hp] using h
theorem jumpDestLoop (mem : ByteArray) (n : Nat) :
    Decode.isValidJumpDest CycleSubmission.Artifact.bytecode (loopPC mem n) = true := by
  unfold loopPC CycleSubmission.Global.ZeroShiftMath.head
    CycleSubmission.Global.ZeroShiftMath.zeroHead CycleSubmission.Global.ZeroShiftMath.normalHead
  split_ifs
  · exact jumpDestLoop3879
  · exact jumpDestLoop3711
  · exact jumpDestLoop10692
  · exact jumpDestLoop2684
end CycleSubmission.Global.Fast.Shift
