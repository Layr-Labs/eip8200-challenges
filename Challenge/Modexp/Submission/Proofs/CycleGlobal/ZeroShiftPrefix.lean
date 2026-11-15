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
@[simp] theorem preloadHDGTPC2851 : CycleSubmission.Artifact.artifact.instructionPC 7984 = 10571 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem preloadHDGTPC2852 : CycleSubmission.Artifact.artifact.instructionPC 7985 = 10572 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem preloadHDGTPC2853 : CycleSubmission.Artifact.artifact.instructionPC 7986 = 10573 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem preloadHDGTPC2854 : CycleSubmission.Artifact.artifact.instructionPC 7987 = 10576 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem preloadHDGTPC2855 : CycleSubmission.Artifact.artifact.instructionPC 7988 = 10579 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem preloadHDGTPC2856 : CycleSubmission.Artifact.artifact.instructionPC 7989 = 10580 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem preloadHDGTPC2857 : CycleSubmission.Artifact.artifact.instructionPC 7990 = 10583 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem preloadHDGTPC2858 : CycleSubmission.Artifact.artifact.instructionPC 7991 = 10584 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem preloadHDGTPC2859 : CycleSubmission.Artifact.artifact.instructionPC 7992 = 10585 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem preloadHDGTPC2860 : CycleSubmission.Artifact.artifact.instructionPC 7993 = 10588 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem preloadHDGTPC2861 : CycleSubmission.Artifact.artifact.instructionPC 7994 = 10589 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem preloadHDGTPC2862 : CycleSubmission.Artifact.artifact.instructionPC 7995 = 10590 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem preloadHDGTPC2863 : CycleSubmission.Artifact.artifact.instructionPC 7996 = 10591 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem preloadHDGTPC2864 : CycleSubmission.Artifact.artifact.instructionPC 7997 = 10592 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem preloadHDGTPC2865 : CycleSubmission.Artifact.artifact.instructionPC 7998 = 10593 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem preloadHDGTPC2866 : CycleSubmission.Artifact.artifact.instructionPC 7999 = 10594 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem preloadHDGTPC2867 : CycleSubmission.Artifact.artifact.instructionPC 8000 = 10595 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem preloadHDGTPC2868 : CycleSubmission.Artifact.artifact.instructionPC 8001 = 10596 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem preloadHDGTPC2869 : CycleSubmission.Artifact.artifact.instructionPC 8002 = 10597 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem preloadHDGTPC2870 : CycleSubmission.Artifact.artifact.instructionPC 8003 = 10598 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem preloadHDGTPC2871 : CycleSubmission.Artifact.artifact.instructionPC 8004 = 10599 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem preloadHDGTPC2872 : CycleSubmission.Artifact.artifact.instructionPC 8005 = 10600 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem preloadHDGTPC2873 : CycleSubmission.Artifact.artifact.instructionPC 8006 = 10601 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem preloadHDGTPC2874 : CycleSubmission.Artifact.artifact.instructionPC 8007 = 10602 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem preloadHDGTPC2875 : CycleSubmission.Artifact.artifact.instructionPC 8008 = 10603 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem preloadHDGTPC2876 : CycleSubmission.Artifact.artifact.instructionPC 8009 = 10605 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem preloadHDGTPC2877 : CycleSubmission.Artifact.artifact.instructionPC 8010 = 10606 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem preloadHDGTPC2878 : CycleSubmission.Artifact.artifact.instructionPC 8011 = 10607 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem preloadHDGTPC2879 : CycleSubmission.Artifact.artifact.instructionPC 8012 = 10608 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem preloadHDGTPC2880 : CycleSubmission.Artifact.artifact.instructionPC 8013 = 10609 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem preloadHDGTPC2881 : CycleSubmission.Artifact.artifact.instructionPC 8014 = 10610 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem preloadHDGTPC2882 : CycleSubmission.Artifact.artifact.instructionPC 8015 = 10613 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem preloadHDGTPC2998 : CycleSubmission.Artifact.artifact.instructionPC 8017 = 10615 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem preloadHDGTPC2999 : CycleSubmission.Artifact.artifact.instructionPC 8018 = 10616 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem preloadHDGTPC3000 : CycleSubmission.Artifact.artifact.instructionPC 8019 = 10617 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem preloadHDGTPC3001 : CycleSubmission.Artifact.artifact.instructionPC 8020 = 10620 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem preloadHDGTPC3002 : CycleSubmission.Artifact.artifact.instructionPC 8021 = 10623 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem preloadHDGTPC3003 : CycleSubmission.Artifact.artifact.instructionPC 8022 = 10624 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem preloadHDGTPC3004 : CycleSubmission.Artifact.artifact.instructionPC 8023 = 10627 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem preloadHDGTPC3005 : CycleSubmission.Artifact.artifact.instructionPC 8024 = 10628 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem preloadHDGTPC3006 : CycleSubmission.Artifact.artifact.instructionPC 8025 = 10629 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem preloadHDGTPC3007 : CycleSubmission.Artifact.artifact.instructionPC 8026 = 10632 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem preloadHDGTPC3008 : CycleSubmission.Artifact.artifact.instructionPC 8027 = 10633 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem preloadHDGTPC3009 : CycleSubmission.Artifact.artifact.instructionPC 8028 = 10634 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem preloadHDGTPC3010 : CycleSubmission.Artifact.artifact.instructionPC 8029 = 10635 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem preloadHDGTPC3011 : CycleSubmission.Artifact.artifact.instructionPC 8030 = 10636 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem preloadHDGTPC3012 : CycleSubmission.Artifact.artifact.instructionPC 8031 = 10637 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem preloadHDGTPC3013 : CycleSubmission.Artifact.artifact.instructionPC 8032 = 10638 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem preloadHDGTPC3014 : CycleSubmission.Artifact.artifact.instructionPC 8033 = 10639 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem preloadHDGTPC3015 : CycleSubmission.Artifact.artifact.instructionPC 8034 = 10640 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem preloadHDGTPC3016 : CycleSubmission.Artifact.artifact.instructionPC 8035 = 10641 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem preloadHDGTPC3017 : CycleSubmission.Artifact.artifact.instructionPC 8036 = 10642 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem preloadHDGTPC3018 : CycleSubmission.Artifact.artifact.instructionPC 8037 = 10643 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem preloadHDGTPC3019 : CycleSubmission.Artifact.artifact.instructionPC 8038 = 10644 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem preloadHDGTPC3020 : CycleSubmission.Artifact.artifact.instructionPC 8039 = 10645 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem preloadHDGTPC3021 : CycleSubmission.Artifact.artifact.instructionPC 8040 = 10646 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem preloadHDGTPC3022 : CycleSubmission.Artifact.artifact.instructionPC 8041 = 10647 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem preloadHDGTPC3023 : CycleSubmission.Artifact.artifact.instructionPC 8042 = 10649 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem preloadHDGTPC3024 : CycleSubmission.Artifact.artifact.instructionPC 8043 = 10650 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem preloadHDGTPC3025 : CycleSubmission.Artifact.artifact.instructionPC 8044 = 10651 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem preloadHDGTPC3026 : CycleSubmission.Artifact.artifact.instructionPC 8045 = 10652 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem preloadHDGTPC3027 : CycleSubmission.Artifact.artifact.instructionPC 8046 = 10653 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem preloadHDGTPC3028 : CycleSubmission.Artifact.artifact.instructionPC 8047 = 10654 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem preloadHDGTPC3029 : CycleSubmission.Artifact.artifact.instructionPC 8048 = 10657 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem rhoPC2142 : CycleSubmission.Artifact.artifact.instructionPC 6399 = 8506 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem rhoPC2854 : CycleSubmission.Artifact.artifact.instructionPC 7984 = 10571 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem rhoPC2855 : CycleSubmission.Artifact.artifact.instructionPC 7985 = 10572 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem rhoPC2856 : CycleSubmission.Artifact.artifact.instructionPC 7986 = 10573 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem rhoPC2857 : CycleSubmission.Artifact.artifact.instructionPC 7987 = 10576 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem rhoPC2858 : CycleSubmission.Artifact.artifact.instructionPC 7988 = 10579 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem rhoPC2859 : CycleSubmission.Artifact.artifact.instructionPC 7989 = 10580 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem rhoPC2860 : CycleSubmission.Artifact.artifact.instructionPC 7990 = 10583 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem rhoPC2861 : CycleSubmission.Artifact.artifact.instructionPC 7992 = 10585 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem rhoPC2862 : CycleSubmission.Artifact.artifact.instructionPC 7993 = 10588 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem rhoPC2863 : CycleSubmission.Artifact.artifact.instructionPC 7994 = 10589 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem rhoPC2864 : CycleSubmission.Artifact.artifact.instructionPC 7995 = 10590 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem rhoPC2865 : CycleSubmission.Artifact.artifact.instructionPC 7996 = 10591 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem rhoPC2866 : CycleSubmission.Artifact.artifact.instructionPC 7997 = 10592 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem rhoPC2867 : CycleSubmission.Artifact.artifact.instructionPC 7998 = 10593 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem rhoPC2868 : CycleSubmission.Artifact.artifact.instructionPC 7999 = 10594 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem rhoPC2869 : CycleSubmission.Artifact.artifact.instructionPC 8000 = 10595 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem rhoPC2870 : CycleSubmission.Artifact.artifact.instructionPC 8001 = 10596 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem rhoPC2871 : CycleSubmission.Artifact.artifact.instructionPC 8002 = 10597 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem rhoPC2872 : CycleSubmission.Artifact.artifact.instructionPC 8003 = 10598 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem rhoPC2873 : CycleSubmission.Artifact.artifact.instructionPC 8004 = 10599 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem rhoPC2874 : CycleSubmission.Artifact.artifact.instructionPC 8005 = 10600 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem rhoPC2875 : CycleSubmission.Artifact.artifact.instructionPC 8006 = 10601 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem rhoPC2876 : CycleSubmission.Artifact.artifact.instructionPC 8007 = 10602 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem rhoPC2877 : CycleSubmission.Artifact.artifact.instructionPC 8008 = 10603 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem rhoPC2878 : CycleSubmission.Artifact.artifact.instructionPC 8009 = 10605 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem rhoPC2879 : CycleSubmission.Artifact.artifact.instructionPC 8010 = 10606 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem rhoPC2880 : CycleSubmission.Artifact.artifact.instructionPC 8011 = 10607 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem rhoPC2881 : CycleSubmission.Artifact.artifact.instructionPC 8011 = 10607 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem rhoPC2882 : CycleSubmission.Artifact.artifact.instructionPC 8011 = 10607 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem rhoPC2883 : CycleSubmission.Artifact.artifact.instructionPC 8012 = 10608 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem rhoPC2884 : CycleSubmission.Artifact.artifact.instructionPC 8013 = 10609 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem rhoPC2885 : CycleSubmission.Artifact.artifact.instructionPC 8014 = 10610 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem rhoPC2886 : CycleSubmission.Artifact.artifact.instructionPC 8015 = 10613 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem rhoPC3002 : CycleSubmission.Artifact.artifact.instructionPC 8017 = 10615 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem rhoPC3003 : CycleSubmission.Artifact.artifact.instructionPC 8018 = 10616 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem rhoPC3004 : CycleSubmission.Artifact.artifact.instructionPC 8019 = 10617 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem rhoPC3005 : CycleSubmission.Artifact.artifact.instructionPC 8020 = 10620 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem rhoPC3006 : CycleSubmission.Artifact.artifact.instructionPC 8021 = 10623 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem rhoPC3007 : CycleSubmission.Artifact.artifact.instructionPC 8022 = 10624 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem rhoPC3008 : CycleSubmission.Artifact.artifact.instructionPC 8023 = 10627 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem rhoPC3009 : CycleSubmission.Artifact.artifact.instructionPC 8025 = 10629 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem rhoPC3010 : CycleSubmission.Artifact.artifact.instructionPC 8026 = 10632 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem rhoPC3011 : CycleSubmission.Artifact.artifact.instructionPC 8027 = 10633 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem rhoPC3012 : CycleSubmission.Artifact.artifact.instructionPC 8028 = 10634 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem rhoPC3013 : CycleSubmission.Artifact.artifact.instructionPC 8029 = 10635 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem rhoPC3014 : CycleSubmission.Artifact.artifact.instructionPC 8030 = 10636 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem rhoPC3015 : CycleSubmission.Artifact.artifact.instructionPC 8031 = 10637 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem rhoPC3016 : CycleSubmission.Artifact.artifact.instructionPC 8032 = 10638 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem rhoPC3017 : CycleSubmission.Artifact.artifact.instructionPC 8033 = 10639 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem rhoPC3018 : CycleSubmission.Artifact.artifact.instructionPC 8034 = 10640 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem rhoPC3019 : CycleSubmission.Artifact.artifact.instructionPC 8035 = 10641 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem rhoPC3020 : CycleSubmission.Artifact.artifact.instructionPC 8036 = 10642 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem rhoPC3021 : CycleSubmission.Artifact.artifact.instructionPC 8037 = 10643 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem rhoPC3022 : CycleSubmission.Artifact.artifact.instructionPC 8038 = 10644 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem rhoPC3023 : CycleSubmission.Artifact.artifact.instructionPC 8039 = 10645 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem rhoPC3024 : CycleSubmission.Artifact.artifact.instructionPC 8040 = 10646 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem rhoPC3025 : CycleSubmission.Artifact.artifact.instructionPC 8041 = 10647 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem rhoPC3026 : CycleSubmission.Artifact.artifact.instructionPC 8042 = 10649 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem rhoPC3027 : CycleSubmission.Artifact.artifact.instructionPC 8043 = 10650 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem rhoPC3028 : CycleSubmission.Artifact.artifact.instructionPC 8044 = 10651 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem rhoPC3029 : CycleSubmission.Artifact.artifact.instructionPC 8044 = 10651 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem rhoPC3030 : CycleSubmission.Artifact.artifact.instructionPC 8044 = 10651 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem rhoPC3031 : CycleSubmission.Artifact.artifact.instructionPC 8045 = 10652 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem rhoPC3032 : CycleSubmission.Artifact.artifact.instructionPC 8046 = 10653 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem rhoPC3033 : CycleSubmission.Artifact.artifact.instructionPC 8047 = 10654 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem rhoPC3034 : CycleSubmission.Artifact.artifact.instructionPC 8048 = 10657 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem rhoPC8318 : CycleSubmission.Artifact.artifact.instructionPC 432 = 586 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
theorem jumpDestZeroJoin8 : Decode.isValidJumpDest CycleSubmission.Artifact.bytecode 8506 = true := by
  have h := CycleSubmission.Global.Binding.jumpDest 6399 (by rw [CycleSubmission.Artifact.instruction_get]; rfl)
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
theorem jumpDestZeroJoin4 : Decode.isValidJumpDest CycleSubmission.Artifact.bytecode 586 = true := by
  have h := CycleSubmission.Global.Binding.jumpDest 432 (by rw [CycleSubmission.Artifact.instruction_get]; rfl)
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
theorem jumpDestLoop2684 : Decode.isValidJumpDest CycleSubmission.Artifact.bytecode 8448 = true := by
  have h := CycleSubmission.Global.Binding.jumpDest 6354 (by rw [CycleSubmission.Artifact.instruction_get]; rfl)
  have hp : CycleSubmission.Artifact.artifact.instructionPC 6354 = 8448 := by
    rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
  simpa only [hp] using h
theorem jumpDestLoop10692 : Decode.isValidJumpDest CycleSubmission.Artifact.bytecode 528 = true := by
  have h := CycleSubmission.Global.Binding.jumpDest 387 (by rw [CycleSubmission.Artifact.instruction_get]; rfl)
  have hp : CycleSubmission.Artifact.artifact.instructionPC 387 = 528 := by
    rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
  simpa only [hp] using h
theorem jumpDestLoop3711 : Decode.isValidJumpDest CycleSubmission.Artifact.bytecode 10571 = true := by
  have h := CycleSubmission.Global.Binding.jumpDest 7984 (by rw [CycleSubmission.Artifact.instruction_get]; rfl)
  have hp : CycleSubmission.Artifact.artifact.instructionPC 7984 = 10571 := by
    rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
  simpa only [hp] using h
theorem jumpDestLoop3879 : Decode.isValidJumpDest CycleSubmission.Artifact.bytecode 10615 = true := by
  have h := CycleSubmission.Global.Binding.jumpDest 8017 (by rw [CycleSubmission.Artifact.instruction_get]; rfl)
  have hp : CycleSubmission.Artifact.artifact.instructionPC 8017 = 10615 := by
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
