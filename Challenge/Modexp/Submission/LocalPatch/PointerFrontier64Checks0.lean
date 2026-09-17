import Challenge.Modexp.Submission.LocalPatch.PointerPhase
import Challenge.Modexp.Submission.LocalPatch.PointerFrontier64Bytes

set_option warningAsError true
set_option linter.unusedSimpArgs false

namespace Challenge.Modexp.Submission.LocalPatch.PointerFrontier64
open EvmSemantics EvmSemantics.EVM
open StaticDomain PointerSub32 ScannerTargets

def walk00 : List Nat := StaticDomainFrontier64.pcs00

theorem path00 : ScanPath code 0 walk00 118 := by decide

theorem hits00 : targets reference StaticDomainFrontier64.pcs00 = targets code walk00 := by decide

theorem windows00 : LocalDecode.checkMany reference code
  (StaticDomainFrontier64.pcs00.filter (fun pc => decide (Exterior pc))) = true := by decide

def walk01 : List Nat := StaticDomainFrontier64.pcs01

theorem path01 : ScanPath code 118 walk01 194 := by decide

theorem hits01 : targets reference StaticDomainFrontier64.pcs01 = targets code walk01 := by decide

theorem windows01 : LocalDecode.checkMany reference code
  (StaticDomainFrontier64.pcs01.filter (fun pc => decide (Exterior pc))) = true := by decide

def walk02 : List Nat := StaticDomainFrontier64.pcs02

theorem path02 : ScanPath code 194 walk02 275 := by decide

theorem hits02 : targets reference StaticDomainFrontier64.pcs02 = targets code walk02 := by decide

theorem windows02 : LocalDecode.checkMany reference code
  (StaticDomainFrontier64.pcs02.filter (fun pc => decide (Exterior pc))) = true := by decide

def walk03 : List Nat := StaticDomainFrontier64.pcs03

theorem path03 : ScanPath code 275 walk03 365 := by decide

theorem hits03 : targets reference StaticDomainFrontier64.pcs03 = targets code walk03 := by decide

theorem windows03 : LocalDecode.checkMany reference code
  (StaticDomainFrontier64.pcs03.filter (fun pc => decide (Exterior pc))) = true := by decide

def walk04 : List Nat := StaticDomainFrontier64.pcs04

theorem path04 : ScanPath code 365 walk04 465 := by decide

theorem hits04 : targets reference StaticDomainFrontier64.pcs04 = targets code walk04 := by decide

theorem windows04 : LocalDecode.checkMany reference code
  (StaticDomainFrontier64.pcs04.filter (fun pc => decide (Exterior pc))) = true := by decide

def walk05 : List Nat := StaticDomainFrontier64.pcs05

theorem path05 : ScanPath code 465 walk05 548 := by decide

theorem hits05 : targets reference StaticDomainFrontier64.pcs05 = targets code walk05 := by decide

theorem windows05 : LocalDecode.checkMany reference code
  (StaticDomainFrontier64.pcs05.filter (fun pc => decide (Exterior pc))) = true := by decide

def walk06 : List Nat := StaticDomainFrontier64.pcs06

theorem path06 : ScanPath code 548 walk06 634 := by decide

theorem hits06 : targets reference StaticDomainFrontier64.pcs06 = targets code walk06 := by decide

theorem windows06 : LocalDecode.checkMany reference code
  (StaticDomainFrontier64.pcs06.filter (fun pc => decide (Exterior pc))) = true := by decide

def walk07 : List Nat := StaticDomainFrontier64.pcs07

theorem path07 : ScanPath code 634 walk07 718 := by decide

theorem hits07 : targets reference StaticDomainFrontier64.pcs07 = targets code walk07 := by decide

theorem windows07 : LocalDecode.checkMany reference code
  (StaticDomainFrontier64.pcs07.filter (fun pc => decide (Exterior pc))) = true := by decide

def walk08 : List Nat := StaticDomainFrontier64.pcs08

theorem path08 : ScanPath code 718 walk08 796 := by decide

theorem hits08 : targets reference StaticDomainFrontier64.pcs08 = targets code walk08 := by decide

theorem windows08 : LocalDecode.checkMany reference code
  (StaticDomainFrontier64.pcs08.filter (fun pc => decide (Exterior pc))) = true := by decide

def walk09 : List Nat := StaticDomainFrontier64.pcs09

theorem path09 : ScanPath code 796 walk09 872 := by decide

theorem hits09 : targets reference StaticDomainFrontier64.pcs09 = targets code walk09 := by decide

theorem windows09 : LocalDecode.checkMany reference code
  (StaticDomainFrontier64.pcs09.filter (fun pc => decide (Exterior pc))) = true := by decide

def walk10 : List Nat := StaticDomainFrontier64.pcs10

theorem path10 : ScanPath code 872 walk10 939 := by decide

theorem hits10 : targets reference StaticDomainFrontier64.pcs10 = targets code walk10 := by decide

theorem windows10 : LocalDecode.checkMany reference code
  (StaticDomainFrontier64.pcs10.filter (fun pc => decide (Exterior pc))) = true := by decide

def walk11 : List Nat := StaticDomainFrontier64.pcs11

theorem path11 : ScanPath code 939 walk11 1014 := by decide

theorem hits11 : targets reference StaticDomainFrontier64.pcs11 = targets code walk11 := by decide

theorem windows11 : LocalDecode.checkMany reference code
  (StaticDomainFrontier64.pcs11.filter (fun pc => decide (Exterior pc))) = true := by decide

def walk12 : List Nat := StaticDomainFrontier64.pcs12

theorem path12 : ScanPath code 1014 walk12 1084 := by decide

theorem hits12 : targets reference StaticDomainFrontier64.pcs12 = targets code walk12 := by decide

theorem windows12 : LocalDecode.checkMany reference code
  (StaticDomainFrontier64.pcs12.filter (fun pc => decide (Exterior pc))) = true := by decide

def walk13 : List Nat := StaticDomainFrontier64.pcs13

theorem path13 : ScanPath code 1084 walk13 1156 := by decide

theorem hits13 : targets reference StaticDomainFrontier64.pcs13 = targets code walk13 := by decide

theorem windows13 : LocalDecode.checkMany reference code
  (StaticDomainFrontier64.pcs13.filter (fun pc => decide (Exterior pc))) = true := by decide

end Challenge.Modexp.Submission.LocalPatch.PointerFrontier64
