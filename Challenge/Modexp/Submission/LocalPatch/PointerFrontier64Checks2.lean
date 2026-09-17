import Challenge.Modexp.Submission.LocalPatch.PointerFrontier64Checks1

set_option warningAsError true
set_option linter.unusedSimpArgs false

namespace Challenge.Modexp.Submission.LocalPatch.PointerFrontier64
open EvmSemantics EvmSemantics.EVM
open StaticDomain PointerSub32 ScannerTargets

def walk28 : List Nat := StaticDomainFrontier64.pcs28

theorem path28 : ScanPath code 2155 walk28 2225 := by decide

theorem hits28 : targets reference StaticDomainFrontier64.pcs28 = targets code walk28 := by decide

theorem windows28 : LocalDecode.checkMany reference code
  (StaticDomainFrontier64.pcs28.filter (fun pc => decide (Exterior pc))) = true := by decide

def walk29 : List Nat := StaticDomainFrontier64.pcs29

theorem path29 : ScanPath code 2225 walk29 2295 := by decide

theorem hits29 : targets reference StaticDomainFrontier64.pcs29 = targets code walk29 := by decide

theorem windows29 : LocalDecode.checkMany reference code
  (StaticDomainFrontier64.pcs29.filter (fun pc => decide (Exterior pc))) = true := by decide

def walk30 : List Nat := StaticDomainFrontier64.pcs30

theorem path30 : ScanPath code 2295 walk30 2368 := by decide

theorem hits30 : targets reference StaticDomainFrontier64.pcs30 = targets code walk30 := by decide

theorem windows30 : LocalDecode.checkMany reference code
  (StaticDomainFrontier64.pcs30.filter (fun pc => decide (Exterior pc))) = true := by decide

def walk31 : List Nat := StaticDomainFrontier64.pcs31

theorem path31 : ScanPath code 2368 walk31 2470 := by decide

theorem hits31 : targets reference StaticDomainFrontier64.pcs31 = targets code walk31 := by decide

theorem windows31 : LocalDecode.checkMany reference code
  (StaticDomainFrontier64.pcs31.filter (fun pc => decide (Exterior pc))) = true := by decide

def walk32 : List Nat := [
  2470, 2473, 2474, 2475, 2476, 2477, 2478, 2479, 2480, 2482, 2483, 2484,
  2485, 2488, 2489, 2490, 2492, 2495, 2496, 2497, 2500, 2501, 2504, 2507,
  2508, 2509, 2510, 2513, 2516, 2517, 2519, 2522, 2523, 2524, 2525, 2526,
  2527, 2528, 2529, 2530, 2531, 2532, 2533, 2534, 2537, 2538, 2539, 2542,
  2543, 2544, 2545, 2548, 2549, 2550, 2551, 2552, 2553, 2554, 2555, 2556,
  2557, 2558, 2559
]

theorem path32 : ScanPath code 2470 walk32 2562 := by decide

theorem hits32 : targets reference StaticDomainFrontier64.pcs32 = targets code walk32 := by decide

theorem windows32 : LocalDecode.checkMany reference code
  (StaticDomainFrontier64.pcs32.filter (fun pc => decide (Exterior pc))) = true := by decide

def walk33 : List Nat := StaticDomainFrontier64.pcs33

theorem path33 : ScanPath code 2562 walk33 2641 := by decide

theorem hits33 : targets reference StaticDomainFrontier64.pcs33 = targets code walk33 := by decide

theorem windows33 : LocalDecode.checkMany reference code
  (StaticDomainFrontier64.pcs33.filter (fun pc => decide (Exterior pc))) = true := by decide

def walk34 : List Nat := StaticDomainFrontier64.pcs34

theorem path34 : ScanPath code 2641 walk34 2738 := by decide

theorem hits34 : targets reference StaticDomainFrontier64.pcs34 = targets code walk34 := by decide

theorem windows34 : LocalDecode.checkMany reference code
  (StaticDomainFrontier64.pcs34.filter (fun pc => decide (Exterior pc))) = true := by decide

def walk35 : List Nat := StaticDomainFrontier64.pcs35

theorem path35 : ScanPath code 2738 walk35 2823 := by decide

theorem hits35 : targets reference StaticDomainFrontier64.pcs35 = targets code walk35 := by decide

theorem windows35 : LocalDecode.checkMany reference code
  (StaticDomainFrontier64.pcs35.filter (fun pc => decide (Exterior pc))) = true := by decide

def walk36 : List Nat := StaticDomainFrontier64.pcs36

theorem path36 : ScanPath code 2823 walk36 2901 := by decide

theorem hits36 : targets reference StaticDomainFrontier64.pcs36 = targets code walk36 := by decide

theorem windows36 : LocalDecode.checkMany reference code
  (StaticDomainFrontier64.pcs36.filter (fun pc => decide (Exterior pc))) = true := by decide

def walk37 : List Nat := StaticDomainFrontier64.pcs37

theorem path37 : ScanPath code 2901 walk37 2977 := by decide

theorem hits37 : targets reference StaticDomainFrontier64.pcs37 = targets code walk37 := by decide

theorem windows37 : LocalDecode.checkMany reference code
  (StaticDomainFrontier64.pcs37.filter (fun pc => decide (Exterior pc))) = true := by decide

def walk38 : List Nat := StaticDomainFrontier64.pcs38

theorem path38 : ScanPath code 2977 walk38 3053 := by decide

theorem hits38 : targets reference StaticDomainFrontier64.pcs38 = targets code walk38 := by decide

theorem windows38 : LocalDecode.checkMany reference code
  (StaticDomainFrontier64.pcs38.filter (fun pc => decide (Exterior pc))) = true := by decide

def walk39 : List Nat := StaticDomainFrontier64.pcs39

theorem path39 : ScanPath code 3053 walk39 3137 := by decide

theorem hits39 : targets reference StaticDomainFrontier64.pcs39 = targets code walk39 := by decide

theorem windows39 : LocalDecode.checkMany reference code
  (StaticDomainFrontier64.pcs39.filter (fun pc => decide (Exterior pc))) = true := by decide

def walk40 : List Nat := StaticDomainFrontier64.pcs40

theorem path40 : ScanPath code 3137 walk40 3223 := by decide

theorem hits40 : targets reference StaticDomainFrontier64.pcs40 = targets code walk40 := by decide

theorem windows40 : LocalDecode.checkMany reference code
  (StaticDomainFrontier64.pcs40.filter (fun pc => decide (Exterior pc))) = true := by decide

def walk41 : List Nat := StaticDomainFrontier64.pcs41

theorem path41 : ScanPath code 3223 walk41 3319 := by decide

theorem hits41 : targets reference StaticDomainFrontier64.pcs41 = targets code walk41 := by decide

theorem windows41 : LocalDecode.checkMany reference code
  (StaticDomainFrontier64.pcs41.filter (fun pc => decide (Exterior pc))) = true := by decide

end Challenge.Modexp.Submission.LocalPatch.PointerFrontier64
