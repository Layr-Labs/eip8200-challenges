import Mathlib.Tactic
set_option warningAsError true
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000
namespace RipemdTableOrder20261027
-- Symbol 0 is a zero byte; 1..64 are arbitrary input bytes; 1000+a is an
-- arbitrary old scratch byte. Distinct symbols are not assumed unequal.
def clearAddresses : List Nat := [50, 51, 52, 53, 160, 161, 194, 195, 250, 251, 284, 285, 320, 321, 322, 323, 356, 357, 358, 359, 392, 393, 394, 395, 446, 447, 448, 449, 590, 591, 592, 593, 716, 717, 718, 719, 788, 789, 790, 791, 824, 825, 826, 827, 932, 933, 934, 935, 968, 969, 970, 971, 1004, 1005, 1006, 1007, 1040, 1041, 1042, 1043]
def initial (a : Nat) : Nat :=
  if 162 ≤ a ∧ a < 194 then 33 + ((a-162)/4)*4 + 3 - (a-162)%4
  else if 252 ≤ a ∧ a < 284 then 1 + ((a-252)/4)*4 + 3 - (a-252)%4
  else if a ∈ clearAddresses then 0 else 1000+a
def fan (a : Nat) : Nat :=
  if 286 ≤ a ∧ a < 318 then initial (a-18)
  else if 218 ≤ a ∧ a < 250 then initial (a+18)
  else if 196 ≤ a ∧ a < 228 then initial (a-18)
  else if 128 ≤ a ∧ a < 160 then initial (a+18)
  else initial a
def laneByte (j : Nat) : Bool := (10 ≤ j && j < 14) || (28 ≤ j && j < 32)
abbrev Write := Nat × Nat × Nat × Bool
def plan : List Write := [(612, 900, 138, false),
  (616, 216, 142, false),
  (621, 882, 236, false),
  (625, 126, 146, false),
  (630, 864, 146, false),
  (635, 846, 236, false),
  (640, 828, 138, false),
  (645, 936, 134, false),
  (650, 558, 134, false),
  (655, 540, 228, false),
  (659, 108, 262, false),
  (664, 684, 266, false),
  (667, 666, 176, false),
  (672, 414, 266, false),
  (676, 756, 138, false),
  (681, 522, 224, false),
  (685, 90, 168, false),
  (689, 72, 258, false),
  (692, 54, 224, false),
  (697, 504, 228, false),
  (702, 1080, 262, false),
  (707, 486, 262, false),
  (712, 1062, 172, false),
  (716, 972, 236, false),
  (721, 1008, 180, false),
  (726, 648, 180, false),
  (731, 630, 142, false),
  (737, 612, 180, false),
  (739, 738, 134, false),
  (744, 288, 270, false),
  (772, 594, 146, true),
  (777, 1044, 266, false),
  (781, 720, 262, false),
  (785, 270, 180, false),
  (790, 396, 258, false),
  (793, 792, 228, false),
  (797, 468, 228, false),
  (800, 18, 258, false),
  (804, 360, 232, false),
  (807, 198, 172, false),
  (811, 324, 142, false),
  (814, 252, 270, false),
  (816, 0, 266, false),
  (820, 450, 168, false),
  (823, 162, 176, false)]
def removed : List Nat := [692, 702, 744, 785, 793]
def selected : List Write := [(100157, 828, 236, false),
  (100130, 684, 266, false),
  (100125, 666, 180, false),
  (100022, 108, 258, false),
  (100119, 648, 142, false),
  (100117, 630, 176, false),
  (100004, 18, 266, false),
  (100100, 558, 134, false),
  (100073, 414, 258, false),
  (100099, 540, 228, false),
  (100047, 252, 142, false),
  (100094, 522, 224, false),
  (100017, 90, 224, false),
  (100041, 216, 172, false),
  (100013, 72, 258, false),
  (100110, 594, 146, false),
  (100159, 846, 146, false),
  (100008, 54, 168, false),
  (100174, 936, 134, false),
  (100181, 972, 236, false),
  (100065, 360, 258, false),
  (100142, 756, 134, false),
  (100037, 198, 142, false),
  (100141, 738, 262, false),
  (100091, 504, 228, false),
  (100086, 486, 168, false),
  (100085, 468, 262, false),
  (100079, 450, 168, false),
  (100149, 792, 138, false),
  (100163, 864, 236, false),
  (100184, 1008, 180, false),
  (100168, 900, 138, false),
  (100114, 612, 180, false),
  (100071, 396, 266, false),
  (100137, 720, 262, false),
  (100059, 324, 232, false)]
def sourceByte (w : Write) (j : Nat) : Nat :=
  if w.2.2.2 && !laneByte j then 0 else fan (w.2.2.1+j)
def applyWrite (m : Nat → Nat) (w : Write) (a : Nat) : Nat :=
  if w.2.1 ≤ a ∧ a < w.2.1+32 then sourceByte w (a-w.2.1) else m a
def result (ws : List Write) : Nat → Nat := ws.foldl applyWrite fan
abbrev Load := Nat × Nat × Nat × Bool
def loads : List Load := [(842, 486, 94, true),
  (872, 162, 608, true),
  (911, 252, 728, true),
  (1008, 360, 324, true),
  (1051, 54, 316, true),
  (1089, 774, 838, true),
  (1164, 882, 846, true),
  (1203, 396, 10, true),
  (1241, 1080, 58, true),
  (1280, 1044, 18, true),
  (1318, 288, 66, true),
  (1356, 936, 134, true),
  (1394, 810, 820, true),
  (1445, 324, 142, true),
  (1483, 864, 828, true),
  (1534, 450, 54, true),
  (1600, 1062, 472, true),
  (1639, 144, 202, true),
  (1694, 990, 990, true),
  (1772, 252, 728, true),
  (1811, 72, 108, true),
  (1865, 198, 604, true),
  (1905, 504, 76, true),
  (1958, 324, 142, true),
  (1998, 684, 62, true),
  (2052, 1008, 612, true),
  (2092, 954, 954, true),
  (2146, 450, 54, true),
  (2185, 36, 90, true),
  (2237, 828, 138, true),
  (2277, 486, 94, true),
  (2393, 666, 630, true),
  (2431, 126, 32, true),
  (2486, 558, 558, true),
  (2547, 972, 864, true),
  (2580, 306, 746, true),
  (2625, 162, 608, true),
  (2657, 18, 414, true),
  (2691, 828, 138, true),
  (2724, 612, 594, true),
  (2756, 936, 134, true),
  (2789, 468, 504, true),
  (2866, 234, 270, true),
  (2910, 54, 316, true),
  (2943, 414, 378, true),
  (2992, 198, 604, true),
  (3055, 576, 576, true),
  (3094, 702, 702, true),
  (3150, 90, 432, true),
  (3214, 792, 320, true),
  (3254, 900, 882, true),
  (3298, 594, 146, true),
  (3338, 630, 180, true),
  (3393, 54, 316, true),
  (3433, 738, 756, true),
  (3488, 450, 54, true),
  (3528, 378, 342, true),
  (3581, 198, 604, true),
  (3621, 846, 810, true),
  (3674, 252, 728, true),
  (3714, 648, 666, true),
  (3766, 162, 608, true),
  (3811, 108, 468, true),
  (3849, 1026, 684, true),
  (3890, 342, 842, true),
  (3934, 396, 10, true),
  (3972, 522, 522, true),
  (4025, 720, 14, true),
  (4063, 756, 774, true),
  (4098, 252, 728, true),
  (4136, 432, 36, true),
  (4210, 216, 234, true),
  (4260, 162, 608, true),
  (4300, 540, 540, true),
  (4337, 972, 864, true),
  (4376, 918, 918, true),
  (4425, 594, 146, true),
  (4458, 0, 0, false),
  (4477, 612, 594, true),
  (4514, 198, 604, true)]
def offsets (paired : Bool) : List Nat :=
  if paired then [10,11,12,13,28,29,30,31] else [28,29,30,31]
def projected (l : Load) : Bool :=
  (offsets l.2.2.2).all (fun i => result plan (l.2.1+i) == result selected (l.2.2.1+i))
def barrier (l : Load) : Bool :=
  !l.2.2.2 || (List.range 14).any (fun i => result selected (l.2.2.1+14+i) == 0)
theorem projected_bytes : loads.all projected = true := by decide +kernel
theorem lower_lane_barriers : loads.all barrier = true := by decide +kernel
theorem next_entry_zero_bytes : clearAddresses.all (fun a => result selected a == 0) = true := by decide +kernel
theorem projected_under_every_assignment (value : Nat → UInt8) (l : Load) (hl : l ∈ loads)
    (i : Nat) (hi : i ∈ offsets l.2.2.2) :
    value (result plan (l.2.1+i)) = value (result selected (l.2.2.1+i)) := by
  have h := List.all_eq_true.mp projected_bytes l hl
  have h' := List.all_eq_true.mp h i hi
  exact congrArg value (by simpa only [beq_iff_eq] using h')
theorem next_entry_under_every_assignment (value : Nat → UInt8) (hzero : value 0 = 0)
    (a : Nat) (ha : a ∈ clearAddresses) : value (result selected a) = 0 := by
  have h : result selected a = 0 := by
    simpa only [beq_iff_eq] using List.all_eq_true.mp next_entry_zero_bytes a ha
  rw [h, hzero]
#print axioms projected_bytes
#print axioms lower_lane_barriers
#print axioms next_entry_zero_bytes
#print axioms projected_under_every_assignment
#print axioms next_entry_under_every_assignment
end RipemdTableOrder20261027
