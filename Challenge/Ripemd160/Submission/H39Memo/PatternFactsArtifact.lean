import Challenge.Ripemd160.Submission.H39Memo.PatternFactsData
import Challenge.Ripemd160.Submission.H39Memo.Artifact

set_option warningAsError true
set_option maxRecDepth 40000
set_option maxHeartbeats 2000000

namespace Challenge.Ripemd160.Submission.H39Memo.PatternFacts

private theorem prefix_push_0 :
    Artifact.h39Instructions[860]? = some (.push 32 (prefixWord 0)) := by rfl

private theorem prefix_push_1 :
    Artifact.h39Instructions[886]? = some (.push 32 (prefixWord 1)) := by rfl

private theorem prefix_push_2 :
    Artifact.h39Instructions[902]? = some (.push 32 (prefixWord 2)) := by rfl

private theorem prefix_push_3 :
    Artifact.h39Instructions[918]? = some (.push 32 (prefixWord 3)) := by rfl

private theorem prefix_push_4 :
    Artifact.h39Instructions[929]? = some (.push 32 (prefixWord 4)) := by rfl

private theorem prefix_push_5 :
    Artifact.h39Instructions[935]? = some (.push 32 (prefixWord 5)) := by rfl

private theorem prefix_push_6 :
    Artifact.h39Instructions[941]? = some (.push 32 (prefixWord 6)) := by rfl

private theorem prefix_push_7 :
    Artifact.h39Instructions[947]? = some (.push 32 (prefixWord 7)) := by rfl

private theorem prefix_push_8 :
    Artifact.h39Instructions[958]? = some (.push 32 (prefixWord 8)) := by rfl

private theorem prefix_push_9 :
    Artifact.h39Instructions[964]? = some (.push 32 (prefixWord 9)) := by rfl

private theorem prefix_push_10 :
    Artifact.h39Instructions[970]? = some (.push 32 (prefixWord 10)) := by rfl

private theorem prefix_push_11 :
    Artifact.h39Instructions[981]? = some (.push 32 (prefixWord 11)) := by rfl

private theorem prefix_push_12 :
    Artifact.h39Instructions[987]? = some (.push 32 (prefixWord 12)) := by rfl

private theorem prefix_push_13 :
    Artifact.h39Instructions[993]? = some (.push 32 (prefixWord 13)) := by rfl

private theorem prefix_push_14 :
    Artifact.h39Instructions[999]? = some (.push 32 (prefixWord 14)) := by rfl

private theorem prefix_push_15 :
    Artifact.h39Instructions[1005]? = some (.push 32 (prefixWord 15)) := by rfl

private theorem prefix_push_16 :
    Artifact.h39Instructions[1011]? = some (.push 32 (prefixWord 16)) := by rfl

private theorem prefix_push_17 :
    Artifact.h39Instructions[1017]? = some (.push 32 (prefixWord 17)) := by rfl

private theorem prefix_push_18 :
    Artifact.h39Instructions[1023]? = some (.push 32 (prefixWord 18)) := by rfl

private theorem prefix_push_19 :
    Artifact.h39Instructions[1029]? = some (.push 32 (prefixWord 19)) := by rfl

private theorem prefix_push_20 :
    Artifact.h39Instructions[1035]? = some (.push 32 (prefixWord 20)) := by rfl

private theorem prefix_push_21 :
    Artifact.h39Instructions[1041]? = some (.push 32 (prefixWord 21)) := by rfl

private theorem prefix_push_22 :
    Artifact.h39Instructions[1047]? = some (.push 32 (prefixWord 22)) := by rfl

private theorem prefix_push_23 :
    Artifact.h39Instructions[1053]? = some (.push 32 (prefixWord 23)) := by rfl

private theorem prefix_push_24 :
    Artifact.h39Instructions[1059]? = some (.push 32 (prefixWord 24)) := by rfl

private theorem prefix_push_25 :
    Artifact.h39Instructions[1065]? = some (.push 32 (prefixWord 25)) := by rfl

private theorem prefix_push_26 :
    Artifact.h39Instructions[1071]? = some (.push 32 (prefixWord 26)) := by rfl

private theorem prefix_push_27 :
    Artifact.h39Instructions[1077]? = some (.push 32 (prefixWord 27)) := by rfl

private theorem prefix_push_28 :
    Artifact.h39Instructions[1083]? = some (.push 32 (prefixWord 28)) := by rfl

private theorem prefix_push_29 :
    Artifact.h39Instructions[1089]? = some (.push 32 (prefixWord 29)) := by rfl

private theorem prefix_push_30 :
    Artifact.h39Instructions[1095]? = some (.push 32 (prefixWord 30)) := by rfl

theorem prefix_push (k : Fin 31) :
    Artifact.h39Instructions[prefixPushIndex k]? = some (.push 32 (prefixWord k)) := by
  fin_cases k
  · exact prefix_push_0
  · exact prefix_push_1
  · exact prefix_push_2
  · exact prefix_push_3
  · exact prefix_push_4
  · exact prefix_push_5
  · exact prefix_push_6
  · exact prefix_push_7
  · exact prefix_push_8
  · exact prefix_push_9
  · exact prefix_push_10
  · exact prefix_push_11
  · exact prefix_push_12
  · exact prefix_push_13
  · exact prefix_push_14
  · exact prefix_push_15
  · exact prefix_push_16
  · exact prefix_push_17
  · exact prefix_push_18
  · exact prefix_push_19
  · exact prefix_push_20
  · exact prefix_push_21
  · exact prefix_push_22
  · exact prefix_push_23
  · exact prefix_push_24
  · exact prefix_push_25
  · exact prefix_push_26
  · exact prefix_push_27
  · exact prefix_push_28
  · exact prefix_push_29
  · exact prefix_push_30

private theorem tail_push_0 :
    Artifact.h39Instructions[1184]? = some (.push 32 (tailWord 0)) := by rfl

private theorem tail_push_1 :
    Artifact.h39Instructions[1198]? = some (.push 32 (tailWord 1)) := by rfl

private theorem tail_push_3 :
    Artifact.h39Instructions[1220]? = some (.push 32 (tailWord 3)) := by rfl

private theorem tail_push_4 :
    Artifact.h39Instructions[1234]? = some (.push 32 (tailWord 4)) := by rfl

private theorem tail_push_5 :
    Artifact.h39Instructions[1248]? = some (.push 32 (tailWord 5)) := by rfl

private theorem tail_push_7 :
    Artifact.h39Instructions[1270]? = some (.push 32 (tailWord 7)) := by rfl

private theorem tail_push_8 :
    Artifact.h39Instructions[1284]? = some (.push 32 (tailWord 8)) := by rfl

private theorem tail_push_9 :
    Artifact.h39Instructions[1298]? = some (.push 32 (tailWord 9)) := by rfl

private theorem tail_push_12 :
    Artifact.h39Instructions[1328]? = some (.push 32 (tailWord 12)) := by rfl

private theorem tail_push_13 :
    Artifact.h39Instructions[1342]? = some (.push 32 (tailWord 13)) := by rfl

theorem tail_push (p : Fin 14) (index : Nat) (hi : tailPushIndex p = some index) :
    Artifact.h39Instructions[index]? = some (.push 32 (tailWord p)) := by
  fin_cases p
  · change some 1184 = some index at hi
    have heq := Option.some.inj hi
    subst index
    exact tail_push_0
  · change some 1198 = some index at hi
    have heq := Option.some.inj hi
    subst index
    exact tail_push_1
  · cases hi
  · change some 1220 = some index at hi
    have heq := Option.some.inj hi
    subst index
    exact tail_push_3
  · change some 1234 = some index at hi
    have heq := Option.some.inj hi
    subst index
    exact tail_push_4
  · change some 1248 = some index at hi
    have heq := Option.some.inj hi
    subst index
    exact tail_push_5
  · cases hi
  · change some 1270 = some index at hi
    have heq := Option.some.inj hi
    subst index
    exact tail_push_7
  · change some 1284 = some index at hi
    have heq := Option.some.inj hi
    subst index
    exact tail_push_8
  · change some 1298 = some index at hi
    have heq := Option.some.inj hi
    subst index
    exact tail_push_9
  · cases hi
  · cases hi
  · change some 1328 = some index at hi
    have heq := Option.some.inj hi
    subst index
    exact tail_push_12
  · change some 1342 = some index at hi
    have heq := Option.some.inj hi
    subst index
    exact tail_push_13

end Challenge.Ripemd160.Submission.H39Memo.PatternFacts

