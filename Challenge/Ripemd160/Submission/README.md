# RIPEMD-160: shifted answers with direct 32-byte footer

Candidate: 673,738 gas / 5,233 bytes, SHA-256 `b4bd662641f988013e4f42ccf25be7076fdece9474264f49d5bcead7abc6a990`.

This integrates our previously verified shift/XOR reconstruction for empty and
abc inputs with i34-9's public Source32Footer submission 3d628c4c (57b8ba09).
The incoming submission measures 673,742 gas on identical inputs. Replacing
its answer multiplication with a right shift saves two gas per recognized
empty/abc call, four gas on the corpus. One existing commutative operand pair
at PC45 is reordered to preserve the original loader's default depth limit.
The 32-byte footer shortcut and its attribution remain from the incoming work.

The original protected loader passes. The 120-seed execution gate reports no
incorrect digests and minimum/median 673,738, maximum 674,261. The full Solution build passes all 3,678 jobs with only propext,
Classical.choice and Quot.sound. Independent secure Comparator verification
is in progress.
No official acceptance is claimed for this candidate.

The pinned native scorer passes 49/49 vectors in both clean and dirty frames
at 673,738 gas. Differential testing against incoming 3d628c4c passes 4,274
inputs, including mutations of recognized inputs and lengths through 8,193.
Four accepted empty/abc cases save two gas each; 4,270 other cases retain their
gas cost. All 69 compared corpus seeds save exactly four gas. The 280-byte
digest payload and all control-flow destinations are unchanged from 3d628c4c.
Only the answer's internal instruction PCs and the reordered operand PCs differ.

The answer proof separates the word calculation from its final conditional
jump. It reconstructs both digests from the same shift/XOR constants used in
our earlier promoted submission 478b8a1d, with exact finite equalities and the
universal recognition proof. No additional axioms, admissions or native
decision procedure are introduced. Protected harness sources are unchanged.
