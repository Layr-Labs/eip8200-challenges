import Challenge.Modexp.Submission.Proofs.Fast.Defs
set_option warningAsError true
set_option maxRecDepth 40000
set_option maxHeartbeats 4000000
/-! Basic-block instruction paths, group 14 (instructions 1742..1767).

`CCB` (pc 2863) replaces the second `DOUBLE256` call: it doubles `CC` once
through `ADDMOD` and then squares it eight times through `MONPRO`, which
carries `R mod m` to `radix * R mod m` in `8` Montgomery multiplications
instead of `256` modular doublings. -/

namespace Challenge.Modexp.Submission.Proofs.Fast

open EvmSemantics
open EvmSemantics.EVM
open Challenge.Modexp.Submission.Proofs.Bytecode

/-- Instructions 1742..1748, pc 2863..2873: `CCB` entry, `ADDMOD(px, px) → px`. -/
def blk1742 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 1990 .JUMPDEST,
   pushAt 1991 2 2887,
   opAt 1992 (.Dup ⟨1, by decide⟩),
   opAt 1993 (.Dup ⟨0, by decide⟩),
   opAt 1994 (.Dup ⟨0, by decide⟩),
   pushAt 1995 2 2480,
   opAt 1996 .JUMP]

/-- Instructions 1749..1750, pc 2874..2876: the squaring counter. -/
def blk1749 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 1997 .JUMPDEST,
   pushAt 1998 1 8]

/-- Instructions 1751..1757, pc 2877..2887: `MONPRO(px, px) → px`. -/
def blk1751 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 1999 .JUMPDEST,
   pushAt 2000 2 2901,
   opAt 2001 (.Dup ⟨2, by decide⟩),
   opAt 2002 (.Dup ⟨0, by decide⟩),
   opAt 2003 (.Dup ⟨0, by decide⟩),
   pushAt 2004 2 1939,
   opAt 2005 .JUMP]

/-- Instructions 1758..1764, pc 2888..2897: decrement and loop back. -/
def blk1758 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2006 .JUMPDEST,
   pushAt 2007 0 0,
   opAt 2008 .NOT,
   opAt 2009 .ADD,
   opAt 2010 (.Dup ⟨0, by decide⟩),
   pushAt 2011 3 2890,
   opAt 2012 .JUMPI]

/-- Instructions 1765..1767, pc 2898..2900: drop the counter and return. -/
def blk1765 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2013 .POP,
   opAt 2014 .POP,
   opAt 2015 .JUMP]

end Challenge.Modexp.Submission.Proofs.Fast
