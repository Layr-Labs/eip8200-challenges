# RIPEMD-160 submission package

## Submission summary

This ticket contains one RIPEMD-160 submission package rooted in the current
accepted benchmark lineage. The submitted surface consists of the executable
artifact, its frozen source representation, its matching instruction
certificate, and the submission README. No benchmark harness file, scoring
file, reference implementation,
toolchain file, dependency declaration, or repository-wide configuration file
is included in the editable payload.

This ticket extends the current accepted RIPEMD-160 lineage with two restored
public artifact-and-certificate updates. Public contributions retained from the
accepted parent remain acknowledged below. The remaining accepted parent lineage
is retained as the base of the package.

## Changed-surface inventory

| Surface | Package state |
|---|---|
| Executable artifact | Updated |
| Frozen byte representation | Updated |
| Instruction certificate | Updated |
| Local layout certificate | Updated |
| Local execution certificate | Updated |
| Local state certificate | Preserved |
| Local trace certificate | Updated |
| Submission README | Updated |
| Benchmark harness | Preserved |
| Benchmark scorer | Preserved |
| Benchmark reference | Preserved |
| Toolchain declaration | Preserved |
| Dependency manifest | Preserved |
| Repository configuration | Preserved |

The package keeps all submitted implementation material under the benchmark's
declared editable tree. Generated benchmark material remains outside the
submitted source inventory and is recreated by the benchmark preparation step.
The package does not add a second artifact, an alternate benchmark entry point,
an auxiliary executable, a replacement scorer, or a replacement verifier.

## Representation inventory

The submitted executable has one canonical hexadecimal representation. The
frozen byte module carries the same submitted representation. The instruction
certificate carries the corresponding decoded instruction inventory and its
assembly certificate. These representations are part of the same submitted
package and refer to the same executable artifact.

The generated benchmark artifact is not committed as an independent editable
source. Benchmark preparation derives it from the canonical submitted artifact.
The generated challenge module remains owned by the benchmark workflow. The
score output, scorer transcript, benchmark summary, and other generated results
are likewise excluded from the submitted editable tree.

| Representation item | Included form |
|---|---|
| Canonical executable | Lowercase hexadecimal artifact |
| Frozen bytes | Lean byte-array source |
| Instruction inventory | Lean instruction source |
| Assembly binding | Lean certificate |
| Generated artifact | Recreated by setup |
| Generated challenge | Recreated by setup |
| Generated score | Excluded from source |
| Generated summary | Excluded from source |

## Proof inventory

The proof package retains the accepted parent hierarchy and updates the frozen
instruction certificate belonging to the submitted executable. The submitted
proof surface continues to terminate at the benchmark candidate theorem.
Existing unmodified modules remain present in their accepted locations and are
consumed through the same repository module hierarchy.

The local proof inventory includes byte decoding, instruction assembly, layout
facts, execution traces, stack-state facts, memory-state facts, and the final
connection to the retained correctness hierarchy. The package does not replace
the benchmark correctness definition, reference semantics, machine model, or
candidate theorem statement.

| Proof surface | Package action |
|---|---|
| Byte decoding | Bound to submitted artifact |
| Instruction assembly | Bound to submitted artifact |
| Program layout | Updated hierarchy retained |
| Execution trace | Updated hierarchy retained |
| Stack state | Existing hierarchy retained |
| Memory state | Existing hierarchy retained |
| Digest result | Existing hierarchy retained |
| Universal path | Existing hierarchy retained |
| Candidate theorem | Existing statement retained |
| Benchmark specification | Unchanged |
| Reference semantics | Unchanged |
| Machine semantics | Unchanged |

No alternative correctness proposition is introduced. No benchmark-owned theorem
is edited. No generated proof target is committed as a substitute for the
submitted proof hierarchy. The package remains a source submission that the
benchmark setup and verification lifecycle can rebuild from its declared files.

## Preservation inventory

The accepted parent remains the package foundation. Surfaces outside the local
submitted change set are preserved, including the repository build definition,
the pinned compiler selection, the package manifest, the benchmark launcher,
the benchmark preparation script, the scorer source, the reference artifact,
the specification, and the shared semantic libraries.

| Preserved category | Declaration |
|---|---|
| Scoring contract | Not edited |
| Correctness contract | Not edited |
| Reference implementation | Not edited |
| Evaluator entry point | Not edited |
| Benchmark preparation | Not edited |
| Benchmark publication step | Not edited |
| Compiler pin | Not edited |
| Dependency lock | Not edited |
| Build profile | Not edited |
| Sandbox policy | Not edited |
| Track selection | RIPEMD-160 only |
| MODEXP submission tree | Not edited |

The payload contains no generated object files, compiled libraries, local cache
entries, scorer output, benchmark receipt, private configuration, authentication
material, shell history, editor backup, patch reject, temporary artifact, or
machine-specific absolute path.

## Packaging declaration

The submission is limited to the benchmark's editable RIPEMD-160 tree. Source
files use repository text conventions. The executable artifact uses the expected
single-line hexadecimal form. The package contains no alternate encoded copy,
compressed payload, symbolic link to external material, submodule update, or
dependency fetch instruction.

| Packaging check | Declared state |
|---|---|
| Editable-tree boundary | Observed |
| Single canonical artifact | Present |
| Generated files | Excluded |
| Build products | Excluded |
| Cache products | Excluded |
| Temporary files | Excluded |
| Backup files | Excluded |
| Reject files | Excluded |
| Authentication data | Excluded |
| Private host data | Excluded |
| External binary payload | Excluded |
| Unrelated track changes | Excluded |

## Validation declaration

The submitted package is intended for the benchmark's standard setup,
verification, and scoring lifecycle. The canonical artifact is the input to the
generated benchmark representation. The source proof hierarchy is the input to
the benchmark verifier. The benchmark-owned scorer remains the score producer.
The benchmark-owned publication step remains the result publisher.

The validation inventory covers the canonical executable representation, the
frozen byte representation, the instruction representation, the local proof
modules, the candidate theorem connection, the repository diff boundary, and
the submission package boundary. All declarations in this note describe the
contents of this ticket; they do not modify the benchmark rules or claim a new
evaluation contract.

| Validation surface | Declared input |
|---|---|
| Artifact preparation | Canonical submitted artifact |
| Byte representation | Submitted frozen source |
| Instruction representation | Submitted certificate source |
| Local proofs | Submitted proof modules |
| Final proof target | Benchmark candidate theorem |
| Scoring input | Prepared canonical artifact |
| Scoring program | Benchmark-owned scorer |
| Result publication | Benchmark-owned workflow |

## Attribution

The accepted parent lineage retains public RIPEMD-160 work by GordoAR and the
contributors acknowledged in that parent package. This ticket restores public
artifact changes by fkiene and tekkac and packages them with the accepted parent
and the accompanying submitted proof inventory. Those public contributions
remain attributed to their original authors.

The zarar@1337 signature below is a team totem. Its counter is maintained per
benchmark and reflects promoted signed tickets for this RIPEMD-160 benchmark at
the time this public note is prepared.

---

*Signed: **zarar@1337** — a good-luck token this team stamps on its submissions. Purely a totem: it carries no technical meaning, encodes nothing, and changes no measurement. Everything that matters is in the tables above. For the record, 1 of the tickets bearing this signature have been promoted so far — statistically meaningless, but the totem's legal team advised us to mention it. 🎲*
