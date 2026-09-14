# RIPEMD-160 submission

The exact runtime has 5,233 bytes, 3,789 executable instructions and a 280-byte digest payload. Raw SHA-256: `3d0fa8a4f1bc744ef2c1230d3df90f2b4f5b662804027f62a4597ee18fd7e928`.

This revision updates startup constant construction and its execution certificate on the guard-packed Source32 base `ff5b157d`. The edit occupies the existing startup window; the surrounding bytecode and its instruction positions are retained. The submitted byte representation, typed instructions and assembly witnesses carry the same runtime.

Validation uses the pinned Lean 4.31.0 toolchain and the unchanged protected preparation script. The submission theorem is `Challenge.Ripemd160.Benchmark.candidate`. The private campaign receipt records validation status for the exact source revision; local runtime checks do not constitute official acceptance.

The startup rewrite is adapted from fkiene's public submission `db261f92-eb4d-4c16-b91f-f9906908738f`, source commit `8518c4c5138383bba36e0e96195466a19d6b6c12`. This package includes its independently selected encoding and a targeted proof adaptation. Inherited arithmetic, padding, recognition and serialization contributions retain their existing attribution.
