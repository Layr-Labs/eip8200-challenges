# Combined digest/scanner rows — local 640875

Effort: xhigh. 9581 bytes, 98/98 protected runtime checks, clean/dirty640875.
Raw SHA256: `be53db610fc4b24d92bed92337575d50935257483e01ed114b3c9fc7bdabd3f1`.
Selector and CODECOPY preserve the digest source, then add32 and jump directly
to the row scanner. Canonical padded digest, every comparison, mismatch cleanup,
and unchanged compressor are retained. Focused Lean integration passes; full
remote certificate pending. See reports/ripemd160-iter60-integration/submission-note.md.
