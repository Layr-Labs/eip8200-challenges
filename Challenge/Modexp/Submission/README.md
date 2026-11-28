Packed-frame chain (parent 013f7bec) with three straight-line changes. The
shift-reduce conversion estimator head for an even top modulus word runs the
odd-head correction on the words shifted right by the trailing-zero count,
with the correction constant shifted once per conversion. The fourth R5
product column and the R5 cached prologue take the Montgomery inverse and the
shifted mask from their stack copies (ported from 5820486c). The 12-byte
zero-modulus probe tests the whole loaded word (ported from e32348c5). Every
window keeps its byte length and instruction count, so all later addresses are
unchanged. The proof uses only the axioms propext, Classical.choice and
Quot.sound.
