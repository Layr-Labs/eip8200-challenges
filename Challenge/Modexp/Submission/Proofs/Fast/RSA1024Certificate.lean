import Challenge.Modexp.Scorer
import Mathlib.Tactic

namespace Challenge.Modexp.Submission.Proofs.Fast.RSA1024Certificate
open EvmSemantics.EVM

def modulus : Nat := 0xb0d18352a88f53d5516f46c20e7a367d7de88acf54a019f6def57ab9b44ceddb2242b1bca0fb1b5cb82b3036176a63903564dec6eb41db2f8fc787f4e52e1149e33347572973f660c3c77ca9e0821c2b695be7ae9d7d30f4079110f48aae6f8b702d474b2900817f2866249bec12a2b19b8278416808f81ae1fcf9b7778a623f
def base : Nat := 0x1370d5cf7cd3f80baf7ae9fddfdfcc0253d7d1f00fa2985f14456e44cb16bcdf6269d1ed3f20cfd7a7e421752a77c1b47db96367c224e660a706bbceff1e8bae1e5e0c04e5ec10b0a6876d2d05fdf6184e64794efd75567969f9f67444ba5b2d2ddb6b0396504efc38ea5664a4e8f2e76c29bd9d23e15e48b40b5754830bd0f2
def answer : Nat := 0x21d9b8173adcfbc08b66d78be2d7d2226da965bebb68c676de72d78fcc445847ef1012f0bdb13d7f9f972a183e60e8211019135863a5c8c4a5aebd302d9a8d6742cb04e6cc11f92524c25528642bf0de3bc16e3aac0eb16b1c9e45bc7585b3c42a89e5b54a69fdf0e1ad3241812d3449c6947263a1e6dcb942cbfeb9aeeb46bb

private def b1 : Nat := 0x4490ffa21721bb8e3767ccdf11823554e2657fa457aa1d6726a90aa4e1ba1838a83e695fb9cb421b263d32c444ba5875564b991e17bd8375766e2c142eeb55fbafbbc263261046cf4408a58df392f16255481801893f3dd1e81d92db48736f5e7d1cc42d3a64ca0897b49a941c1774b66f311a2a072e1aa1f07e4164dca36766

private theorem hs0 : base * base % modulus = b1 := by
  norm_num [base, b1, modulus]

private theorem hfinal : base * b1 % modulus = answer := by
  norm_num [base, b1, modulus, answer]

theorem certificate : Precompile.modPow base 3 modulus = answer := by
  have hm0 : modulus ≠ 0 := by norm_num [modulus]
  have hm1 : modulus ≠ 1 := by norm_num [modulus]
  have hb : base % modulus = base := by norm_num [base, modulus]
  simp [Precompile.modPow, Precompile.modPowAux, hm0, hm1, hb, hs0, hfinal]

end Challenge.Modexp.Submission.Proofs.Fast.RSA1024Certificate
