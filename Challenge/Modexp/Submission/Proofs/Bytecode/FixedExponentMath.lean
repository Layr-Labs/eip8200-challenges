import Challenge.Modexp.Submission.Proofs.Bytecode.WindowMath
set_option warningAsError true
set_option maxRecDepth 4096
set_option maxHeartbeats 2000000
namespace HistoricalSearch.FixedExponent
open EvmSemantics EvmSemantics.EVM
open Challenge.Modexp.Submission.Proofs.Bytecode

theorem mulMod_power (base modulus left right : UInt256) (a b c : Nat) (hsum : a+b=c)
    (hm : 0 < modulus.toNat)
    (hl : left.toNat % modulus.toNat = base.toNat ^ a % modulus.toNat)
    (hr : right.toNat % modulus.toNat = base.toNat ^ b % modulus.toNat) :
    (UInt256.mulMod left right modulus).toNat % modulus.toNat =
      base.toNat ^ c % modulus.toNat := by
  rw [← hsum]
  rw [WindowMath.mulMod_toNat _ _ _ hm, Nat.mod_mod,
    Nat.mul_mod left.toNat right.toNat, hl, hr, ← Nat.mul_mod, ← Nat.pow_add]

def value (base modulus : UInt256) : UInt256 :=
  let x0 := base
  let x1 := UInt256.mulMod x0 x0 modulus
  let x2 := UInt256.mulMod x0 x1 modulus
  let x3 := UInt256.mulMod x1 x2 modulus
  let x4 := UInt256.mulMod x1 x3 modulus
  let x5 := UInt256.mulMod x1 x4 modulus
  let x6 := UInt256.mulMod x1 x5 modulus
  let x7 := UInt256.mulMod x1 x6 modulus
  let x8 := UInt256.mulMod x1 x7 modulus
  let x9 := UInt256.mulMod x5 x8 modulus
  let x10 := UInt256.mulMod x9 x9 modulus
  let x11 := UInt256.mulMod x10 x10 modulus
  let x12 := UInt256.mulMod x11 x11 modulus
  let x13 := UInt256.mulMod x0 x12 modulus
  let x14 := UInt256.mulMod x13 x13 modulus
  let x15 := UInt256.mulMod x14 x14 modulus
  let x16 := UInt256.mulMod x15 x15 modulus
  let x17 := UInt256.mulMod x16 x16 modulus
  let x18 := UInt256.mulMod x5 x17 modulus
  let x19 := UInt256.mulMod x18 x18 modulus
  let x20 := UInt256.mulMod x19 x19 modulus
  let x21 := UInt256.mulMod x20 x20 modulus
  let x22 := UInt256.mulMod x21 x21 modulus
  let x23 := UInt256.mulMod x0 x22 modulus
  let x24 := UInt256.mulMod x23 x23 modulus
  let x25 := UInt256.mulMod x24 x24 modulus
  let x26 := UInt256.mulMod x25 x25 modulus
  let x27 := UInt256.mulMod x26 x26 modulus
  let x28 := UInt256.mulMod x27 x27 modulus
  let x29 := UInt256.mulMod x4 x28 modulus
  let x30 := UInt256.mulMod x29 x29 modulus
  let x31 := UInt256.mulMod x30 x30 modulus
  let x32 := UInt256.mulMod x31 x31 modulus
  let x33 := UInt256.mulMod x32 x32 modulus
  let x34 := UInt256.mulMod x33 x33 modulus
  let x35 := UInt256.mulMod x4 x34 modulus
  let x36 := UInt256.mulMod x35 x35 modulus
  let x37 := UInt256.mulMod x36 x36 modulus
  let x38 := UInt256.mulMod x37 x37 modulus
  let x39 := UInt256.mulMod x0 x38 modulus
  let x40 := UInt256.mulMod x39 x39 modulus
  let x41 := UInt256.mulMod x40 x40 modulus
  let x42 := UInt256.mulMod x41 x41 modulus
  let x43 := UInt256.mulMod x42 x42 modulus
  let x44 := UInt256.mulMod x4 x43 modulus
  let x45 := UInt256.mulMod x44 x44 modulus
  let x46 := UInt256.mulMod x45 x45 modulus
  let x47 := UInt256.mulMod x46 x46 modulus
  let x48 := UInt256.mulMod x47 x47 modulus
  let x49 := UInt256.mulMod x48 x48 modulus
  let x50 := UInt256.mulMod x0 x49 modulus
  let x51 := UInt256.mulMod x50 x50 modulus
  let x52 := UInt256.mulMod x51 x51 modulus
  let x53 := UInt256.mulMod x52 x52 modulus
  let x54 := UInt256.mulMod x53 x53 modulus
  let x55 := UInt256.mulMod x2 x54 modulus
  let x56 := UInt256.mulMod x55 x55 modulus
  let x57 := UInt256.mulMod x56 x56 modulus
  let x58 := UInt256.mulMod x57 x57 modulus
  let x59 := UInt256.mulMod x58 x58 modulus
  let x60 := UInt256.mulMod x59 x59 modulus
  let x61 := UInt256.mulMod x60 x60 modulus
  let x62 := UInt256.mulMod x61 x61 modulus
  let x63 := UInt256.mulMod x7 x62 modulus
  let x64 := UInt256.mulMod x63 x63 modulus
  let x65 := UInt256.mulMod x64 x64 modulus
  let x66 := UInt256.mulMod x65 x65 modulus
  let x67 := UInt256.mulMod x66 x66 modulus
  let x68 := UInt256.mulMod x67 x67 modulus
  let x69 := UInt256.mulMod x68 x68 modulus
  let x70 := UInt256.mulMod x69 x69 modulus
  let x71 := UInt256.mulMod x70 x70 modulus
  let x72 := UInt256.mulMod x71 x71 modulus
  let x73 := UInt256.mulMod x72 x72 modulus
  let x74 := UInt256.mulMod x3 x73 modulus
  let x75 := UInt256.mulMod x74 x74 modulus
  let x76 := UInt256.mulMod x75 x75 modulus
  let x77 := UInt256.mulMod x76 x76 modulus
  let x78 := UInt256.mulMod x77 x77 modulus
  let x79 := UInt256.mulMod x2 x78 modulus
  let x80 := UInt256.mulMod x79 x79 modulus
  let x81 := UInt256.mulMod x80 x80 modulus
  let x82 := UInt256.mulMod x81 x81 modulus
  let x83 := UInt256.mulMod x82 x82 modulus
  let x84 := UInt256.mulMod x4 x83 modulus
  let x85 := UInt256.mulMod x84 x84 modulus
  let x86 := UInt256.mulMod x85 x85 modulus
  let x87 := UInt256.mulMod x86 x86 modulus
  let x88 := UInt256.mulMod x87 x87 modulus
  let x89 := UInt256.mulMod x88 x88 modulus
  let x90 := UInt256.mulMod x89 x89 modulus
  let x91 := UInt256.mulMod x90 x90 modulus
  let x92 := UInt256.mulMod x3 x91 modulus
  let x93 := UInt256.mulMod x92 x92 modulus
  let x94 := UInt256.mulMod x93 x93 modulus
  let x95 := UInt256.mulMod x94 x94 modulus
  let x96 := UInt256.mulMod x95 x95 modulus
  let x97 := UInt256.mulMod x96 x96 modulus
  let x98 := UInt256.mulMod x97 x97 modulus
  let x99 := UInt256.mulMod x0 x98 modulus
  let x100 := UInt256.mulMod x99 x99 modulus
  let x101 := UInt256.mulMod x100 x100 modulus
  let x102 := UInt256.mulMod x101 x101 modulus
  let x103 := UInt256.mulMod x102 x102 modulus
  let x104 := UInt256.mulMod x103 x103 modulus
  let x105 := UInt256.mulMod x104 x104 modulus
  let x106 := UInt256.mulMod x3 x105 modulus
  let x107 := UInt256.mulMod x106 x106 modulus
  let x108 := UInt256.mulMod x107 x107 modulus
  let x109 := UInt256.mulMod x108 x108 modulus
  let x110 := UInt256.mulMod x109 x109 modulus
  let x111 := UInt256.mulMod x6 x110 modulus
  let x112 := UInt256.mulMod x111 x111 modulus
  let x113 := UInt256.mulMod x112 x112 modulus
  let x114 := UInt256.mulMod x113 x113 modulus
  let x115 := UInt256.mulMod x114 x114 modulus
  let x116 := UInt256.mulMod x115 x115 modulus
  let x117 := UInt256.mulMod x7 x116 modulus
  let x118 := UInt256.mulMod x117 x117 modulus
  let x119 := UInt256.mulMod x118 x118 modulus
  let x120 := UInt256.mulMod x119 x119 modulus
  let x121 := UInt256.mulMod x120 x120 modulus
  let x122 := UInt256.mulMod x121 x121 modulus
  let x123 := UInt256.mulMod x122 x122 modulus
  let x124 := UInt256.mulMod x123 x123 modulus
  let x125 := UInt256.mulMod x124 x124 modulus
  let x126 := UInt256.mulMod x2 x125 modulus
  let x127 := UInt256.mulMod x126 x126 modulus
  let x128 := UInt256.mulMod x127 x127 modulus
  let x129 := UInt256.mulMod x128 x128 modulus
  let x130 := UInt256.mulMod x129 x129 modulus
  let x131 := UInt256.mulMod x130 x130 modulus
  let x132 := UInt256.mulMod x131 x131 modulus
  let x133 := UInt256.mulMod x132 x132 modulus
  let x134 := UInt256.mulMod x0 x133 modulus
  let x135 := UInt256.mulMod x134 x134 modulus
  let x136 := UInt256.mulMod x135 x135 modulus
  let x137 := UInt256.mulMod x136 x136 modulus
  let x138 := UInt256.mulMod x137 x137 modulus
  let x139 := UInt256.mulMod x138 x138 modulus
  let x140 := UInt256.mulMod x6 x139 modulus
  let x141 := UInt256.mulMod x140 x140 modulus
  let x142 := UInt256.mulMod x141 x141 modulus
  let x143 := UInt256.mulMod x142 x142 modulus
  let x144 := UInt256.mulMod x143 x143 modulus
  let x145 := UInt256.mulMod x144 x144 modulus
  let x146 := UInt256.mulMod x145 x145 modulus
  let x147 := UInt256.mulMod x146 x146 modulus
  let x148 := UInt256.mulMod x147 x147 modulus
  let x149 := UInt256.mulMod x6 x148 modulus
  let x150 := UInt256.mulMod x149 x149 modulus
  let x151 := UInt256.mulMod x150 x150 modulus
  let x152 := UInt256.mulMod x151 x151 modulus
  let x153 := UInt256.mulMod x152 x152 modulus
  let x154 := UInt256.mulMod x6 x153 modulus
  let x155 := UInt256.mulMod x154 x154 modulus
  let x156 := UInt256.mulMod x155 x155 modulus
  let x157 := UInt256.mulMod x156 x156 modulus
  let x158 := UInt256.mulMod x0 x157 modulus
  let x159 := UInt256.mulMod x158 x158 modulus
  let x160 := UInt256.mulMod x159 x159 modulus
  let x161 := UInt256.mulMod x160 x160 modulus
  let x162 := UInt256.mulMod x161 x161 modulus
  let x163 := UInt256.mulMod x162 x162 modulus
  let x164 := UInt256.mulMod x8 x163 modulus
  let x165 := UInt256.mulMod x164 x164 modulus
  let x166 := UInt256.mulMod x165 x165 modulus
  let x167 := UInt256.mulMod x166 x166 modulus
  let x168 := UInt256.mulMod x167 x167 modulus
  let x169 := UInt256.mulMod x168 x168 modulus
  let x170 := UInt256.mulMod x169 x169 modulus
  let x171 := UInt256.mulMod x170 x170 modulus
  let x172 := UInt256.mulMod x171 x171 modulus
  let x173 := UInt256.mulMod x172 x172 modulus
  let x174 := UInt256.mulMod x173 x173 modulus
  let x175 := UInt256.mulMod x6 x174 modulus
  let x176 := UInt256.mulMod x175 x175 modulus
  let x177 := UInt256.mulMod x176 x176 modulus
  let x178 := UInt256.mulMod x177 x177 modulus
  let x179 := UInt256.mulMod x178 x178 modulus
  let x180 := UInt256.mulMod x3 x179 modulus
  let x181 := UInt256.mulMod x180 x180 modulus
  let x182 := UInt256.mulMod x181 x181 modulus
  let x183 := UInt256.mulMod x182 x182 modulus
  let x184 := UInt256.mulMod x183 x183 modulus
  let x185 := UInt256.mulMod x184 x184 modulus
  let x186 := UInt256.mulMod x5 x185 modulus
  let x187 := UInt256.mulMod x186 x186 modulus
  let x188 := UInt256.mulMod x187 x187 modulus
  let x189 := UInt256.mulMod x188 x188 modulus
  let x190 := UInt256.mulMod x189 x189 modulus
  let x191 := UInt256.mulMod x0 x190 modulus
  let x192 := UInt256.mulMod x191 x191 modulus
  let x193 := UInt256.mulMod x192 x192 modulus
  let x194 := UInt256.mulMod x193 x193 modulus
  let x195 := UInt256.mulMod x194 x194 modulus
  let x196 := UInt256.mulMod x195 x195 modulus
  let x197 := UInt256.mulMod x7 x196 modulus
  let x198 := UInt256.mulMod x197 x197 modulus
  let x199 := UInt256.mulMod x198 x198 modulus
  let x200 := UInt256.mulMod x199 x199 modulus
  let x201 := UInt256.mulMod x200 x200 modulus
  let x202 := UInt256.mulMod x201 x201 modulus
  let x203 := UInt256.mulMod x202 x202 modulus
  let x204 := UInt256.mulMod x203 x203 modulus
  let x205 := UInt256.mulMod x4 x204 modulus
  let x206 := UInt256.mulMod x205 x205 modulus
  let x207 := UInt256.mulMod x206 x206 modulus
  let x208 := UInt256.mulMod x207 x207 modulus
  let x209 := UInt256.mulMod x208 x208 modulus
  let x210 := UInt256.mulMod x209 x209 modulus
  let x211 := UInt256.mulMod x210 x210 modulus
  let x212 := UInt256.mulMod x4 x211 modulus
  let x213 := UInt256.mulMod x212 x212 modulus
  let x214 := UInt256.mulMod x213 x213 modulus
  let x215 := UInt256.mulMod x214 x214 modulus
  let x216 := UInt256.mulMod x0 x215 modulus
  let x217 := UInt256.mulMod x216 x216 modulus
  let x218 := UInt256.mulMod x217 x217 modulus
  let x219 := UInt256.mulMod x218 x218 modulus
  let x220 := UInt256.mulMod x219 x219 modulus
  let x221 := UInt256.mulMod x3 x220 modulus
  let x222 := UInt256.mulMod x221 x221 modulus
  let x223 := UInt256.mulMod x222 x222 modulus
  let x224 := UInt256.mulMod x223 x223 modulus
  let x225 := UInt256.mulMod x224 x224 modulus
  let x226 := UInt256.mulMod x225 x225 modulus
  let x227 := UInt256.mulMod x226 x226 modulus
  let x228 := UInt256.mulMod x227 x227 modulus
  let x229 := UInt256.mulMod x7 x228 modulus
  let x230 := UInt256.mulMod x229 x229 modulus
  let x231 := UInt256.mulMod x230 x230 modulus
  let x232 := UInt256.mulMod x231 x231 modulus
  let x233 := UInt256.mulMod x232 x232 modulus
  let x234 := UInt256.mulMod x233 x233 modulus
  let x235 := UInt256.mulMod x234 x234 modulus
  let x236 := UInt256.mulMod x8 x235 modulus
  let x237 := UInt256.mulMod x236 x236 modulus
  let x238 := UInt256.mulMod x237 x237 modulus
  let x239 := UInt256.mulMod x238 x238 modulus
  let x240 := UInt256.mulMod x239 x239 modulus
  let x241 := UInt256.mulMod x240 x240 modulus
  let x242 := UInt256.mulMod x0 x241 modulus
  let x243 := UInt256.mulMod x242 x242 modulus
  let x244 := UInt256.mulMod x243 x243 modulus
  let x245 := UInt256.mulMod x244 x244 modulus
  let x246 := UInt256.mulMod x245 x245 modulus
  let x247 := UInt256.mulMod x246 x246 modulus
  let x248 := UInt256.mulMod x247 x247 modulus
  let x249 := UInt256.mulMod x0 x248 modulus
  let x250 := UInt256.mulMod x249 x249 modulus
  let x251 := UInt256.mulMod x250 x250 modulus
  let x252 := UInt256.mulMod x251 x251 modulus
  let x253 := UInt256.mulMod x252 x252 modulus
  let x254 := UInt256.mulMod x253 x253 modulus
  let x255 := UInt256.mulMod x2 x254 modulus
  let x256 := UInt256.mulMod x255 x255 modulus
  let x257 := UInt256.mulMod x256 x256 modulus
  let x258 := UInt256.mulMod x257 x257 modulus
  let x259 := UInt256.mulMod x258 x258 modulus
  let x260 := UInt256.mulMod x259 x259 modulus
  let x261 := UInt256.mulMod x260 x260 modulus
  let x262 := UInt256.mulMod x0 x261 modulus
  let x263 := UInt256.mulMod x262 x262 modulus
  let x264 := UInt256.mulMod x263 x263 modulus
  let x265 := UInt256.mulMod x264 x264 modulus
  let x266 := UInt256.mulMod x265 x265 modulus
  let x267 := UInt256.mulMod x266 x266 modulus
  let x268 := UInt256.mulMod x7 x267 modulus
  let x269 := UInt256.mulMod x268 x268 modulus
  let x270 := UInt256.mulMod x269 x269 modulus
  let x271 := UInt256.mulMod x270 x270 modulus
  let x272 := UInt256.mulMod x271 x271 modulus
  let x273 := UInt256.mulMod x6 x272 modulus
  let x274 := UInt256.mulMod x273 x273 modulus
  let x275 := UInt256.mulMod x274 x274 modulus
  let x276 := UInt256.mulMod x275 x275 modulus
  let x277 := UInt256.mulMod x276 x276 modulus
  let x278 := UInt256.mulMod x277 x277 modulus
  let x279 := UInt256.mulMod x0 x278 modulus
  let x280 := UInt256.mulMod x279 x279 modulus
  let x281 := UInt256.mulMod x280 x280 modulus
  let x282 := UInt256.mulMod x281 x281 modulus
  let x283 := UInt256.mulMod x282 x282 modulus
  let x284 := UInt256.mulMod x8 x283 modulus
  let x285 := UInt256.mulMod x284 x284 modulus
  let x286 := UInt256.mulMod x285 x285 modulus
  let x287 := UInt256.mulMod x286 x286 modulus
  let x288 := UInt256.mulMod x287 x287 modulus
  let x289 := UInt256.mulMod x288 x288 modulus
  let x290 := UInt256.mulMod x289 x289 modulus
  let x291 := UInt256.mulMod x8 x290 modulus
  let x292 := UInt256.mulMod x291 x291 modulus
  let x293 := UInt256.mulMod x292 x292 modulus
  let x294 := UInt256.mulMod x293 x293 modulus
  let x295 := UInt256.mulMod x294 x294 modulus
  let x296 := UInt256.mulMod x7 x295 modulus
  let x297 := UInt256.mulMod x296 x296 modulus
  let x298 := UInt256.mulMod x297 x297 modulus
  let x299 := UInt256.mulMod x0 x298 modulus
  let x300 := UInt256.mulMod x299 x299 modulus
  let x301 := UInt256.mulMod x300 x300 modulus
  let x302 := UInt256.mulMod x301 x301 modulus
  let x303 := UInt256.mulMod x302 x302 modulus
  let x304 := UInt256.mulMod x303 x303 modulus
  let x305 := UInt256.mulMod x304 x304 modulus
  let x306 := UInt256.mulMod x3 x305 modulus
  x306

theorem value_toNat (base modulus : UInt256) (hm : 0 < modulus.toNat) :
  (value base modulus).toNat =
    base.toNat ^ 21888242871839275222246405745257275088696311157297823662689037894645226208581 % modulus.toNat := by
  let x0 := base
  have h0 : x0.toNat % modulus.toNat = base.toNat ^ 1 % modulus.toNat := by simp [x0]
  let x1 := UInt256.mulMod x0 x0 modulus
  have h1 : x1.toNat % modulus.toNat = base.toNat ^ 2 % modulus.toNat :=
    mulMod_power base modulus x0 x0 1 1 2 (by decide) hm h0 h0
  let x2 := UInt256.mulMod x0 x1 modulus
  have h2 : x2.toNat % modulus.toNat = base.toNat ^ 3 % modulus.toNat :=
    mulMod_power base modulus x0 x1 1 2 3 (by decide) hm h0 h1
  let x3 := UInt256.mulMod x1 x2 modulus
  have h3 : x3.toNat % modulus.toNat = base.toNat ^ 5 % modulus.toNat :=
    mulMod_power base modulus x1 x2 2 3 5 (by decide) hm h1 h2
  let x4 := UInt256.mulMod x1 x3 modulus
  have h4 : x4.toNat % modulus.toNat = base.toNat ^ 7 % modulus.toNat :=
    mulMod_power base modulus x1 x3 2 5 7 (by decide) hm h1 h3
  let x5 := UInt256.mulMod x1 x4 modulus
  have h5 : x5.toNat % modulus.toNat = base.toNat ^ 9 % modulus.toNat :=
    mulMod_power base modulus x1 x4 2 7 9 (by decide) hm h1 h4
  let x6 := UInt256.mulMod x1 x5 modulus
  have h6 : x6.toNat % modulus.toNat = base.toNat ^ 11 % modulus.toNat :=
    mulMod_power base modulus x1 x5 2 9 11 (by decide) hm h1 h5
  let x7 := UInt256.mulMod x1 x6 modulus
  have h7 : x7.toNat % modulus.toNat = base.toNat ^ 13 % modulus.toNat :=
    mulMod_power base modulus x1 x6 2 11 13 (by decide) hm h1 h6
  let x8 := UInt256.mulMod x1 x7 modulus
  have h8 : x8.toNat % modulus.toNat = base.toNat ^ 15 % modulus.toNat :=
    mulMod_power base modulus x1 x7 2 13 15 (by decide) hm h1 h7
  let x9 := UInt256.mulMod x5 x8 modulus
  have h9 : x9.toNat % modulus.toNat = base.toNat ^ 24 % modulus.toNat :=
    mulMod_power base modulus x5 x8 9 15 24 (by decide) hm h5 h8
  let x10 := UInt256.mulMod x9 x9 modulus
  have h10 : x10.toNat % modulus.toNat = base.toNat ^ 48 % modulus.toNat :=
    mulMod_power base modulus x9 x9 24 24 48 (by decide) hm h9 h9
  let x11 := UInt256.mulMod x10 x10 modulus
  have h11 : x11.toNat % modulus.toNat = base.toNat ^ 96 % modulus.toNat :=
    mulMod_power base modulus x10 x10 48 48 96 (by decide) hm h10 h10
  let x12 := UInt256.mulMod x11 x11 modulus
  have h12 : x12.toNat % modulus.toNat = base.toNat ^ 192 % modulus.toNat :=
    mulMod_power base modulus x11 x11 96 96 192 (by decide) hm h11 h11
  let x13 := UInt256.mulMod x0 x12 modulus
  have h13 : x13.toNat % modulus.toNat = base.toNat ^ 193 % modulus.toNat :=
    mulMod_power base modulus x0 x12 1 192 193 (by decide) hm h0 h12
  let x14 := UInt256.mulMod x13 x13 modulus
  have h14 : x14.toNat % modulus.toNat = base.toNat ^ 386 % modulus.toNat :=
    mulMod_power base modulus x13 x13 193 193 386 (by decide) hm h13 h13
  let x15 := UInt256.mulMod x14 x14 modulus
  have h15 : x15.toNat % modulus.toNat = base.toNat ^ 772 % modulus.toNat :=
    mulMod_power base modulus x14 x14 386 386 772 (by decide) hm h14 h14
  let x16 := UInt256.mulMod x15 x15 modulus
  have h16 : x16.toNat % modulus.toNat = base.toNat ^ 1544 % modulus.toNat :=
    mulMod_power base modulus x15 x15 772 772 1544 (by decide) hm h15 h15
  let x17 := UInt256.mulMod x16 x16 modulus
  have h17 : x17.toNat % modulus.toNat = base.toNat ^ 3088 % modulus.toNat :=
    mulMod_power base modulus x16 x16 1544 1544 3088 (by decide) hm h16 h16
  let x18 := UInt256.mulMod x5 x17 modulus
  have h18 : x18.toNat % modulus.toNat = base.toNat ^ 3097 % modulus.toNat :=
    mulMod_power base modulus x5 x17 9 3088 3097 (by decide) hm h5 h17
  let x19 := UInt256.mulMod x18 x18 modulus
  have h19 : x19.toNat % modulus.toNat = base.toNat ^ 6194 % modulus.toNat :=
    mulMod_power base modulus x18 x18 3097 3097 6194 (by decide) hm h18 h18
  let x20 := UInt256.mulMod x19 x19 modulus
  have h20 : x20.toNat % modulus.toNat = base.toNat ^ 12388 % modulus.toNat :=
    mulMod_power base modulus x19 x19 6194 6194 12388 (by decide) hm h19 h19
  let x21 := UInt256.mulMod x20 x20 modulus
  have h21 : x21.toNat % modulus.toNat = base.toNat ^ 24776 % modulus.toNat :=
    mulMod_power base modulus x20 x20 12388 12388 24776 (by decide) hm h20 h20
  let x22 := UInt256.mulMod x21 x21 modulus
  have h22 : x22.toNat % modulus.toNat = base.toNat ^ 49552 % modulus.toNat :=
    mulMod_power base modulus x21 x21 24776 24776 49552 (by decide) hm h21 h21
  let x23 := UInt256.mulMod x0 x22 modulus
  have h23 : x23.toNat % modulus.toNat = base.toNat ^ 49553 % modulus.toNat :=
    mulMod_power base modulus x0 x22 1 49552 49553 (by decide) hm h0 h22
  let x24 := UInt256.mulMod x23 x23 modulus
  have h24 : x24.toNat % modulus.toNat = base.toNat ^ 99106 % modulus.toNat :=
    mulMod_power base modulus x23 x23 49553 49553 99106 (by decide) hm h23 h23
  let x25 := UInt256.mulMod x24 x24 modulus
  have h25 : x25.toNat % modulus.toNat = base.toNat ^ 198212 % modulus.toNat :=
    mulMod_power base modulus x24 x24 99106 99106 198212 (by decide) hm h24 h24
  let x26 := UInt256.mulMod x25 x25 modulus
  have h26 : x26.toNat % modulus.toNat = base.toNat ^ 396424 % modulus.toNat :=
    mulMod_power base modulus x25 x25 198212 198212 396424 (by decide) hm h25 h25
  let x27 := UInt256.mulMod x26 x26 modulus
  have h27 : x27.toNat % modulus.toNat = base.toNat ^ 792848 % modulus.toNat :=
    mulMod_power base modulus x26 x26 396424 396424 792848 (by decide) hm h26 h26
  let x28 := UInt256.mulMod x27 x27 modulus
  have h28 : x28.toNat % modulus.toNat = base.toNat ^ 1585696 % modulus.toNat :=
    mulMod_power base modulus x27 x27 792848 792848 1585696 (by decide) hm h27 h27
  let x29 := UInt256.mulMod x4 x28 modulus
  have h29 : x29.toNat % modulus.toNat = base.toNat ^ 1585703 % modulus.toNat :=
    mulMod_power base modulus x4 x28 7 1585696 1585703 (by decide) hm h4 h28
  let x30 := UInt256.mulMod x29 x29 modulus
  have h30 : x30.toNat % modulus.toNat = base.toNat ^ 3171406 % modulus.toNat :=
    mulMod_power base modulus x29 x29 1585703 1585703 3171406 (by decide) hm h29 h29
  let x31 := UInt256.mulMod x30 x30 modulus
  have h31 : x31.toNat % modulus.toNat = base.toNat ^ 6342812 % modulus.toNat :=
    mulMod_power base modulus x30 x30 3171406 3171406 6342812 (by decide) hm h30 h30
  let x32 := UInt256.mulMod x31 x31 modulus
  have h32 : x32.toNat % modulus.toNat = base.toNat ^ 12685624 % modulus.toNat :=
    mulMod_power base modulus x31 x31 6342812 6342812 12685624 (by decide) hm h31 h31
  let x33 := UInt256.mulMod x32 x32 modulus
  have h33 : x33.toNat % modulus.toNat = base.toNat ^ 25371248 % modulus.toNat :=
    mulMod_power base modulus x32 x32 12685624 12685624 25371248 (by decide) hm h32 h32
  let x34 := UInt256.mulMod x33 x33 modulus
  have h34 : x34.toNat % modulus.toNat = base.toNat ^ 50742496 % modulus.toNat :=
    mulMod_power base modulus x33 x33 25371248 25371248 50742496 (by decide) hm h33 h33
  let x35 := UInt256.mulMod x4 x34 modulus
  have h35 : x35.toNat % modulus.toNat = base.toNat ^ 50742503 % modulus.toNat :=
    mulMod_power base modulus x4 x34 7 50742496 50742503 (by decide) hm h4 h34
  let x36 := UInt256.mulMod x35 x35 modulus
  have h36 : x36.toNat % modulus.toNat = base.toNat ^ 101485006 % modulus.toNat :=
    mulMod_power base modulus x35 x35 50742503 50742503 101485006 (by decide) hm h35 h35
  let x37 := UInt256.mulMod x36 x36 modulus
  have h37 : x37.toNat % modulus.toNat = base.toNat ^ 202970012 % modulus.toNat :=
    mulMod_power base modulus x36 x36 101485006 101485006 202970012 (by decide) hm h36 h36
  let x38 := UInt256.mulMod x37 x37 modulus
  have h38 : x38.toNat % modulus.toNat = base.toNat ^ 405940024 % modulus.toNat :=
    mulMod_power base modulus x37 x37 202970012 202970012 405940024 (by decide) hm h37 h37
  let x39 := UInt256.mulMod x0 x38 modulus
  have h39 : x39.toNat % modulus.toNat = base.toNat ^ 405940025 % modulus.toNat :=
    mulMod_power base modulus x0 x38 1 405940024 405940025 (by decide) hm h0 h38
  let x40 := UInt256.mulMod x39 x39 modulus
  have h40 : x40.toNat % modulus.toNat = base.toNat ^ 811880050 % modulus.toNat :=
    mulMod_power base modulus x39 x39 405940025 405940025 811880050 (by decide) hm h39 h39
  let x41 := UInt256.mulMod x40 x40 modulus
  have h41 : x41.toNat % modulus.toNat = base.toNat ^ 1623760100 % modulus.toNat :=
    mulMod_power base modulus x40 x40 811880050 811880050 1623760100 (by decide) hm h40 h40
  let x42 := UInt256.mulMod x41 x41 modulus
  have h42 : x42.toNat % modulus.toNat = base.toNat ^ 3247520200 % modulus.toNat :=
    mulMod_power base modulus x41 x41 1623760100 1623760100 3247520200 (by decide) hm h41 h41
  let x43 := UInt256.mulMod x42 x42 modulus
  have h43 : x43.toNat % modulus.toNat = base.toNat ^ 6495040400 % modulus.toNat :=
    mulMod_power base modulus x42 x42 3247520200 3247520200 6495040400 (by decide) hm h42 h42
  let x44 := UInt256.mulMod x4 x43 modulus
  have h44 : x44.toNat % modulus.toNat = base.toNat ^ 6495040407 % modulus.toNat :=
    mulMod_power base modulus x4 x43 7 6495040400 6495040407 (by decide) hm h4 h43
  let x45 := UInt256.mulMod x44 x44 modulus
  have h45 : x45.toNat % modulus.toNat = base.toNat ^ 12990080814 % modulus.toNat :=
    mulMod_power base modulus x44 x44 6495040407 6495040407 12990080814 (by decide) hm h44 h44
  let x46 := UInt256.mulMod x45 x45 modulus
  have h46 : x46.toNat % modulus.toNat = base.toNat ^ 25980161628 % modulus.toNat :=
    mulMod_power base modulus x45 x45 12990080814 12990080814 25980161628 (by decide) hm h45 h45
  let x47 := UInt256.mulMod x46 x46 modulus
  have h47 : x47.toNat % modulus.toNat = base.toNat ^ 51960323256 % modulus.toNat :=
    mulMod_power base modulus x46 x46 25980161628 25980161628 51960323256 (by decide) hm h46 h46
  let x48 := UInt256.mulMod x47 x47 modulus
  have h48 : x48.toNat % modulus.toNat = base.toNat ^ 103920646512 % modulus.toNat :=
    mulMod_power base modulus x47 x47 51960323256 51960323256 103920646512 (by decide) hm h47 h47
  let x49 := UInt256.mulMod x48 x48 modulus
  have h49 : x49.toNat % modulus.toNat = base.toNat ^ 207841293024 % modulus.toNat :=
    mulMod_power base modulus x48 x48 103920646512 103920646512 207841293024 (by decide) hm h48 h48
  let x50 := UInt256.mulMod x0 x49 modulus
  have h50 : x50.toNat % modulus.toNat = base.toNat ^ 207841293025 % modulus.toNat :=
    mulMod_power base modulus x0 x49 1 207841293024 207841293025 (by decide) hm h0 h49
  let x51 := UInt256.mulMod x50 x50 modulus
  have h51 : x51.toNat % modulus.toNat = base.toNat ^ 415682586050 % modulus.toNat :=
    mulMod_power base modulus x50 x50 207841293025 207841293025 415682586050 (by decide) hm h50 h50
  let x52 := UInt256.mulMod x51 x51 modulus
  have h52 : x52.toNat % modulus.toNat = base.toNat ^ 831365172100 % modulus.toNat :=
    mulMod_power base modulus x51 x51 415682586050 415682586050 831365172100 (by decide) hm h51 h51
  let x53 := UInt256.mulMod x52 x52 modulus
  have h53 : x53.toNat % modulus.toNat = base.toNat ^ 1662730344200 % modulus.toNat :=
    mulMod_power base modulus x52 x52 831365172100 831365172100 1662730344200 (by decide) hm h52 h52
  let x54 := UInt256.mulMod x53 x53 modulus
  have h54 : x54.toNat % modulus.toNat = base.toNat ^ 3325460688400 % modulus.toNat :=
    mulMod_power base modulus x53 x53 1662730344200 1662730344200 3325460688400 (by decide) hm h53 h53
  let x55 := UInt256.mulMod x2 x54 modulus
  have h55 : x55.toNat % modulus.toNat = base.toNat ^ 3325460688403 % modulus.toNat :=
    mulMod_power base modulus x2 x54 3 3325460688400 3325460688403 (by decide) hm h2 h54
  let x56 := UInt256.mulMod x55 x55 modulus
  have h56 : x56.toNat % modulus.toNat = base.toNat ^ 6650921376806 % modulus.toNat :=
    mulMod_power base modulus x55 x55 3325460688403 3325460688403 6650921376806 (by decide) hm h55 h55
  let x57 := UInt256.mulMod x56 x56 modulus
  have h57 : x57.toNat % modulus.toNat = base.toNat ^ 13301842753612 % modulus.toNat :=
    mulMod_power base modulus x56 x56 6650921376806 6650921376806 13301842753612 (by decide) hm h56 h56
  let x58 := UInt256.mulMod x57 x57 modulus
  have h58 : x58.toNat % modulus.toNat = base.toNat ^ 26603685507224 % modulus.toNat :=
    mulMod_power base modulus x57 x57 13301842753612 13301842753612 26603685507224 (by decide) hm h57 h57
  let x59 := UInt256.mulMod x58 x58 modulus
  have h59 : x59.toNat % modulus.toNat = base.toNat ^ 53207371014448 % modulus.toNat :=
    mulMod_power base modulus x58 x58 26603685507224 26603685507224 53207371014448 (by decide) hm h58 h58
  let x60 := UInt256.mulMod x59 x59 modulus
  have h60 : x60.toNat % modulus.toNat = base.toNat ^ 106414742028896 % modulus.toNat :=
    mulMod_power base modulus x59 x59 53207371014448 53207371014448 106414742028896 (by decide) hm h59 h59
  let x61 := UInt256.mulMod x60 x60 modulus
  have h61 : x61.toNat % modulus.toNat = base.toNat ^ 212829484057792 % modulus.toNat :=
    mulMod_power base modulus x60 x60 106414742028896 106414742028896 212829484057792 (by decide) hm h60 h60
  let x62 := UInt256.mulMod x61 x61 modulus
  have h62 : x62.toNat % modulus.toNat = base.toNat ^ 425658968115584 % modulus.toNat :=
    mulMod_power base modulus x61 x61 212829484057792 212829484057792 425658968115584 (by decide) hm h61 h61
  let x63 := UInt256.mulMod x7 x62 modulus
  have h63 : x63.toNat % modulus.toNat = base.toNat ^ 425658968115597 % modulus.toNat :=
    mulMod_power base modulus x7 x62 13 425658968115584 425658968115597 (by decide) hm h7 h62
  let x64 := UInt256.mulMod x63 x63 modulus
  have h64 : x64.toNat % modulus.toNat = base.toNat ^ 851317936231194 % modulus.toNat :=
    mulMod_power base modulus x63 x63 425658968115597 425658968115597 851317936231194 (by decide) hm h63 h63
  let x65 := UInt256.mulMod x64 x64 modulus
  have h65 : x65.toNat % modulus.toNat = base.toNat ^ 1702635872462388 % modulus.toNat :=
    mulMod_power base modulus x64 x64 851317936231194 851317936231194 1702635872462388 (by decide) hm h64 h64
  let x66 := UInt256.mulMod x65 x65 modulus
  have h66 : x66.toNat % modulus.toNat = base.toNat ^ 3405271744924776 % modulus.toNat :=
    mulMod_power base modulus x65 x65 1702635872462388 1702635872462388 3405271744924776 (by decide) hm h65 h65
  let x67 := UInt256.mulMod x66 x66 modulus
  have h67 : x67.toNat % modulus.toNat = base.toNat ^ 6810543489849552 % modulus.toNat :=
    mulMod_power base modulus x66 x66 3405271744924776 3405271744924776 6810543489849552 (by decide) hm h66 h66
  let x68 := UInt256.mulMod x67 x67 modulus
  have h68 : x68.toNat % modulus.toNat = base.toNat ^ 13621086979699104 % modulus.toNat :=
    mulMod_power base modulus x67 x67 6810543489849552 6810543489849552 13621086979699104 (by decide) hm h67 h67
  let x69 := UInt256.mulMod x68 x68 modulus
  have h69 : x69.toNat % modulus.toNat = base.toNat ^ 27242173959398208 % modulus.toNat :=
    mulMod_power base modulus x68 x68 13621086979699104 13621086979699104 27242173959398208 (by decide) hm h68 h68
  let x70 := UInt256.mulMod x69 x69 modulus
  have h70 : x70.toNat % modulus.toNat = base.toNat ^ 54484347918796416 % modulus.toNat :=
    mulMod_power base modulus x69 x69 27242173959398208 27242173959398208 54484347918796416 (by decide) hm h69 h69
  let x71 := UInt256.mulMod x70 x70 modulus
  have h71 : x71.toNat % modulus.toNat = base.toNat ^ 108968695837592832 % modulus.toNat :=
    mulMod_power base modulus x70 x70 54484347918796416 54484347918796416 108968695837592832 (by decide) hm h70 h70
  let x72 := UInt256.mulMod x71 x71 modulus
  have h72 : x72.toNat % modulus.toNat = base.toNat ^ 217937391675185664 % modulus.toNat :=
    mulMod_power base modulus x71 x71 108968695837592832 108968695837592832 217937391675185664 (by decide) hm h71 h71
  let x73 := UInt256.mulMod x72 x72 modulus
  have h73 : x73.toNat % modulus.toNat = base.toNat ^ 435874783350371328 % modulus.toNat :=
    mulMod_power base modulus x72 x72 217937391675185664 217937391675185664 435874783350371328 (by decide) hm h72 h72
  let x74 := UInt256.mulMod x3 x73 modulus
  have h74 : x74.toNat % modulus.toNat = base.toNat ^ 435874783350371333 % modulus.toNat :=
    mulMod_power base modulus x3 x73 5 435874783350371328 435874783350371333 (by decide) hm h3 h73
  let x75 := UInt256.mulMod x74 x74 modulus
  have h75 : x75.toNat % modulus.toNat = base.toNat ^ 871749566700742666 % modulus.toNat :=
    mulMod_power base modulus x74 x74 435874783350371333 435874783350371333 871749566700742666 (by decide) hm h74 h74
  let x76 := UInt256.mulMod x75 x75 modulus
  have h76 : x76.toNat % modulus.toNat = base.toNat ^ 1743499133401485332 % modulus.toNat :=
    mulMod_power base modulus x75 x75 871749566700742666 871749566700742666 1743499133401485332 (by decide) hm h75 h75
  let x77 := UInt256.mulMod x76 x76 modulus
  have h77 : x77.toNat % modulus.toNat = base.toNat ^ 3486998266802970664 % modulus.toNat :=
    mulMod_power base modulus x76 x76 1743499133401485332 1743499133401485332 3486998266802970664 (by decide) hm h76 h76
  let x78 := UInt256.mulMod x77 x77 modulus
  have h78 : x78.toNat % modulus.toNat = base.toNat ^ 6973996533605941328 % modulus.toNat :=
    mulMod_power base modulus x77 x77 3486998266802970664 3486998266802970664 6973996533605941328 (by decide) hm h77 h77
  let x79 := UInt256.mulMod x2 x78 modulus
  have h79 : x79.toNat % modulus.toNat = base.toNat ^ 6973996533605941331 % modulus.toNat :=
    mulMod_power base modulus x2 x78 3 6973996533605941328 6973996533605941331 (by decide) hm h2 h78
  let x80 := UInt256.mulMod x79 x79 modulus
  have h80 : x80.toNat % modulus.toNat = base.toNat ^ 13947993067211882662 % modulus.toNat :=
    mulMod_power base modulus x79 x79 6973996533605941331 6973996533605941331 13947993067211882662 (by decide) hm h79 h79
  let x81 := UInt256.mulMod x80 x80 modulus
  have h81 : x81.toNat % modulus.toNat = base.toNat ^ 27895986134423765324 % modulus.toNat :=
    mulMod_power base modulus x80 x80 13947993067211882662 13947993067211882662 27895986134423765324 (by decide) hm h80 h80
  let x82 := UInt256.mulMod x81 x81 modulus
  have h82 : x82.toNat % modulus.toNat = base.toNat ^ 55791972268847530648 % modulus.toNat :=
    mulMod_power base modulus x81 x81 27895986134423765324 27895986134423765324 55791972268847530648 (by decide) hm h81 h81
  let x83 := UInt256.mulMod x82 x82 modulus
  have h83 : x83.toNat % modulus.toNat = base.toNat ^ 111583944537695061296 % modulus.toNat :=
    mulMod_power base modulus x82 x82 55791972268847530648 55791972268847530648 111583944537695061296 (by decide) hm h82 h82
  let x84 := UInt256.mulMod x4 x83 modulus
  have h84 : x84.toNat % modulus.toNat = base.toNat ^ 111583944537695061303 % modulus.toNat :=
    mulMod_power base modulus x4 x83 7 111583944537695061296 111583944537695061303 (by decide) hm h4 h83
  let x85 := UInt256.mulMod x84 x84 modulus
  have h85 : x85.toNat % modulus.toNat = base.toNat ^ 223167889075390122606 % modulus.toNat :=
    mulMod_power base modulus x84 x84 111583944537695061303 111583944537695061303 223167889075390122606 (by decide) hm h84 h84
  let x86 := UInt256.mulMod x85 x85 modulus
  have h86 : x86.toNat % modulus.toNat = base.toNat ^ 446335778150780245212 % modulus.toNat :=
    mulMod_power base modulus x85 x85 223167889075390122606 223167889075390122606 446335778150780245212 (by decide) hm h85 h85
  let x87 := UInt256.mulMod x86 x86 modulus
  have h87 : x87.toNat % modulus.toNat = base.toNat ^ 892671556301560490424 % modulus.toNat :=
    mulMod_power base modulus x86 x86 446335778150780245212 446335778150780245212 892671556301560490424 (by decide) hm h86 h86
  let x88 := UInt256.mulMod x87 x87 modulus
  have h88 : x88.toNat % modulus.toNat = base.toNat ^ 1785343112603120980848 % modulus.toNat :=
    mulMod_power base modulus x87 x87 892671556301560490424 892671556301560490424 1785343112603120980848 (by decide) hm h87 h87
  let x89 := UInt256.mulMod x88 x88 modulus
  have h89 : x89.toNat % modulus.toNat = base.toNat ^ 3570686225206241961696 % modulus.toNat :=
    mulMod_power base modulus x88 x88 1785343112603120980848 1785343112603120980848 3570686225206241961696 (by decide) hm h88 h88
  let x90 := UInt256.mulMod x89 x89 modulus
  have h90 : x90.toNat % modulus.toNat = base.toNat ^ 7141372450412483923392 % modulus.toNat :=
    mulMod_power base modulus x89 x89 3570686225206241961696 3570686225206241961696 7141372450412483923392 (by decide) hm h89 h89
  let x91 := UInt256.mulMod x90 x90 modulus
  have h91 : x91.toNat % modulus.toNat = base.toNat ^ 14282744900824967846784 % modulus.toNat :=
    mulMod_power base modulus x90 x90 7141372450412483923392 7141372450412483923392 14282744900824967846784 (by decide) hm h90 h90
  let x92 := UInt256.mulMod x3 x91 modulus
  have h92 : x92.toNat % modulus.toNat = base.toNat ^ 14282744900824967846789 % modulus.toNat :=
    mulMod_power base modulus x3 x91 5 14282744900824967846784 14282744900824967846789 (by decide) hm h3 h91
  let x93 := UInt256.mulMod x92 x92 modulus
  have h93 : x93.toNat % modulus.toNat = base.toNat ^ 28565489801649935693578 % modulus.toNat :=
    mulMod_power base modulus x92 x92 14282744900824967846789 14282744900824967846789 28565489801649935693578 (by decide) hm h92 h92
  let x94 := UInt256.mulMod x93 x93 modulus
  have h94 : x94.toNat % modulus.toNat = base.toNat ^ 57130979603299871387156 % modulus.toNat :=
    mulMod_power base modulus x93 x93 28565489801649935693578 28565489801649935693578 57130979603299871387156 (by decide) hm h93 h93
  let x95 := UInt256.mulMod x94 x94 modulus
  have h95 : x95.toNat % modulus.toNat = base.toNat ^ 114261959206599742774312 % modulus.toNat :=
    mulMod_power base modulus x94 x94 57130979603299871387156 57130979603299871387156 114261959206599742774312 (by decide) hm h94 h94
  let x96 := UInt256.mulMod x95 x95 modulus
  have h96 : x96.toNat % modulus.toNat = base.toNat ^ 228523918413199485548624 % modulus.toNat :=
    mulMod_power base modulus x95 x95 114261959206599742774312 114261959206599742774312 228523918413199485548624 (by decide) hm h95 h95
  let x97 := UInt256.mulMod x96 x96 modulus
  have h97 : x97.toNat % modulus.toNat = base.toNat ^ 457047836826398971097248 % modulus.toNat :=
    mulMod_power base modulus x96 x96 228523918413199485548624 228523918413199485548624 457047836826398971097248 (by decide) hm h96 h96
  let x98 := UInt256.mulMod x97 x97 modulus
  have h98 : x98.toNat % modulus.toNat = base.toNat ^ 914095673652797942194496 % modulus.toNat :=
    mulMod_power base modulus x97 x97 457047836826398971097248 457047836826398971097248 914095673652797942194496 (by decide) hm h97 h97
  let x99 := UInt256.mulMod x0 x98 modulus
  have h99 : x99.toNat % modulus.toNat = base.toNat ^ 914095673652797942194497 % modulus.toNat :=
    mulMod_power base modulus x0 x98 1 914095673652797942194496 914095673652797942194497 (by decide) hm h0 h98
  let x100 := UInt256.mulMod x99 x99 modulus
  have h100 : x100.toNat % modulus.toNat = base.toNat ^ 1828191347305595884388994 % modulus.toNat :=
    mulMod_power base modulus x99 x99 914095673652797942194497 914095673652797942194497 1828191347305595884388994 (by decide) hm h99 h99
  let x101 := UInt256.mulMod x100 x100 modulus
  have h101 : x101.toNat % modulus.toNat = base.toNat ^ 3656382694611191768777988 % modulus.toNat :=
    mulMod_power base modulus x100 x100 1828191347305595884388994 1828191347305595884388994 3656382694611191768777988 (by decide) hm h100 h100
  let x102 := UInt256.mulMod x101 x101 modulus
  have h102 : x102.toNat % modulus.toNat = base.toNat ^ 7312765389222383537555976 % modulus.toNat :=
    mulMod_power base modulus x101 x101 3656382694611191768777988 3656382694611191768777988 7312765389222383537555976 (by decide) hm h101 h101
  let x103 := UInt256.mulMod x102 x102 modulus
  have h103 : x103.toNat % modulus.toNat = base.toNat ^ 14625530778444767075111952 % modulus.toNat :=
    mulMod_power base modulus x102 x102 7312765389222383537555976 7312765389222383537555976 14625530778444767075111952 (by decide) hm h102 h102
  let x104 := UInt256.mulMod x103 x103 modulus
  have h104 : x104.toNat % modulus.toNat = base.toNat ^ 29251061556889534150223904 % modulus.toNat :=
    mulMod_power base modulus x103 x103 14625530778444767075111952 14625530778444767075111952 29251061556889534150223904 (by decide) hm h103 h103
  let x105 := UInt256.mulMod x104 x104 modulus
  have h105 : x105.toNat % modulus.toNat = base.toNat ^ 58502123113779068300447808 % modulus.toNat :=
    mulMod_power base modulus x104 x104 29251061556889534150223904 29251061556889534150223904 58502123113779068300447808 (by decide) hm h104 h104
  let x106 := UInt256.mulMod x3 x105 modulus
  have h106 : x106.toNat % modulus.toNat = base.toNat ^ 58502123113779068300447813 % modulus.toNat :=
    mulMod_power base modulus x3 x105 5 58502123113779068300447808 58502123113779068300447813 (by decide) hm h3 h105
  let x107 := UInt256.mulMod x106 x106 modulus
  have h107 : x107.toNat % modulus.toNat = base.toNat ^ 117004246227558136600895626 % modulus.toNat :=
    mulMod_power base modulus x106 x106 58502123113779068300447813 58502123113779068300447813 117004246227558136600895626 (by decide) hm h106 h106
  let x108 := UInt256.mulMod x107 x107 modulus
  have h108 : x108.toNat % modulus.toNat = base.toNat ^ 234008492455116273201791252 % modulus.toNat :=
    mulMod_power base modulus x107 x107 117004246227558136600895626 117004246227558136600895626 234008492455116273201791252 (by decide) hm h107 h107
  let x109 := UInt256.mulMod x108 x108 modulus
  have h109 : x109.toNat % modulus.toNat = base.toNat ^ 468016984910232546403582504 % modulus.toNat :=
    mulMod_power base modulus x108 x108 234008492455116273201791252 234008492455116273201791252 468016984910232546403582504 (by decide) hm h108 h108
  let x110 := UInt256.mulMod x109 x109 modulus
  have h110 : x110.toNat % modulus.toNat = base.toNat ^ 936033969820465092807165008 % modulus.toNat :=
    mulMod_power base modulus x109 x109 468016984910232546403582504 468016984910232546403582504 936033969820465092807165008 (by decide) hm h109 h109
  let x111 := UInt256.mulMod x6 x110 modulus
  have h111 : x111.toNat % modulus.toNat = base.toNat ^ 936033969820465092807165019 % modulus.toNat :=
    mulMod_power base modulus x6 x110 11 936033969820465092807165008 936033969820465092807165019 (by decide) hm h6 h110
  let x112 := UInt256.mulMod x111 x111 modulus
  have h112 : x112.toNat % modulus.toNat = base.toNat ^ 1872067939640930185614330038 % modulus.toNat :=
    mulMod_power base modulus x111 x111 936033969820465092807165019 936033969820465092807165019 1872067939640930185614330038 (by decide) hm h111 h111
  let x113 := UInt256.mulMod x112 x112 modulus
  have h113 : x113.toNat % modulus.toNat = base.toNat ^ 3744135879281860371228660076 % modulus.toNat :=
    mulMod_power base modulus x112 x112 1872067939640930185614330038 1872067939640930185614330038 3744135879281860371228660076 (by decide) hm h112 h112
  let x114 := UInt256.mulMod x113 x113 modulus
  have h114 : x114.toNat % modulus.toNat = base.toNat ^ 7488271758563720742457320152 % modulus.toNat :=
    mulMod_power base modulus x113 x113 3744135879281860371228660076 3744135879281860371228660076 7488271758563720742457320152 (by decide) hm h113 h113
  let x115 := UInt256.mulMod x114 x114 modulus
  have h115 : x115.toNat % modulus.toNat = base.toNat ^ 14976543517127441484914640304 % modulus.toNat :=
    mulMod_power base modulus x114 x114 7488271758563720742457320152 7488271758563720742457320152 14976543517127441484914640304 (by decide) hm h114 h114
  let x116 := UInt256.mulMod x115 x115 modulus
  have h116 : x116.toNat % modulus.toNat = base.toNat ^ 29953087034254882969829280608 % modulus.toNat :=
    mulMod_power base modulus x115 x115 14976543517127441484914640304 14976543517127441484914640304 29953087034254882969829280608 (by decide) hm h115 h115
  let x117 := UInt256.mulMod x7 x116 modulus
  have h117 : x117.toNat % modulus.toNat = base.toNat ^ 29953087034254882969829280621 % modulus.toNat :=
    mulMod_power base modulus x7 x116 13 29953087034254882969829280608 29953087034254882969829280621 (by decide) hm h7 h116
  let x118 := UInt256.mulMod x117 x117 modulus
  have h118 : x118.toNat % modulus.toNat = base.toNat ^ 59906174068509765939658561242 % modulus.toNat :=
    mulMod_power base modulus x117 x117 29953087034254882969829280621 29953087034254882969829280621 59906174068509765939658561242 (by decide) hm h117 h117
  let x119 := UInt256.mulMod x118 x118 modulus
  have h119 : x119.toNat % modulus.toNat = base.toNat ^ 119812348137019531879317122484 % modulus.toNat :=
    mulMod_power base modulus x118 x118 59906174068509765939658561242 59906174068509765939658561242 119812348137019531879317122484 (by decide) hm h118 h118
  let x120 := UInt256.mulMod x119 x119 modulus
  have h120 : x120.toNat % modulus.toNat = base.toNat ^ 239624696274039063758634244968 % modulus.toNat :=
    mulMod_power base modulus x119 x119 119812348137019531879317122484 119812348137019531879317122484 239624696274039063758634244968 (by decide) hm h119 h119
  let x121 := UInt256.mulMod x120 x120 modulus
  have h121 : x121.toNat % modulus.toNat = base.toNat ^ 479249392548078127517268489936 % modulus.toNat :=
    mulMod_power base modulus x120 x120 239624696274039063758634244968 239624696274039063758634244968 479249392548078127517268489936 (by decide) hm h120 h120
  let x122 := UInt256.mulMod x121 x121 modulus
  have h122 : x122.toNat % modulus.toNat = base.toNat ^ 958498785096156255034536979872 % modulus.toNat :=
    mulMod_power base modulus x121 x121 479249392548078127517268489936 479249392548078127517268489936 958498785096156255034536979872 (by decide) hm h121 h121
  let x123 := UInt256.mulMod x122 x122 modulus
  have h123 : x123.toNat % modulus.toNat = base.toNat ^ 1916997570192312510069073959744 % modulus.toNat :=
    mulMod_power base modulus x122 x122 958498785096156255034536979872 958498785096156255034536979872 1916997570192312510069073959744 (by decide) hm h122 h122
  let x124 := UInt256.mulMod x123 x123 modulus
  have h124 : x124.toNat % modulus.toNat = base.toNat ^ 3833995140384625020138147919488 % modulus.toNat :=
    mulMod_power base modulus x123 x123 1916997570192312510069073959744 1916997570192312510069073959744 3833995140384625020138147919488 (by decide) hm h123 h123
  let x125 := UInt256.mulMod x124 x124 modulus
  have h125 : x125.toNat % modulus.toNat = base.toNat ^ 7667990280769250040276295838976 % modulus.toNat :=
    mulMod_power base modulus x124 x124 3833995140384625020138147919488 3833995140384625020138147919488 7667990280769250040276295838976 (by decide) hm h124 h124
  let x126 := UInt256.mulMod x2 x125 modulus
  have h126 : x126.toNat % modulus.toNat = base.toNat ^ 7667990280769250040276295838979 % modulus.toNat :=
    mulMod_power base modulus x2 x125 3 7667990280769250040276295838976 7667990280769250040276295838979 (by decide) hm h2 h125
  let x127 := UInt256.mulMod x126 x126 modulus
  have h127 : x127.toNat % modulus.toNat = base.toNat ^ 15335980561538500080552591677958 % modulus.toNat :=
    mulMod_power base modulus x126 x126 7667990280769250040276295838979 7667990280769250040276295838979 15335980561538500080552591677958 (by decide) hm h126 h126
  let x128 := UInt256.mulMod x127 x127 modulus
  have h128 : x128.toNat % modulus.toNat = base.toNat ^ 30671961123077000161105183355916 % modulus.toNat :=
    mulMod_power base modulus x127 x127 15335980561538500080552591677958 15335980561538500080552591677958 30671961123077000161105183355916 (by decide) hm h127 h127
  let x129 := UInt256.mulMod x128 x128 modulus
  have h129 : x129.toNat % modulus.toNat = base.toNat ^ 61343922246154000322210366711832 % modulus.toNat :=
    mulMod_power base modulus x128 x128 30671961123077000161105183355916 30671961123077000161105183355916 61343922246154000322210366711832 (by decide) hm h128 h128
  let x130 := UInt256.mulMod x129 x129 modulus
  have h130 : x130.toNat % modulus.toNat = base.toNat ^ 122687844492308000644420733423664 % modulus.toNat :=
    mulMod_power base modulus x129 x129 61343922246154000322210366711832 61343922246154000322210366711832 122687844492308000644420733423664 (by decide) hm h129 h129
  let x131 := UInt256.mulMod x130 x130 modulus
  have h131 : x131.toNat % modulus.toNat = base.toNat ^ 245375688984616001288841466847328 % modulus.toNat :=
    mulMod_power base modulus x130 x130 122687844492308000644420733423664 122687844492308000644420733423664 245375688984616001288841466847328 (by decide) hm h130 h130
  let x132 := UInt256.mulMod x131 x131 modulus
  have h132 : x132.toNat % modulus.toNat = base.toNat ^ 490751377969232002577682933694656 % modulus.toNat :=
    mulMod_power base modulus x131 x131 245375688984616001288841466847328 245375688984616001288841466847328 490751377969232002577682933694656 (by decide) hm h131 h131
  let x133 := UInt256.mulMod x132 x132 modulus
  have h133 : x133.toNat % modulus.toNat = base.toNat ^ 981502755938464005155365867389312 % modulus.toNat :=
    mulMod_power base modulus x132 x132 490751377969232002577682933694656 490751377969232002577682933694656 981502755938464005155365867389312 (by decide) hm h132 h132
  let x134 := UInt256.mulMod x0 x133 modulus
  have h134 : x134.toNat % modulus.toNat = base.toNat ^ 981502755938464005155365867389313 % modulus.toNat :=
    mulMod_power base modulus x0 x133 1 981502755938464005155365867389312 981502755938464005155365867389313 (by decide) hm h0 h133
  let x135 := UInt256.mulMod x134 x134 modulus
  have h135 : x135.toNat % modulus.toNat = base.toNat ^ 1963005511876928010310731734778626 % modulus.toNat :=
    mulMod_power base modulus x134 x134 981502755938464005155365867389313 981502755938464005155365867389313 1963005511876928010310731734778626 (by decide) hm h134 h134
  let x136 := UInt256.mulMod x135 x135 modulus
  have h136 : x136.toNat % modulus.toNat = base.toNat ^ 3926011023753856020621463469557252 % modulus.toNat :=
    mulMod_power base modulus x135 x135 1963005511876928010310731734778626 1963005511876928010310731734778626 3926011023753856020621463469557252 (by decide) hm h135 h135
  let x137 := UInt256.mulMod x136 x136 modulus
  have h137 : x137.toNat % modulus.toNat = base.toNat ^ 7852022047507712041242926939114504 % modulus.toNat :=
    mulMod_power base modulus x136 x136 3926011023753856020621463469557252 3926011023753856020621463469557252 7852022047507712041242926939114504 (by decide) hm h136 h136
  let x138 := UInt256.mulMod x137 x137 modulus
  have h138 : x138.toNat % modulus.toNat = base.toNat ^ 15704044095015424082485853878229008 % modulus.toNat :=
    mulMod_power base modulus x137 x137 7852022047507712041242926939114504 7852022047507712041242926939114504 15704044095015424082485853878229008 (by decide) hm h137 h137
  let x139 := UInt256.mulMod x138 x138 modulus
  have h139 : x139.toNat % modulus.toNat = base.toNat ^ 31408088190030848164971707756458016 % modulus.toNat :=
    mulMod_power base modulus x138 x138 15704044095015424082485853878229008 15704044095015424082485853878229008 31408088190030848164971707756458016 (by decide) hm h138 h138
  let x140 := UInt256.mulMod x6 x139 modulus
  have h140 : x140.toNat % modulus.toNat = base.toNat ^ 31408088190030848164971707756458027 % modulus.toNat :=
    mulMod_power base modulus x6 x139 11 31408088190030848164971707756458016 31408088190030848164971707756458027 (by decide) hm h6 h139
  let x141 := UInt256.mulMod x140 x140 modulus
  have h141 : x141.toNat % modulus.toNat = base.toNat ^ 62816176380061696329943415512916054 % modulus.toNat :=
    mulMod_power base modulus x140 x140 31408088190030848164971707756458027 31408088190030848164971707756458027 62816176380061696329943415512916054 (by decide) hm h140 h140
  let x142 := UInt256.mulMod x141 x141 modulus
  have h142 : x142.toNat % modulus.toNat = base.toNat ^ 125632352760123392659886831025832108 % modulus.toNat :=
    mulMod_power base modulus x141 x141 62816176380061696329943415512916054 62816176380061696329943415512916054 125632352760123392659886831025832108 (by decide) hm h141 h141
  let x143 := UInt256.mulMod x142 x142 modulus
  have h143 : x143.toNat % modulus.toNat = base.toNat ^ 251264705520246785319773662051664216 % modulus.toNat :=
    mulMod_power base modulus x142 x142 125632352760123392659886831025832108 125632352760123392659886831025832108 251264705520246785319773662051664216 (by decide) hm h142 h142
  let x144 := UInt256.mulMod x143 x143 modulus
  have h144 : x144.toNat % modulus.toNat = base.toNat ^ 502529411040493570639547324103328432 % modulus.toNat :=
    mulMod_power base modulus x143 x143 251264705520246785319773662051664216 251264705520246785319773662051664216 502529411040493570639547324103328432 (by decide) hm h143 h143
  let x145 := UInt256.mulMod x144 x144 modulus
  have h145 : x145.toNat % modulus.toNat = base.toNat ^ 1005058822080987141279094648206656864 % modulus.toNat :=
    mulMod_power base modulus x144 x144 502529411040493570639547324103328432 502529411040493570639547324103328432 1005058822080987141279094648206656864 (by decide) hm h144 h144
  let x146 := UInt256.mulMod x145 x145 modulus
  have h146 : x146.toNat % modulus.toNat = base.toNat ^ 2010117644161974282558189296413313728 % modulus.toNat :=
    mulMod_power base modulus x145 x145 1005058822080987141279094648206656864 1005058822080987141279094648206656864 2010117644161974282558189296413313728 (by decide) hm h145 h145
  let x147 := UInt256.mulMod x146 x146 modulus
  have h147 : x147.toNat % modulus.toNat = base.toNat ^ 4020235288323948565116378592826627456 % modulus.toNat :=
    mulMod_power base modulus x146 x146 2010117644161974282558189296413313728 2010117644161974282558189296413313728 4020235288323948565116378592826627456 (by decide) hm h146 h146
  let x148 := UInt256.mulMod x147 x147 modulus
  have h148 : x148.toNat % modulus.toNat = base.toNat ^ 8040470576647897130232757185653254912 % modulus.toNat :=
    mulMod_power base modulus x147 x147 4020235288323948565116378592826627456 4020235288323948565116378592826627456 8040470576647897130232757185653254912 (by decide) hm h147 h147
  let x149 := UInt256.mulMod x6 x148 modulus
  have h149 : x149.toNat % modulus.toNat = base.toNat ^ 8040470576647897130232757185653254923 % modulus.toNat :=
    mulMod_power base modulus x6 x148 11 8040470576647897130232757185653254912 8040470576647897130232757185653254923 (by decide) hm h6 h148
  let x150 := UInt256.mulMod x149 x149 modulus
  have h150 : x150.toNat % modulus.toNat = base.toNat ^ 16080941153295794260465514371306509846 % modulus.toNat :=
    mulMod_power base modulus x149 x149 8040470576647897130232757185653254923 8040470576647897130232757185653254923 16080941153295794260465514371306509846 (by decide) hm h149 h149
  let x151 := UInt256.mulMod x150 x150 modulus
  have h151 : x151.toNat % modulus.toNat = base.toNat ^ 32161882306591588520931028742613019692 % modulus.toNat :=
    mulMod_power base modulus x150 x150 16080941153295794260465514371306509846 16080941153295794260465514371306509846 32161882306591588520931028742613019692 (by decide) hm h150 h150
  let x152 := UInt256.mulMod x151 x151 modulus
  have h152 : x152.toNat % modulus.toNat = base.toNat ^ 64323764613183177041862057485226039384 % modulus.toNat :=
    mulMod_power base modulus x151 x151 32161882306591588520931028742613019692 32161882306591588520931028742613019692 64323764613183177041862057485226039384 (by decide) hm h151 h151
  let x153 := UInt256.mulMod x152 x152 modulus
  have h153 : x153.toNat % modulus.toNat = base.toNat ^ 128647529226366354083724114970452078768 % modulus.toNat :=
    mulMod_power base modulus x152 x152 64323764613183177041862057485226039384 64323764613183177041862057485226039384 128647529226366354083724114970452078768 (by decide) hm h152 h152
  let x154 := UInt256.mulMod x6 x153 modulus
  have h154 : x154.toNat % modulus.toNat = base.toNat ^ 128647529226366354083724114970452078779 % modulus.toNat :=
    mulMod_power base modulus x6 x153 11 128647529226366354083724114970452078768 128647529226366354083724114970452078779 (by decide) hm h6 h153
  let x155 := UInt256.mulMod x154 x154 modulus
  have h155 : x155.toNat % modulus.toNat = base.toNat ^ 257295058452732708167448229940904157558 % modulus.toNat :=
    mulMod_power base modulus x154 x154 128647529226366354083724114970452078779 128647529226366354083724114970452078779 257295058452732708167448229940904157558 (by decide) hm h154 h154
  let x156 := UInt256.mulMod x155 x155 modulus
  have h156 : x156.toNat % modulus.toNat = base.toNat ^ 514590116905465416334896459881808315116 % modulus.toNat :=
    mulMod_power base modulus x155 x155 257295058452732708167448229940904157558 257295058452732708167448229940904157558 514590116905465416334896459881808315116 (by decide) hm h155 h155
  let x157 := UInt256.mulMod x156 x156 modulus
  have h157 : x157.toNat % modulus.toNat = base.toNat ^ 1029180233810930832669792919763616630232 % modulus.toNat :=
    mulMod_power base modulus x156 x156 514590116905465416334896459881808315116 514590116905465416334896459881808315116 1029180233810930832669792919763616630232 (by decide) hm h156 h156
  let x158 := UInt256.mulMod x0 x157 modulus
  have h158 : x158.toNat % modulus.toNat = base.toNat ^ 1029180233810930832669792919763616630233 % modulus.toNat :=
    mulMod_power base modulus x0 x157 1 1029180233810930832669792919763616630232 1029180233810930832669792919763616630233 (by decide) hm h0 h157
  let x159 := UInt256.mulMod x158 x158 modulus
  have h159 : x159.toNat % modulus.toNat = base.toNat ^ 2058360467621861665339585839527233260466 % modulus.toNat :=
    mulMod_power base modulus x158 x158 1029180233810930832669792919763616630233 1029180233810930832669792919763616630233 2058360467621861665339585839527233260466 (by decide) hm h158 h158
  let x160 := UInt256.mulMod x159 x159 modulus
  have h160 : x160.toNat % modulus.toNat = base.toNat ^ 4116720935243723330679171679054466520932 % modulus.toNat :=
    mulMod_power base modulus x159 x159 2058360467621861665339585839527233260466 2058360467621861665339585839527233260466 4116720935243723330679171679054466520932 (by decide) hm h159 h159
  let x161 := UInt256.mulMod x160 x160 modulus
  have h161 : x161.toNat % modulus.toNat = base.toNat ^ 8233441870487446661358343358108933041864 % modulus.toNat :=
    mulMod_power base modulus x160 x160 4116720935243723330679171679054466520932 4116720935243723330679171679054466520932 8233441870487446661358343358108933041864 (by decide) hm h160 h160
  let x162 := UInt256.mulMod x161 x161 modulus
  have h162 : x162.toNat % modulus.toNat = base.toNat ^ 16466883740974893322716686716217866083728 % modulus.toNat :=
    mulMod_power base modulus x161 x161 8233441870487446661358343358108933041864 8233441870487446661358343358108933041864 16466883740974893322716686716217866083728 (by decide) hm h161 h161
  let x163 := UInt256.mulMod x162 x162 modulus
  have h163 : x163.toNat % modulus.toNat = base.toNat ^ 32933767481949786645433373432435732167456 % modulus.toNat :=
    mulMod_power base modulus x162 x162 16466883740974893322716686716217866083728 16466883740974893322716686716217866083728 32933767481949786645433373432435732167456 (by decide) hm h162 h162
  let x164 := UInt256.mulMod x8 x163 modulus
  have h164 : x164.toNat % modulus.toNat = base.toNat ^ 32933767481949786645433373432435732167471 % modulus.toNat :=
    mulMod_power base modulus x8 x163 15 32933767481949786645433373432435732167456 32933767481949786645433373432435732167471 (by decide) hm h8 h163
  let x165 := UInt256.mulMod x164 x164 modulus
  have h165 : x165.toNat % modulus.toNat = base.toNat ^ 65867534963899573290866746864871464334942 % modulus.toNat :=
    mulMod_power base modulus x164 x164 32933767481949786645433373432435732167471 32933767481949786645433373432435732167471 65867534963899573290866746864871464334942 (by decide) hm h164 h164
  let x166 := UInt256.mulMod x165 x165 modulus
  have h166 : x166.toNat % modulus.toNat = base.toNat ^ 131735069927799146581733493729742928669884 % modulus.toNat :=
    mulMod_power base modulus x165 x165 65867534963899573290866746864871464334942 65867534963899573290866746864871464334942 131735069927799146581733493729742928669884 (by decide) hm h165 h165
  let x167 := UInt256.mulMod x166 x166 modulus
  have h167 : x167.toNat % modulus.toNat = base.toNat ^ 263470139855598293163466987459485857339768 % modulus.toNat :=
    mulMod_power base modulus x166 x166 131735069927799146581733493729742928669884 131735069927799146581733493729742928669884 263470139855598293163466987459485857339768 (by decide) hm h166 h166
  let x168 := UInt256.mulMod x167 x167 modulus
  have h168 : x168.toNat % modulus.toNat = base.toNat ^ 526940279711196586326933974918971714679536 % modulus.toNat :=
    mulMod_power base modulus x167 x167 263470139855598293163466987459485857339768 263470139855598293163466987459485857339768 526940279711196586326933974918971714679536 (by decide) hm h167 h167
  let x169 := UInt256.mulMod x168 x168 modulus
  have h169 : x169.toNat % modulus.toNat = base.toNat ^ 1053880559422393172653867949837943429359072 % modulus.toNat :=
    mulMod_power base modulus x168 x168 526940279711196586326933974918971714679536 526940279711196586326933974918971714679536 1053880559422393172653867949837943429359072 (by decide) hm h168 h168
  let x170 := UInt256.mulMod x169 x169 modulus
  have h170 : x170.toNat % modulus.toNat = base.toNat ^ 2107761118844786345307735899675886858718144 % modulus.toNat :=
    mulMod_power base modulus x169 x169 1053880559422393172653867949837943429359072 1053880559422393172653867949837943429359072 2107761118844786345307735899675886858718144 (by decide) hm h169 h169
  let x171 := UInt256.mulMod x170 x170 modulus
  have h171 : x171.toNat % modulus.toNat = base.toNat ^ 4215522237689572690615471799351773717436288 % modulus.toNat :=
    mulMod_power base modulus x170 x170 2107761118844786345307735899675886858718144 2107761118844786345307735899675886858718144 4215522237689572690615471799351773717436288 (by decide) hm h170 h170
  let x172 := UInt256.mulMod x171 x171 modulus
  have h172 : x172.toNat % modulus.toNat = base.toNat ^ 8431044475379145381230943598703547434872576 % modulus.toNat :=
    mulMod_power base modulus x171 x171 4215522237689572690615471799351773717436288 4215522237689572690615471799351773717436288 8431044475379145381230943598703547434872576 (by decide) hm h171 h171
  let x173 := UInt256.mulMod x172 x172 modulus
  have h173 : x173.toNat % modulus.toNat = base.toNat ^ 16862088950758290762461887197407094869745152 % modulus.toNat :=
    mulMod_power base modulus x172 x172 8431044475379145381230943598703547434872576 8431044475379145381230943598703547434872576 16862088950758290762461887197407094869745152 (by decide) hm h172 h172
  let x174 := UInt256.mulMod x173 x173 modulus
  have h174 : x174.toNat % modulus.toNat = base.toNat ^ 33724177901516581524923774394814189739490304 % modulus.toNat :=
    mulMod_power base modulus x173 x173 16862088950758290762461887197407094869745152 16862088950758290762461887197407094869745152 33724177901516581524923774394814189739490304 (by decide) hm h173 h173
  let x175 := UInt256.mulMod x6 x174 modulus
  have h175 : x175.toNat % modulus.toNat = base.toNat ^ 33724177901516581524923774394814189739490315 % modulus.toNat :=
    mulMod_power base modulus x6 x174 11 33724177901516581524923774394814189739490304 33724177901516581524923774394814189739490315 (by decide) hm h6 h174
  let x176 := UInt256.mulMod x175 x175 modulus
  have h176 : x176.toNat % modulus.toNat = base.toNat ^ 67448355803033163049847548789628379478980630 % modulus.toNat :=
    mulMod_power base modulus x175 x175 33724177901516581524923774394814189739490315 33724177901516581524923774394814189739490315 67448355803033163049847548789628379478980630 (by decide) hm h175 h175
  let x177 := UInt256.mulMod x176 x176 modulus
  have h177 : x177.toNat % modulus.toNat = base.toNat ^ 134896711606066326099695097579256758957961260 % modulus.toNat :=
    mulMod_power base modulus x176 x176 67448355803033163049847548789628379478980630 67448355803033163049847548789628379478980630 134896711606066326099695097579256758957961260 (by decide) hm h176 h176
  let x178 := UInt256.mulMod x177 x177 modulus
  have h178 : x178.toNat % modulus.toNat = base.toNat ^ 269793423212132652199390195158513517915922520 % modulus.toNat :=
    mulMod_power base modulus x177 x177 134896711606066326099695097579256758957961260 134896711606066326099695097579256758957961260 269793423212132652199390195158513517915922520 (by decide) hm h177 h177
  let x179 := UInt256.mulMod x178 x178 modulus
  have h179 : x179.toNat % modulus.toNat = base.toNat ^ 539586846424265304398780390317027035831845040 % modulus.toNat :=
    mulMod_power base modulus x178 x178 269793423212132652199390195158513517915922520 269793423212132652199390195158513517915922520 539586846424265304398780390317027035831845040 (by decide) hm h178 h178
  let x180 := UInt256.mulMod x3 x179 modulus
  have h180 : x180.toNat % modulus.toNat = base.toNat ^ 539586846424265304398780390317027035831845045 % modulus.toNat :=
    mulMod_power base modulus x3 x179 5 539586846424265304398780390317027035831845040 539586846424265304398780390317027035831845045 (by decide) hm h3 h179
  let x181 := UInt256.mulMod x180 x180 modulus
  have h181 : x181.toNat % modulus.toNat = base.toNat ^ 1079173692848530608797560780634054071663690090 % modulus.toNat :=
    mulMod_power base modulus x180 x180 539586846424265304398780390317027035831845045 539586846424265304398780390317027035831845045 1079173692848530608797560780634054071663690090 (by decide) hm h180 h180
  let x182 := UInt256.mulMod x181 x181 modulus
  have h182 : x182.toNat % modulus.toNat = base.toNat ^ 2158347385697061217595121561268108143327380180 % modulus.toNat :=
    mulMod_power base modulus x181 x181 1079173692848530608797560780634054071663690090 1079173692848530608797560780634054071663690090 2158347385697061217595121561268108143327380180 (by decide) hm h181 h181
  let x183 := UInt256.mulMod x182 x182 modulus
  have h183 : x183.toNat % modulus.toNat = base.toNat ^ 4316694771394122435190243122536216286654760360 % modulus.toNat :=
    mulMod_power base modulus x182 x182 2158347385697061217595121561268108143327380180 2158347385697061217595121561268108143327380180 4316694771394122435190243122536216286654760360 (by decide) hm h182 h182
  let x184 := UInt256.mulMod x183 x183 modulus
  have h184 : x184.toNat % modulus.toNat = base.toNat ^ 8633389542788244870380486245072432573309520720 % modulus.toNat :=
    mulMod_power base modulus x183 x183 4316694771394122435190243122536216286654760360 4316694771394122435190243122536216286654760360 8633389542788244870380486245072432573309520720 (by decide) hm h183 h183
  let x185 := UInt256.mulMod x184 x184 modulus
  have h185 : x185.toNat % modulus.toNat = base.toNat ^ 17266779085576489740760972490144865146619041440 % modulus.toNat :=
    mulMod_power base modulus x184 x184 8633389542788244870380486245072432573309520720 8633389542788244870380486245072432573309520720 17266779085576489740760972490144865146619041440 (by decide) hm h184 h184
  let x186 := UInt256.mulMod x5 x185 modulus
  have h186 : x186.toNat % modulus.toNat = base.toNat ^ 17266779085576489740760972490144865146619041449 % modulus.toNat :=
    mulMod_power base modulus x5 x185 9 17266779085576489740760972490144865146619041440 17266779085576489740760972490144865146619041449 (by decide) hm h5 h185
  let x187 := UInt256.mulMod x186 x186 modulus
  have h187 : x187.toNat % modulus.toNat = base.toNat ^ 34533558171152979481521944980289730293238082898 % modulus.toNat :=
    mulMod_power base modulus x186 x186 17266779085576489740760972490144865146619041449 17266779085576489740760972490144865146619041449 34533558171152979481521944980289730293238082898 (by decide) hm h186 h186
  let x188 := UInt256.mulMod x187 x187 modulus
  have h188 : x188.toNat % modulus.toNat = base.toNat ^ 69067116342305958963043889960579460586476165796 % modulus.toNat :=
    mulMod_power base modulus x187 x187 34533558171152979481521944980289730293238082898 34533558171152979481521944980289730293238082898 69067116342305958963043889960579460586476165796 (by decide) hm h187 h187
  let x189 := UInt256.mulMod x188 x188 modulus
  have h189 : x189.toNat % modulus.toNat = base.toNat ^ 138134232684611917926087779921158921172952331592 % modulus.toNat :=
    mulMod_power base modulus x188 x188 69067116342305958963043889960579460586476165796 69067116342305958963043889960579460586476165796 138134232684611917926087779921158921172952331592 (by decide) hm h188 h188
  let x190 := UInt256.mulMod x189 x189 modulus
  have h190 : x190.toNat % modulus.toNat = base.toNat ^ 276268465369223835852175559842317842345904663184 % modulus.toNat :=
    mulMod_power base modulus x189 x189 138134232684611917926087779921158921172952331592 138134232684611917926087779921158921172952331592 276268465369223835852175559842317842345904663184 (by decide) hm h189 h189
  let x191 := UInt256.mulMod x0 x190 modulus
  have h191 : x191.toNat % modulus.toNat = base.toNat ^ 276268465369223835852175559842317842345904663185 % modulus.toNat :=
    mulMod_power base modulus x0 x190 1 276268465369223835852175559842317842345904663184 276268465369223835852175559842317842345904663185 (by decide) hm h0 h190
  let x192 := UInt256.mulMod x191 x191 modulus
  have h192 : x192.toNat % modulus.toNat = base.toNat ^ 552536930738447671704351119684635684691809326370 % modulus.toNat :=
    mulMod_power base modulus x191 x191 276268465369223835852175559842317842345904663185 276268465369223835852175559842317842345904663185 552536930738447671704351119684635684691809326370 (by decide) hm h191 h191
  let x193 := UInt256.mulMod x192 x192 modulus
  have h193 : x193.toNat % modulus.toNat = base.toNat ^ 1105073861476895343408702239369271369383618652740 % modulus.toNat :=
    mulMod_power base modulus x192 x192 552536930738447671704351119684635684691809326370 552536930738447671704351119684635684691809326370 1105073861476895343408702239369271369383618652740 (by decide) hm h192 h192
  let x194 := UInt256.mulMod x193 x193 modulus
  have h194 : x194.toNat % modulus.toNat = base.toNat ^ 2210147722953790686817404478738542738767237305480 % modulus.toNat :=
    mulMod_power base modulus x193 x193 1105073861476895343408702239369271369383618652740 1105073861476895343408702239369271369383618652740 2210147722953790686817404478738542738767237305480 (by decide) hm h193 h193
  let x195 := UInt256.mulMod x194 x194 modulus
  have h195 : x195.toNat % modulus.toNat = base.toNat ^ 4420295445907581373634808957477085477534474610960 % modulus.toNat :=
    mulMod_power base modulus x194 x194 2210147722953790686817404478738542738767237305480 2210147722953790686817404478738542738767237305480 4420295445907581373634808957477085477534474610960 (by decide) hm h194 h194
  let x196 := UInt256.mulMod x195 x195 modulus
  have h196 : x196.toNat % modulus.toNat = base.toNat ^ 8840590891815162747269617914954170955068949221920 % modulus.toNat :=
    mulMod_power base modulus x195 x195 4420295445907581373634808957477085477534474610960 4420295445907581373634808957477085477534474610960 8840590891815162747269617914954170955068949221920 (by decide) hm h195 h195
  let x197 := UInt256.mulMod x7 x196 modulus
  have h197 : x197.toNat % modulus.toNat = base.toNat ^ 8840590891815162747269617914954170955068949221933 % modulus.toNat :=
    mulMod_power base modulus x7 x196 13 8840590891815162747269617914954170955068949221920 8840590891815162747269617914954170955068949221933 (by decide) hm h7 h196
  let x198 := UInt256.mulMod x197 x197 modulus
  have h198 : x198.toNat % modulus.toNat = base.toNat ^ 17681181783630325494539235829908341910137898443866 % modulus.toNat :=
    mulMod_power base modulus x197 x197 8840590891815162747269617914954170955068949221933 8840590891815162747269617914954170955068949221933 17681181783630325494539235829908341910137898443866 (by decide) hm h197 h197
  let x199 := UInt256.mulMod x198 x198 modulus
  have h199 : x199.toNat % modulus.toNat = base.toNat ^ 35362363567260650989078471659816683820275796887732 % modulus.toNat :=
    mulMod_power base modulus x198 x198 17681181783630325494539235829908341910137898443866 17681181783630325494539235829908341910137898443866 35362363567260650989078471659816683820275796887732 (by decide) hm h198 h198
  let x200 := UInt256.mulMod x199 x199 modulus
  have h200 : x200.toNat % modulus.toNat = base.toNat ^ 70724727134521301978156943319633367640551593775464 % modulus.toNat :=
    mulMod_power base modulus x199 x199 35362363567260650989078471659816683820275796887732 35362363567260650989078471659816683820275796887732 70724727134521301978156943319633367640551593775464 (by decide) hm h199 h199
  let x201 := UInt256.mulMod x200 x200 modulus
  have h201 : x201.toNat % modulus.toNat = base.toNat ^ 141449454269042603956313886639266735281103187550928 % modulus.toNat :=
    mulMod_power base modulus x200 x200 70724727134521301978156943319633367640551593775464 70724727134521301978156943319633367640551593775464 141449454269042603956313886639266735281103187550928 (by decide) hm h200 h200
  let x202 := UInt256.mulMod x201 x201 modulus
  have h202 : x202.toNat % modulus.toNat = base.toNat ^ 282898908538085207912627773278533470562206375101856 % modulus.toNat :=
    mulMod_power base modulus x201 x201 141449454269042603956313886639266735281103187550928 141449454269042603956313886639266735281103187550928 282898908538085207912627773278533470562206375101856 (by decide) hm h201 h201
  let x203 := UInt256.mulMod x202 x202 modulus
  have h203 : x203.toNat % modulus.toNat = base.toNat ^ 565797817076170415825255546557066941124412750203712 % modulus.toNat :=
    mulMod_power base modulus x202 x202 282898908538085207912627773278533470562206375101856 282898908538085207912627773278533470562206375101856 565797817076170415825255546557066941124412750203712 (by decide) hm h202 h202
  let x204 := UInt256.mulMod x203 x203 modulus
  have h204 : x204.toNat % modulus.toNat = base.toNat ^ 1131595634152340831650511093114133882248825500407424 % modulus.toNat :=
    mulMod_power base modulus x203 x203 565797817076170415825255546557066941124412750203712 565797817076170415825255546557066941124412750203712 1131595634152340831650511093114133882248825500407424 (by decide) hm h203 h203
  let x205 := UInt256.mulMod x4 x204 modulus
  have h205 : x205.toNat % modulus.toNat = base.toNat ^ 1131595634152340831650511093114133882248825500407431 % modulus.toNat :=
    mulMod_power base modulus x4 x204 7 1131595634152340831650511093114133882248825500407424 1131595634152340831650511093114133882248825500407431 (by decide) hm h4 h204
  let x206 := UInt256.mulMod x205 x205 modulus
  have h206 : x206.toNat % modulus.toNat = base.toNat ^ 2263191268304681663301022186228267764497651000814862 % modulus.toNat :=
    mulMod_power base modulus x205 x205 1131595634152340831650511093114133882248825500407431 1131595634152340831650511093114133882248825500407431 2263191268304681663301022186228267764497651000814862 (by decide) hm h205 h205
  let x207 := UInt256.mulMod x206 x206 modulus
  have h207 : x207.toNat % modulus.toNat = base.toNat ^ 4526382536609363326602044372456535528995302001629724 % modulus.toNat :=
    mulMod_power base modulus x206 x206 2263191268304681663301022186228267764497651000814862 2263191268304681663301022186228267764497651000814862 4526382536609363326602044372456535528995302001629724 (by decide) hm h206 h206
  let x208 := UInt256.mulMod x207 x207 modulus
  have h208 : x208.toNat % modulus.toNat = base.toNat ^ 9052765073218726653204088744913071057990604003259448 % modulus.toNat :=
    mulMod_power base modulus x207 x207 4526382536609363326602044372456535528995302001629724 4526382536609363326602044372456535528995302001629724 9052765073218726653204088744913071057990604003259448 (by decide) hm h207 h207
  let x209 := UInt256.mulMod x208 x208 modulus
  have h209 : x209.toNat % modulus.toNat = base.toNat ^ 18105530146437453306408177489826142115981208006518896 % modulus.toNat :=
    mulMod_power base modulus x208 x208 9052765073218726653204088744913071057990604003259448 9052765073218726653204088744913071057990604003259448 18105530146437453306408177489826142115981208006518896 (by decide) hm h208 h208
  let x210 := UInt256.mulMod x209 x209 modulus
  have h210 : x210.toNat % modulus.toNat = base.toNat ^ 36211060292874906612816354979652284231962416013037792 % modulus.toNat :=
    mulMod_power base modulus x209 x209 18105530146437453306408177489826142115981208006518896 18105530146437453306408177489826142115981208006518896 36211060292874906612816354979652284231962416013037792 (by decide) hm h209 h209
  let x211 := UInt256.mulMod x210 x210 modulus
  have h211 : x211.toNat % modulus.toNat = base.toNat ^ 72422120585749813225632709959304568463924832026075584 % modulus.toNat :=
    mulMod_power base modulus x210 x210 36211060292874906612816354979652284231962416013037792 36211060292874906612816354979652284231962416013037792 72422120585749813225632709959304568463924832026075584 (by decide) hm h210 h210
  let x212 := UInt256.mulMod x4 x211 modulus
  have h212 : x212.toNat % modulus.toNat = base.toNat ^ 72422120585749813225632709959304568463924832026075591 % modulus.toNat :=
    mulMod_power base modulus x4 x211 7 72422120585749813225632709959304568463924832026075584 72422120585749813225632709959304568463924832026075591 (by decide) hm h4 h211
  let x213 := UInt256.mulMod x212 x212 modulus
  have h213 : x213.toNat % modulus.toNat = base.toNat ^ 144844241171499626451265419918609136927849664052151182 % modulus.toNat :=
    mulMod_power base modulus x212 x212 72422120585749813225632709959304568463924832026075591 72422120585749813225632709959304568463924832026075591 144844241171499626451265419918609136927849664052151182 (by decide) hm h212 h212
  let x214 := UInt256.mulMod x213 x213 modulus
  have h214 : x214.toNat % modulus.toNat = base.toNat ^ 289688482342999252902530839837218273855699328104302364 % modulus.toNat :=
    mulMod_power base modulus x213 x213 144844241171499626451265419918609136927849664052151182 144844241171499626451265419918609136927849664052151182 289688482342999252902530839837218273855699328104302364 (by decide) hm h213 h213
  let x215 := UInt256.mulMod x214 x214 modulus
  have h215 : x215.toNat % modulus.toNat = base.toNat ^ 579376964685998505805061679674436547711398656208604728 % modulus.toNat :=
    mulMod_power base modulus x214 x214 289688482342999252902530839837218273855699328104302364 289688482342999252902530839837218273855699328104302364 579376964685998505805061679674436547711398656208604728 (by decide) hm h214 h214
  let x216 := UInt256.mulMod x0 x215 modulus
  have h216 : x216.toNat % modulus.toNat = base.toNat ^ 579376964685998505805061679674436547711398656208604729 % modulus.toNat :=
    mulMod_power base modulus x0 x215 1 579376964685998505805061679674436547711398656208604728 579376964685998505805061679674436547711398656208604729 (by decide) hm h0 h215
  let x217 := UInt256.mulMod x216 x216 modulus
  have h217 : x217.toNat % modulus.toNat = base.toNat ^ 1158753929371997011610123359348873095422797312417209458 % modulus.toNat :=
    mulMod_power base modulus x216 x216 579376964685998505805061679674436547711398656208604729 579376964685998505805061679674436547711398656208604729 1158753929371997011610123359348873095422797312417209458 (by decide) hm h216 h216
  let x218 := UInt256.mulMod x217 x217 modulus
  have h218 : x218.toNat % modulus.toNat = base.toNat ^ 2317507858743994023220246718697746190845594624834418916 % modulus.toNat :=
    mulMod_power base modulus x217 x217 1158753929371997011610123359348873095422797312417209458 1158753929371997011610123359348873095422797312417209458 2317507858743994023220246718697746190845594624834418916 (by decide) hm h217 h217
  let x219 := UInt256.mulMod x218 x218 modulus
  have h219 : x219.toNat % modulus.toNat = base.toNat ^ 4635015717487988046440493437395492381691189249668837832 % modulus.toNat :=
    mulMod_power base modulus x218 x218 2317507858743994023220246718697746190845594624834418916 2317507858743994023220246718697746190845594624834418916 4635015717487988046440493437395492381691189249668837832 (by decide) hm h218 h218
  let x220 := UInt256.mulMod x219 x219 modulus
  have h220 : x220.toNat % modulus.toNat = base.toNat ^ 9270031434975976092880986874790984763382378499337675664 % modulus.toNat :=
    mulMod_power base modulus x219 x219 4635015717487988046440493437395492381691189249668837832 4635015717487988046440493437395492381691189249668837832 9270031434975976092880986874790984763382378499337675664 (by decide) hm h219 h219
  let x221 := UInt256.mulMod x3 x220 modulus
  have h221 : x221.toNat % modulus.toNat = base.toNat ^ 9270031434975976092880986874790984763382378499337675669 % modulus.toNat :=
    mulMod_power base modulus x3 x220 5 9270031434975976092880986874790984763382378499337675664 9270031434975976092880986874790984763382378499337675669 (by decide) hm h3 h220
  let x222 := UInt256.mulMod x221 x221 modulus
  have h222 : x222.toNat % modulus.toNat = base.toNat ^ 18540062869951952185761973749581969526764756998675351338 % modulus.toNat :=
    mulMod_power base modulus x221 x221 9270031434975976092880986874790984763382378499337675669 9270031434975976092880986874790984763382378499337675669 18540062869951952185761973749581969526764756998675351338 (by decide) hm h221 h221
  let x223 := UInt256.mulMod x222 x222 modulus
  have h223 : x223.toNat % modulus.toNat = base.toNat ^ 37080125739903904371523947499163939053529513997350702676 % modulus.toNat :=
    mulMod_power base modulus x222 x222 18540062869951952185761973749581969526764756998675351338 18540062869951952185761973749581969526764756998675351338 37080125739903904371523947499163939053529513997350702676 (by decide) hm h222 h222
  let x224 := UInt256.mulMod x223 x223 modulus
  have h224 : x224.toNat % modulus.toNat = base.toNat ^ 74160251479807808743047894998327878107059027994701405352 % modulus.toNat :=
    mulMod_power base modulus x223 x223 37080125739903904371523947499163939053529513997350702676 37080125739903904371523947499163939053529513997350702676 74160251479807808743047894998327878107059027994701405352 (by decide) hm h223 h223
  let x225 := UInt256.mulMod x224 x224 modulus
  have h225 : x225.toNat % modulus.toNat = base.toNat ^ 148320502959615617486095789996655756214118055989402810704 % modulus.toNat :=
    mulMod_power base modulus x224 x224 74160251479807808743047894998327878107059027994701405352 74160251479807808743047894998327878107059027994701405352 148320502959615617486095789996655756214118055989402810704 (by decide) hm h224 h224
  let x226 := UInt256.mulMod x225 x225 modulus
  have h226 : x226.toNat % modulus.toNat = base.toNat ^ 296641005919231234972191579993311512428236111978805621408 % modulus.toNat :=
    mulMod_power base modulus x225 x225 148320502959615617486095789996655756214118055989402810704 148320502959615617486095789996655756214118055989402810704 296641005919231234972191579993311512428236111978805621408 (by decide) hm h225 h225
  let x227 := UInt256.mulMod x226 x226 modulus
  have h227 : x227.toNat % modulus.toNat = base.toNat ^ 593282011838462469944383159986623024856472223957611242816 % modulus.toNat :=
    mulMod_power base modulus x226 x226 296641005919231234972191579993311512428236111978805621408 296641005919231234972191579993311512428236111978805621408 593282011838462469944383159986623024856472223957611242816 (by decide) hm h226 h226
  let x228 := UInt256.mulMod x227 x227 modulus
  have h228 : x228.toNat % modulus.toNat = base.toNat ^ 1186564023676924939888766319973246049712944447915222485632 % modulus.toNat :=
    mulMod_power base modulus x227 x227 593282011838462469944383159986623024856472223957611242816 593282011838462469944383159986623024856472223957611242816 1186564023676924939888766319973246049712944447915222485632 (by decide) hm h227 h227
  let x229 := UInt256.mulMod x7 x228 modulus
  have h229 : x229.toNat % modulus.toNat = base.toNat ^ 1186564023676924939888766319973246049712944447915222485645 % modulus.toNat :=
    mulMod_power base modulus x7 x228 13 1186564023676924939888766319973246049712944447915222485632 1186564023676924939888766319973246049712944447915222485645 (by decide) hm h7 h228
  let x230 := UInt256.mulMod x229 x229 modulus
  have h230 : x230.toNat % modulus.toNat = base.toNat ^ 2373128047353849879777532639946492099425888895830444971290 % modulus.toNat :=
    mulMod_power base modulus x229 x229 1186564023676924939888766319973246049712944447915222485645 1186564023676924939888766319973246049712944447915222485645 2373128047353849879777532639946492099425888895830444971290 (by decide) hm h229 h229
  let x231 := UInt256.mulMod x230 x230 modulus
  have h231 : x231.toNat % modulus.toNat = base.toNat ^ 4746256094707699759555065279892984198851777791660889942580 % modulus.toNat :=
    mulMod_power base modulus x230 x230 2373128047353849879777532639946492099425888895830444971290 2373128047353849879777532639946492099425888895830444971290 4746256094707699759555065279892984198851777791660889942580 (by decide) hm h230 h230
  let x232 := UInt256.mulMod x231 x231 modulus
  have h232 : x232.toNat % modulus.toNat = base.toNat ^ 9492512189415399519110130559785968397703555583321779885160 % modulus.toNat :=
    mulMod_power base modulus x231 x231 4746256094707699759555065279892984198851777791660889942580 4746256094707699759555065279892984198851777791660889942580 9492512189415399519110130559785968397703555583321779885160 (by decide) hm h231 h231
  let x233 := UInt256.mulMod x232 x232 modulus
  have h233 : x233.toNat % modulus.toNat = base.toNat ^ 18985024378830799038220261119571936795407111166643559770320 % modulus.toNat :=
    mulMod_power base modulus x232 x232 9492512189415399519110130559785968397703555583321779885160 9492512189415399519110130559785968397703555583321779885160 18985024378830799038220261119571936795407111166643559770320 (by decide) hm h232 h232
  let x234 := UInt256.mulMod x233 x233 modulus
  have h234 : x234.toNat % modulus.toNat = base.toNat ^ 37970048757661598076440522239143873590814222333287119540640 % modulus.toNat :=
    mulMod_power base modulus x233 x233 18985024378830799038220261119571936795407111166643559770320 18985024378830799038220261119571936795407111166643559770320 37970048757661598076440522239143873590814222333287119540640 (by decide) hm h233 h233
  let x235 := UInt256.mulMod x234 x234 modulus
  have h235 : x235.toNat % modulus.toNat = base.toNat ^ 75940097515323196152881044478287747181628444666574239081280 % modulus.toNat :=
    mulMod_power base modulus x234 x234 37970048757661598076440522239143873590814222333287119540640 37970048757661598076440522239143873590814222333287119540640 75940097515323196152881044478287747181628444666574239081280 (by decide) hm h234 h234
  let x236 := UInt256.mulMod x8 x235 modulus
  have h236 : x236.toNat % modulus.toNat = base.toNat ^ 75940097515323196152881044478287747181628444666574239081295 % modulus.toNat :=
    mulMod_power base modulus x8 x235 15 75940097515323196152881044478287747181628444666574239081280 75940097515323196152881044478287747181628444666574239081295 (by decide) hm h8 h235
  let x237 := UInt256.mulMod x236 x236 modulus
  have h237 : x237.toNat % modulus.toNat = base.toNat ^ 151880195030646392305762088956575494363256889333148478162590 % modulus.toNat :=
    mulMod_power base modulus x236 x236 75940097515323196152881044478287747181628444666574239081295 75940097515323196152881044478287747181628444666574239081295 151880195030646392305762088956575494363256889333148478162590 (by decide) hm h236 h236
  let x238 := UInt256.mulMod x237 x237 modulus
  have h238 : x238.toNat % modulus.toNat = base.toNat ^ 303760390061292784611524177913150988726513778666296956325180 % modulus.toNat :=
    mulMod_power base modulus x237 x237 151880195030646392305762088956575494363256889333148478162590 151880195030646392305762088956575494363256889333148478162590 303760390061292784611524177913150988726513778666296956325180 (by decide) hm h237 h237
  let x239 := UInt256.mulMod x238 x238 modulus
  have h239 : x239.toNat % modulus.toNat = base.toNat ^ 607520780122585569223048355826301977453027557332593912650360 % modulus.toNat :=
    mulMod_power base modulus x238 x238 303760390061292784611524177913150988726513778666296956325180 303760390061292784611524177913150988726513778666296956325180 607520780122585569223048355826301977453027557332593912650360 (by decide) hm h238 h238
  let x240 := UInt256.mulMod x239 x239 modulus
  have h240 : x240.toNat % modulus.toNat = base.toNat ^ 1215041560245171138446096711652603954906055114665187825300720 % modulus.toNat :=
    mulMod_power base modulus x239 x239 607520780122585569223048355826301977453027557332593912650360 607520780122585569223048355826301977453027557332593912650360 1215041560245171138446096711652603954906055114665187825300720 (by decide) hm h239 h239
  let x241 := UInt256.mulMod x240 x240 modulus
  have h241 : x241.toNat % modulus.toNat = base.toNat ^ 2430083120490342276892193423305207909812110229330375650601440 % modulus.toNat :=
    mulMod_power base modulus x240 x240 1215041560245171138446096711652603954906055114665187825300720 1215041560245171138446096711652603954906055114665187825300720 2430083120490342276892193423305207909812110229330375650601440 (by decide) hm h240 h240
  let x242 := UInt256.mulMod x0 x241 modulus
  have h242 : x242.toNat % modulus.toNat = base.toNat ^ 2430083120490342276892193423305207909812110229330375650601441 % modulus.toNat :=
    mulMod_power base modulus x0 x241 1 2430083120490342276892193423305207909812110229330375650601440 2430083120490342276892193423305207909812110229330375650601441 (by decide) hm h0 h241
  let x243 := UInt256.mulMod x242 x242 modulus
  have h243 : x243.toNat % modulus.toNat = base.toNat ^ 4860166240980684553784386846610415819624220458660751301202882 % modulus.toNat :=
    mulMod_power base modulus x242 x242 2430083120490342276892193423305207909812110229330375650601441 2430083120490342276892193423305207909812110229330375650601441 4860166240980684553784386846610415819624220458660751301202882 (by decide) hm h242 h242
  let x244 := UInt256.mulMod x243 x243 modulus
  have h244 : x244.toNat % modulus.toNat = base.toNat ^ 9720332481961369107568773693220831639248440917321502602405764 % modulus.toNat :=
    mulMod_power base modulus x243 x243 4860166240980684553784386846610415819624220458660751301202882 4860166240980684553784386846610415819624220458660751301202882 9720332481961369107568773693220831639248440917321502602405764 (by decide) hm h243 h243
  let x245 := UInt256.mulMod x244 x244 modulus
  have h245 : x245.toNat % modulus.toNat = base.toNat ^ 19440664963922738215137547386441663278496881834643005204811528 % modulus.toNat :=
    mulMod_power base modulus x244 x244 9720332481961369107568773693220831639248440917321502602405764 9720332481961369107568773693220831639248440917321502602405764 19440664963922738215137547386441663278496881834643005204811528 (by decide) hm h244 h244
  let x246 := UInt256.mulMod x245 x245 modulus
  have h246 : x246.toNat % modulus.toNat = base.toNat ^ 38881329927845476430275094772883326556993763669286010409623056 % modulus.toNat :=
    mulMod_power base modulus x245 x245 19440664963922738215137547386441663278496881834643005204811528 19440664963922738215137547386441663278496881834643005204811528 38881329927845476430275094772883326556993763669286010409623056 (by decide) hm h245 h245
  let x247 := UInt256.mulMod x246 x246 modulus
  have h247 : x247.toNat % modulus.toNat = base.toNat ^ 77762659855690952860550189545766653113987527338572020819246112 % modulus.toNat :=
    mulMod_power base modulus x246 x246 38881329927845476430275094772883326556993763669286010409623056 38881329927845476430275094772883326556993763669286010409623056 77762659855690952860550189545766653113987527338572020819246112 (by decide) hm h246 h246
  let x248 := UInt256.mulMod x247 x247 modulus
  have h248 : x248.toNat % modulus.toNat = base.toNat ^ 155525319711381905721100379091533306227975054677144041638492224 % modulus.toNat :=
    mulMod_power base modulus x247 x247 77762659855690952860550189545766653113987527338572020819246112 77762659855690952860550189545766653113987527338572020819246112 155525319711381905721100379091533306227975054677144041638492224 (by decide) hm h247 h247
  let x249 := UInt256.mulMod x0 x248 modulus
  have h249 : x249.toNat % modulus.toNat = base.toNat ^ 155525319711381905721100379091533306227975054677144041638492225 % modulus.toNat :=
    mulMod_power base modulus x0 x248 1 155525319711381905721100379091533306227975054677144041638492224 155525319711381905721100379091533306227975054677144041638492225 (by decide) hm h0 h248
  let x250 := UInt256.mulMod x249 x249 modulus
  have h250 : x250.toNat % modulus.toNat = base.toNat ^ 311050639422763811442200758183066612455950109354288083276984450 % modulus.toNat :=
    mulMod_power base modulus x249 x249 155525319711381905721100379091533306227975054677144041638492225 155525319711381905721100379091533306227975054677144041638492225 311050639422763811442200758183066612455950109354288083276984450 (by decide) hm h249 h249
  let x251 := UInt256.mulMod x250 x250 modulus
  have h251 : x251.toNat % modulus.toNat = base.toNat ^ 622101278845527622884401516366133224911900218708576166553968900 % modulus.toNat :=
    mulMod_power base modulus x250 x250 311050639422763811442200758183066612455950109354288083276984450 311050639422763811442200758183066612455950109354288083276984450 622101278845527622884401516366133224911900218708576166553968900 (by decide) hm h250 h250
  let x252 := UInt256.mulMod x251 x251 modulus
  have h252 : x252.toNat % modulus.toNat = base.toNat ^ 1244202557691055245768803032732266449823800437417152333107937800 % modulus.toNat :=
    mulMod_power base modulus x251 x251 622101278845527622884401516366133224911900218708576166553968900 622101278845527622884401516366133224911900218708576166553968900 1244202557691055245768803032732266449823800437417152333107937800 (by decide) hm h251 h251
  let x253 := UInt256.mulMod x252 x252 modulus
  have h253 : x253.toNat % modulus.toNat = base.toNat ^ 2488405115382110491537606065464532899647600874834304666215875600 % modulus.toNat :=
    mulMod_power base modulus x252 x252 1244202557691055245768803032732266449823800437417152333107937800 1244202557691055245768803032732266449823800437417152333107937800 2488405115382110491537606065464532899647600874834304666215875600 (by decide) hm h252 h252
  let x254 := UInt256.mulMod x253 x253 modulus
  have h254 : x254.toNat % modulus.toNat = base.toNat ^ 4976810230764220983075212130929065799295201749668609332431751200 % modulus.toNat :=
    mulMod_power base modulus x253 x253 2488405115382110491537606065464532899647600874834304666215875600 2488405115382110491537606065464532899647600874834304666215875600 4976810230764220983075212130929065799295201749668609332431751200 (by decide) hm h253 h253
  let x255 := UInt256.mulMod x2 x254 modulus
  have h255 : x255.toNat % modulus.toNat = base.toNat ^ 4976810230764220983075212130929065799295201749668609332431751203 % modulus.toNat :=
    mulMod_power base modulus x2 x254 3 4976810230764220983075212130929065799295201749668609332431751200 4976810230764220983075212130929065799295201749668609332431751203 (by decide) hm h2 h254
  let x256 := UInt256.mulMod x255 x255 modulus
  have h256 : x256.toNat % modulus.toNat = base.toNat ^ 9953620461528441966150424261858131598590403499337218664863502406 % modulus.toNat :=
    mulMod_power base modulus x255 x255 4976810230764220983075212130929065799295201749668609332431751203 4976810230764220983075212130929065799295201749668609332431751203 9953620461528441966150424261858131598590403499337218664863502406 (by decide) hm h255 h255
  let x257 := UInt256.mulMod x256 x256 modulus
  have h257 : x257.toNat % modulus.toNat = base.toNat ^ 19907240923056883932300848523716263197180806998674437329727004812 % modulus.toNat :=
    mulMod_power base modulus x256 x256 9953620461528441966150424261858131598590403499337218664863502406 9953620461528441966150424261858131598590403499337218664863502406 19907240923056883932300848523716263197180806998674437329727004812 (by decide) hm h256 h256
  let x258 := UInt256.mulMod x257 x257 modulus
  have h258 : x258.toNat % modulus.toNat = base.toNat ^ 39814481846113767864601697047432526394361613997348874659454009624 % modulus.toNat :=
    mulMod_power base modulus x257 x257 19907240923056883932300848523716263197180806998674437329727004812 19907240923056883932300848523716263197180806998674437329727004812 39814481846113767864601697047432526394361613997348874659454009624 (by decide) hm h257 h257
  let x259 := UInt256.mulMod x258 x258 modulus
  have h259 : x259.toNat % modulus.toNat = base.toNat ^ 79628963692227535729203394094865052788723227994697749318908019248 % modulus.toNat :=
    mulMod_power base modulus x258 x258 39814481846113767864601697047432526394361613997348874659454009624 39814481846113767864601697047432526394361613997348874659454009624 79628963692227535729203394094865052788723227994697749318908019248 (by decide) hm h258 h258
  let x260 := UInt256.mulMod x259 x259 modulus
  have h260 : x260.toNat % modulus.toNat = base.toNat ^ 159257927384455071458406788189730105577446455989395498637816038496 % modulus.toNat :=
    mulMod_power base modulus x259 x259 79628963692227535729203394094865052788723227994697749318908019248 79628963692227535729203394094865052788723227994697749318908019248 159257927384455071458406788189730105577446455989395498637816038496 (by decide) hm h259 h259
  let x261 := UInt256.mulMod x260 x260 modulus
  have h261 : x261.toNat % modulus.toNat = base.toNat ^ 318515854768910142916813576379460211154892911978790997275632076992 % modulus.toNat :=
    mulMod_power base modulus x260 x260 159257927384455071458406788189730105577446455989395498637816038496 159257927384455071458406788189730105577446455989395498637816038496 318515854768910142916813576379460211154892911978790997275632076992 (by decide) hm h260 h260
  let x262 := UInt256.mulMod x0 x261 modulus
  have h262 : x262.toNat % modulus.toNat = base.toNat ^ 318515854768910142916813576379460211154892911978790997275632076993 % modulus.toNat :=
    mulMod_power base modulus x0 x261 1 318515854768910142916813576379460211154892911978790997275632076992 318515854768910142916813576379460211154892911978790997275632076993 (by decide) hm h0 h261
  let x263 := UInt256.mulMod x262 x262 modulus
  have h263 : x263.toNat % modulus.toNat = base.toNat ^ 637031709537820285833627152758920422309785823957581994551264153986 % modulus.toNat :=
    mulMod_power base modulus x262 x262 318515854768910142916813576379460211154892911978790997275632076993 318515854768910142916813576379460211154892911978790997275632076993 637031709537820285833627152758920422309785823957581994551264153986 (by decide) hm h262 h262
  let x264 := UInt256.mulMod x263 x263 modulus
  have h264 : x264.toNat % modulus.toNat = base.toNat ^ 1274063419075640571667254305517840844619571647915163989102528307972 % modulus.toNat :=
    mulMod_power base modulus x263 x263 637031709537820285833627152758920422309785823957581994551264153986 637031709537820285833627152758920422309785823957581994551264153986 1274063419075640571667254305517840844619571647915163989102528307972 (by decide) hm h263 h263
  let x265 := UInt256.mulMod x264 x264 modulus
  have h265 : x265.toNat % modulus.toNat = base.toNat ^ 2548126838151281143334508611035681689239143295830327978205056615944 % modulus.toNat :=
    mulMod_power base modulus x264 x264 1274063419075640571667254305517840844619571647915163989102528307972 1274063419075640571667254305517840844619571647915163989102528307972 2548126838151281143334508611035681689239143295830327978205056615944 (by decide) hm h264 h264
  let x266 := UInt256.mulMod x265 x265 modulus
  have h266 : x266.toNat % modulus.toNat = base.toNat ^ 5096253676302562286669017222071363378478286591660655956410113231888 % modulus.toNat :=
    mulMod_power base modulus x265 x265 2548126838151281143334508611035681689239143295830327978205056615944 2548126838151281143334508611035681689239143295830327978205056615944 5096253676302562286669017222071363378478286591660655956410113231888 (by decide) hm h265 h265
  let x267 := UInt256.mulMod x266 x266 modulus
  have h267 : x267.toNat % modulus.toNat = base.toNat ^ 10192507352605124573338034444142726756956573183321311912820226463776 % modulus.toNat :=
    mulMod_power base modulus x266 x266 5096253676302562286669017222071363378478286591660655956410113231888 5096253676302562286669017222071363378478286591660655956410113231888 10192507352605124573338034444142726756956573183321311912820226463776 (by decide) hm h266 h266
  let x268 := UInt256.mulMod x7 x267 modulus
  have h268 : x268.toNat % modulus.toNat = base.toNat ^ 10192507352605124573338034444142726756956573183321311912820226463789 % modulus.toNat :=
    mulMod_power base modulus x7 x267 13 10192507352605124573338034444142726756956573183321311912820226463776 10192507352605124573338034444142726756956573183321311912820226463789 (by decide) hm h7 h267
  let x269 := UInt256.mulMod x268 x268 modulus
  have h269 : x269.toNat % modulus.toNat = base.toNat ^ 20385014705210249146676068888285453513913146366642623825640452927578 % modulus.toNat :=
    mulMod_power base modulus x268 x268 10192507352605124573338034444142726756956573183321311912820226463789 10192507352605124573338034444142726756956573183321311912820226463789 20385014705210249146676068888285453513913146366642623825640452927578 (by decide) hm h268 h268
  let x270 := UInt256.mulMod x269 x269 modulus
  have h270 : x270.toNat % modulus.toNat = base.toNat ^ 40770029410420498293352137776570907027826292733285247651280905855156 % modulus.toNat :=
    mulMod_power base modulus x269 x269 20385014705210249146676068888285453513913146366642623825640452927578 20385014705210249146676068888285453513913146366642623825640452927578 40770029410420498293352137776570907027826292733285247651280905855156 (by decide) hm h269 h269
  let x271 := UInt256.mulMod x270 x270 modulus
  have h271 : x271.toNat % modulus.toNat = base.toNat ^ 81540058820840996586704275553141814055652585466570495302561811710312 % modulus.toNat :=
    mulMod_power base modulus x270 x270 40770029410420498293352137776570907027826292733285247651280905855156 40770029410420498293352137776570907027826292733285247651280905855156 81540058820840996586704275553141814055652585466570495302561811710312 (by decide) hm h270 h270
  let x272 := UInt256.mulMod x271 x271 modulus
  have h272 : x272.toNat % modulus.toNat = base.toNat ^ 163080117641681993173408551106283628111305170933140990605123623420624 % modulus.toNat :=
    mulMod_power base modulus x271 x271 81540058820840996586704275553141814055652585466570495302561811710312 81540058820840996586704275553141814055652585466570495302561811710312 163080117641681993173408551106283628111305170933140990605123623420624 (by decide) hm h271 h271
  let x273 := UInt256.mulMod x6 x272 modulus
  have h273 : x273.toNat % modulus.toNat = base.toNat ^ 163080117641681993173408551106283628111305170933140990605123623420635 % modulus.toNat :=
    mulMod_power base modulus x6 x272 11 163080117641681993173408551106283628111305170933140990605123623420624 163080117641681993173408551106283628111305170933140990605123623420635 (by decide) hm h6 h272
  let x274 := UInt256.mulMod x273 x273 modulus
  have h274 : x274.toNat % modulus.toNat = base.toNat ^ 326160235283363986346817102212567256222610341866281981210247246841270 % modulus.toNat :=
    mulMod_power base modulus x273 x273 163080117641681993173408551106283628111305170933140990605123623420635 163080117641681993173408551106283628111305170933140990605123623420635 326160235283363986346817102212567256222610341866281981210247246841270 (by decide) hm h273 h273
  let x275 := UInt256.mulMod x274 x274 modulus
  have h275 : x275.toNat % modulus.toNat = base.toNat ^ 652320470566727972693634204425134512445220683732563962420494493682540 % modulus.toNat :=
    mulMod_power base modulus x274 x274 326160235283363986346817102212567256222610341866281981210247246841270 326160235283363986346817102212567256222610341866281981210247246841270 652320470566727972693634204425134512445220683732563962420494493682540 (by decide) hm h274 h274
  let x276 := UInt256.mulMod x275 x275 modulus
  have h276 : x276.toNat % modulus.toNat = base.toNat ^ 1304640941133455945387268408850269024890441367465127924840988987365080 % modulus.toNat :=
    mulMod_power base modulus x275 x275 652320470566727972693634204425134512445220683732563962420494493682540 652320470566727972693634204425134512445220683732563962420494493682540 1304640941133455945387268408850269024890441367465127924840988987365080 (by decide) hm h275 h275
  let x277 := UInt256.mulMod x276 x276 modulus
  have h277 : x277.toNat % modulus.toNat = base.toNat ^ 2609281882266911890774536817700538049780882734930255849681977974730160 % modulus.toNat :=
    mulMod_power base modulus x276 x276 1304640941133455945387268408850269024890441367465127924840988987365080 1304640941133455945387268408850269024890441367465127924840988987365080 2609281882266911890774536817700538049780882734930255849681977974730160 (by decide) hm h276 h276
  let x278 := UInt256.mulMod x277 x277 modulus
  have h278 : x278.toNat % modulus.toNat = base.toNat ^ 5218563764533823781549073635401076099561765469860511699363955949460320 % modulus.toNat :=
    mulMod_power base modulus x277 x277 2609281882266911890774536817700538049780882734930255849681977974730160 2609281882266911890774536817700538049780882734930255849681977974730160 5218563764533823781549073635401076099561765469860511699363955949460320 (by decide) hm h277 h277
  let x279 := UInt256.mulMod x0 x278 modulus
  have h279 : x279.toNat % modulus.toNat = base.toNat ^ 5218563764533823781549073635401076099561765469860511699363955949460321 % modulus.toNat :=
    mulMod_power base modulus x0 x278 1 5218563764533823781549073635401076099561765469860511699363955949460320 5218563764533823781549073635401076099561765469860511699363955949460321 (by decide) hm h0 h278
  let x280 := UInt256.mulMod x279 x279 modulus
  have h280 : x280.toNat % modulus.toNat = base.toNat ^ 10437127529067647563098147270802152199123530939721023398727911898920642 % modulus.toNat :=
    mulMod_power base modulus x279 x279 5218563764533823781549073635401076099561765469860511699363955949460321 5218563764533823781549073635401076099561765469860511699363955949460321 10437127529067647563098147270802152199123530939721023398727911898920642 (by decide) hm h279 h279
  let x281 := UInt256.mulMod x280 x280 modulus
  have h281 : x281.toNat % modulus.toNat = base.toNat ^ 20874255058135295126196294541604304398247061879442046797455823797841284 % modulus.toNat :=
    mulMod_power base modulus x280 x280 10437127529067647563098147270802152199123530939721023398727911898920642 10437127529067647563098147270802152199123530939721023398727911898920642 20874255058135295126196294541604304398247061879442046797455823797841284 (by decide) hm h280 h280
  let x282 := UInt256.mulMod x281 x281 modulus
  have h282 : x282.toNat % modulus.toNat = base.toNat ^ 41748510116270590252392589083208608796494123758884093594911647595682568 % modulus.toNat :=
    mulMod_power base modulus x281 x281 20874255058135295126196294541604304398247061879442046797455823797841284 20874255058135295126196294541604304398247061879442046797455823797841284 41748510116270590252392589083208608796494123758884093594911647595682568 (by decide) hm h281 h281
  let x283 := UInt256.mulMod x282 x282 modulus
  have h283 : x283.toNat % modulus.toNat = base.toNat ^ 83497020232541180504785178166417217592988247517768187189823295191365136 % modulus.toNat :=
    mulMod_power base modulus x282 x282 41748510116270590252392589083208608796494123758884093594911647595682568 41748510116270590252392589083208608796494123758884093594911647595682568 83497020232541180504785178166417217592988247517768187189823295191365136 (by decide) hm h282 h282
  let x284 := UInt256.mulMod x8 x283 modulus
  have h284 : x284.toNat % modulus.toNat = base.toNat ^ 83497020232541180504785178166417217592988247517768187189823295191365151 % modulus.toNat :=
    mulMod_power base modulus x8 x283 15 83497020232541180504785178166417217592988247517768187189823295191365136 83497020232541180504785178166417217592988247517768187189823295191365151 (by decide) hm h8 h283
  let x285 := UInt256.mulMod x284 x284 modulus
  have h285 : x285.toNat % modulus.toNat = base.toNat ^ 166994040465082361009570356332834435185976495035536374379646590382730302 % modulus.toNat :=
    mulMod_power base modulus x284 x284 83497020232541180504785178166417217592988247517768187189823295191365151 83497020232541180504785178166417217592988247517768187189823295191365151 166994040465082361009570356332834435185976495035536374379646590382730302 (by decide) hm h284 h284
  let x286 := UInt256.mulMod x285 x285 modulus
  have h286 : x286.toNat % modulus.toNat = base.toNat ^ 333988080930164722019140712665668870371952990071072748759293180765460604 % modulus.toNat :=
    mulMod_power base modulus x285 x285 166994040465082361009570356332834435185976495035536374379646590382730302 166994040465082361009570356332834435185976495035536374379646590382730302 333988080930164722019140712665668870371952990071072748759293180765460604 (by decide) hm h285 h285
  let x287 := UInt256.mulMod x286 x286 modulus
  have h287 : x287.toNat % modulus.toNat = base.toNat ^ 667976161860329444038281425331337740743905980142145497518586361530921208 % modulus.toNat :=
    mulMod_power base modulus x286 x286 333988080930164722019140712665668870371952990071072748759293180765460604 333988080930164722019140712665668870371952990071072748759293180765460604 667976161860329444038281425331337740743905980142145497518586361530921208 (by decide) hm h286 h286
  let x288 := UInt256.mulMod x287 x287 modulus
  have h288 : x288.toNat % modulus.toNat = base.toNat ^ 1335952323720658888076562850662675481487811960284290995037172723061842416 % modulus.toNat :=
    mulMod_power base modulus x287 x287 667976161860329444038281425331337740743905980142145497518586361530921208 667976161860329444038281425331337740743905980142145497518586361530921208 1335952323720658888076562850662675481487811960284290995037172723061842416 (by decide) hm h287 h287
  let x289 := UInt256.mulMod x288 x288 modulus
  have h289 : x289.toNat % modulus.toNat = base.toNat ^ 2671904647441317776153125701325350962975623920568581990074345446123684832 % modulus.toNat :=
    mulMod_power base modulus x288 x288 1335952323720658888076562850662675481487811960284290995037172723061842416 1335952323720658888076562850662675481487811960284290995037172723061842416 2671904647441317776153125701325350962975623920568581990074345446123684832 (by decide) hm h288 h288
  let x290 := UInt256.mulMod x289 x289 modulus
  have h290 : x290.toNat % modulus.toNat = base.toNat ^ 5343809294882635552306251402650701925951247841137163980148690892247369664 % modulus.toNat :=
    mulMod_power base modulus x289 x289 2671904647441317776153125701325350962975623920568581990074345446123684832 2671904647441317776153125701325350962975623920568581990074345446123684832 5343809294882635552306251402650701925951247841137163980148690892247369664 (by decide) hm h289 h289
  let x291 := UInt256.mulMod x8 x290 modulus
  have h291 : x291.toNat % modulus.toNat = base.toNat ^ 5343809294882635552306251402650701925951247841137163980148690892247369679 % modulus.toNat :=
    mulMod_power base modulus x8 x290 15 5343809294882635552306251402650701925951247841137163980148690892247369664 5343809294882635552306251402650701925951247841137163980148690892247369679 (by decide) hm h8 h290
  let x292 := UInt256.mulMod x291 x291 modulus
  have h292 : x292.toNat % modulus.toNat = base.toNat ^ 10687618589765271104612502805301403851902495682274327960297381784494739358 % modulus.toNat :=
    mulMod_power base modulus x291 x291 5343809294882635552306251402650701925951247841137163980148690892247369679 5343809294882635552306251402650701925951247841137163980148690892247369679 10687618589765271104612502805301403851902495682274327960297381784494739358 (by decide) hm h291 h291
  let x293 := UInt256.mulMod x292 x292 modulus
  have h293 : x293.toNat % modulus.toNat = base.toNat ^ 21375237179530542209225005610602807703804991364548655920594763568989478716 % modulus.toNat :=
    mulMod_power base modulus x292 x292 10687618589765271104612502805301403851902495682274327960297381784494739358 10687618589765271104612502805301403851902495682274327960297381784494739358 21375237179530542209225005610602807703804991364548655920594763568989478716 (by decide) hm h292 h292
  let x294 := UInt256.mulMod x293 x293 modulus
  have h294 : x294.toNat % modulus.toNat = base.toNat ^ 42750474359061084418450011221205615407609982729097311841189527137978957432 % modulus.toNat :=
    mulMod_power base modulus x293 x293 21375237179530542209225005610602807703804991364548655920594763568989478716 21375237179530542209225005610602807703804991364548655920594763568989478716 42750474359061084418450011221205615407609982729097311841189527137978957432 (by decide) hm h293 h293
  let x295 := UInt256.mulMod x294 x294 modulus
  have h295 : x295.toNat % modulus.toNat = base.toNat ^ 85500948718122168836900022442411230815219965458194623682379054275957914864 % modulus.toNat :=
    mulMod_power base modulus x294 x294 42750474359061084418450011221205615407609982729097311841189527137978957432 42750474359061084418450011221205615407609982729097311841189527137978957432 85500948718122168836900022442411230815219965458194623682379054275957914864 (by decide) hm h294 h294
  let x296 := UInt256.mulMod x7 x295 modulus
  have h296 : x296.toNat % modulus.toNat = base.toNat ^ 85500948718122168836900022442411230815219965458194623682379054275957914877 % modulus.toNat :=
    mulMod_power base modulus x7 x295 13 85500948718122168836900022442411230815219965458194623682379054275957914864 85500948718122168836900022442411230815219965458194623682379054275957914877 (by decide) hm h7 h295
  let x297 := UInt256.mulMod x296 x296 modulus
  have h297 : x297.toNat % modulus.toNat = base.toNat ^ 171001897436244337673800044884822461630439930916389247364758108551915829754 % modulus.toNat :=
    mulMod_power base modulus x296 x296 85500948718122168836900022442411230815219965458194623682379054275957914877 85500948718122168836900022442411230815219965458194623682379054275957914877 171001897436244337673800044884822461630439930916389247364758108551915829754 (by decide) hm h296 h296
  let x298 := UInt256.mulMod x297 x297 modulus
  have h298 : x298.toNat % modulus.toNat = base.toNat ^ 342003794872488675347600089769644923260879861832778494729516217103831659508 % modulus.toNat :=
    mulMod_power base modulus x297 x297 171001897436244337673800044884822461630439930916389247364758108551915829754 171001897436244337673800044884822461630439930916389247364758108551915829754 342003794872488675347600089769644923260879861832778494729516217103831659508 (by decide) hm h297 h297
  let x299 := UInt256.mulMod x0 x298 modulus
  have h299 : x299.toNat % modulus.toNat = base.toNat ^ 342003794872488675347600089769644923260879861832778494729516217103831659509 % modulus.toNat :=
    mulMod_power base modulus x0 x298 1 342003794872488675347600089769644923260879861832778494729516217103831659508 342003794872488675347600089769644923260879861832778494729516217103831659509 (by decide) hm h0 h298
  let x300 := UInt256.mulMod x299 x299 modulus
  have h300 : x300.toNat % modulus.toNat = base.toNat ^ 684007589744977350695200179539289846521759723665556989459032434207663319018 % modulus.toNat :=
    mulMod_power base modulus x299 x299 342003794872488675347600089769644923260879861832778494729516217103831659509 342003794872488675347600089769644923260879861832778494729516217103831659509 684007589744977350695200179539289846521759723665556989459032434207663319018 (by decide) hm h299 h299
  let x301 := UInt256.mulMod x300 x300 modulus
  have h301 : x301.toNat % modulus.toNat = base.toNat ^ 1368015179489954701390400359078579693043519447331113978918064868415326638036 % modulus.toNat :=
    mulMod_power base modulus x300 x300 684007589744977350695200179539289846521759723665556989459032434207663319018 684007589744977350695200179539289846521759723665556989459032434207663319018 1368015179489954701390400359078579693043519447331113978918064868415326638036 (by decide) hm h300 h300
  let x302 := UInt256.mulMod x301 x301 modulus
  have h302 : x302.toNat % modulus.toNat = base.toNat ^ 2736030358979909402780800718157159386087038894662227957836129736830653276072 % modulus.toNat :=
    mulMod_power base modulus x301 x301 1368015179489954701390400359078579693043519447331113978918064868415326638036 1368015179489954701390400359078579693043519447331113978918064868415326638036 2736030358979909402780800718157159386087038894662227957836129736830653276072 (by decide) hm h301 h301
  let x303 := UInt256.mulMod x302 x302 modulus
  have h303 : x303.toNat % modulus.toNat = base.toNat ^ 5472060717959818805561601436314318772174077789324455915672259473661306552144 % modulus.toNat :=
    mulMod_power base modulus x302 x302 2736030358979909402780800718157159386087038894662227957836129736830653276072 2736030358979909402780800718157159386087038894662227957836129736830653276072 5472060717959818805561601436314318772174077789324455915672259473661306552144 (by decide) hm h302 h302
  let x304 := UInt256.mulMod x303 x303 modulus
  have h304 : x304.toNat % modulus.toNat = base.toNat ^ 10944121435919637611123202872628637544348155578648911831344518947322613104288 % modulus.toNat :=
    mulMod_power base modulus x303 x303 5472060717959818805561601436314318772174077789324455915672259473661306552144 5472060717959818805561601436314318772174077789324455915672259473661306552144 10944121435919637611123202872628637544348155578648911831344518947322613104288 (by decide) hm h303 h303
  let x305 := UInt256.mulMod x304 x304 modulus
  have h305 : x305.toNat % modulus.toNat = base.toNat ^ 21888242871839275222246405745257275088696311157297823662689037894645226208576 % modulus.toNat :=
    mulMod_power base modulus x304 x304 10944121435919637611123202872628637544348155578648911831344518947322613104288 10944121435919637611123202872628637544348155578648911831344518947322613104288 21888242871839275222246405745257275088696311157297823662689037894645226208576 (by decide) hm h304 h304
  let x306 := UInt256.mulMod x3 x305 modulus
  have h306 : x306.toNat % modulus.toNat = base.toNat ^ 21888242871839275222246405745257275088696311157297823662689037894645226208581 % modulus.toNat :=
    mulMod_power base modulus x3 x305 5 21888242871839275222246405745257275088696311157297823662689037894645226208576 21888242871839275222246405745257275088696311157297823662689037894645226208581 (by decide) hm h3 h305
  have hlt : x306.toNat < modulus.toNat := by
    change (UInt256.mulMod x3 x305 modulus).toNat < modulus.toNat
    rw [WindowMath.mulMod_toNat _ _ _ hm]
    exact Nat.mod_lt _ hm
  rw [Nat.mod_eq_of_lt hlt] at h306
  exact h306

#print axioms value_toNat
end HistoricalSearch.FixedExponent
