import Challenge.Ripemd160.Submission.Proofs.Bytecode.VerifierData
import Challenge.Ripemd160.Submission.Proofs.Bytecode.PatternedScanState
import Challenge.Ripemd160.Submission.Proofs.Bytecode.PatternedScanTrace

set_option warningAsError true
set_option maxRecDepth 100000
set_option maxHeartbeats 20000000
set_option linter.unusedSimpArgs false

/-!
# Straight-line patterned-input verifier: located paths and run lemmas

Each verifier is a straight-line block appended after the main body.  It loads
the calldata words at the compare offsets, folds `lor (xor readWord expected)`
into one accumulator, and branches on it: nonzero jumps to the generic fallback
at pc 268, zero falls through to a `JUMP` to the digest-table entry at pc 4836.
-/

namespace Challenge.Ripemd160.Submission.Proofs.Bytecode.VerifierRun

open Challenge.Ripemd160 Challenge.EvmProof EvmSemantics EvmSemantics.EVM
open PatternedScan PatternedSwar PatternedScanState
open VerifierData

/-- The verifier start pc for each size. -/
def verifyStart : Nat → Nat
  | 1 => 5209
  | 31 => 5257
  | 32 => 5305
  | 55 => 5353
  | 56 => 5439
  | 63 => 5525
  | 64 => 5611
  | 65 => 5697
  | 119 => 5821
  | 120 => 5983
  | 128 => 6145
  | 256 => 6307
  | 376 => 6621
  | 1000 => 7091
  | _ => 0

/-- Verifier entry: the dispatch `JUMPI` lands here with an empty stack. -/
def verifyEntry (n : Nat) (input : ByteArray) : State :=
  atPC input (verifyStart n)

/-- Hit exit: fall through the `JUMPI` and `JUMP` to the digest entry. -/
def verifyHit (input : ByteArray) : State := atPC input 4836

/-- Miss exit: the `JUMPI` jumps to the generic fallback. -/
def verifyMiss (input : ByteArray) : State := atPC input 268

def verifyPath1 : List Located :=
[
    opAt 4142 .JUMPDEST,
    pushAt 4143 0 0,
    pushAt 4144 32 43874346312576839672212443538448152585028080127215369968075725190498334277632,
    pushAt 4145 1 0,
    opAt 4146 .CALLDATALOAD,
    opAt 4147 .XOR,
    opAt 4148 .OR,
    pushAt 4149 2 268,
    opAt 4150 .JUMPI,
    pushAt 4151 2 4836,
    opAt 4152 .JUMP
  ]

def verifyPath31 : List Located :=
[
    opAt 4153 .JUMPDEST,
    pushAt 4154 0 0,
    pushAt 4155 32 44046402572626160612103472728795008085361523578694645928734845681441465000192,
    pushAt 4156 1 0,
    opAt 4157 .CALLDATALOAD,
    opAt 4158 .XOR,
    opAt 4159 .OR,
    pushAt 4160 2 268,
    opAt 4161 .JUMPI,
    pushAt 4162 2 4836,
    opAt 4163 .JUMP
  ]

def verifyPath32 : List Located :=
[
    opAt 4164 .JUMPDEST,
    pushAt 4165 0 0,
    pushAt 4166 32 44046402572626160612103472728795008085361523578694645928734845681441465000289,
    pushAt 4167 1 0,
    opAt 4168 .CALLDATALOAD,
    opAt 4169 .XOR,
    opAt 4170 .OR,
    pushAt 4171 2 268,
    opAt 4172 .JUMPI,
    pushAt 4173 2 4836,
    opAt 4174 .JUMP
  ]

def verifyPath55 : List Located :=
[
    opAt 4175 .JUMPDEST,
    pushAt 4176 0 0,
    pushAt 4177 32 44046402572626160612103472728795008085361523578694645928734845681441465000289,
    pushAt 4178 1 0,
    opAt 4179 .CALLDATALOAD,
    opAt 4180 .XOR,
    opAt 4181 .OR,
    pushAt 4182 32 44046402572626160612103472728795008085361523578694645928734845681441465000289,
    pushAt 4183 1 23,
    opAt 4184 .CALLDATALOAD,
    opAt 4185 .XOR,
    opAt 4186 .OR,
    pushAt 4187 2 268,
    opAt 4188 .JUMPI,
    pushAt 4189 2 4836,
    opAt 4190 .JUMP
  ]

def verifyPath56 : List Located :=
[
    opAt 4191 .JUMPDEST,
    pushAt 4192 0 0,
    pushAt 4193 32 44046402572626160612103472728795008085361523578694645928734845681441465000289,
    pushAt 4194 1 0,
    opAt 4195 .CALLDATALOAD,
    opAt 4196 .XOR,
    opAt 4197 .OR,
    pushAt 4198 32 44046402572626160612103472728795008085361523578694645928734845681441465000289,
    pushAt 4199 1 24,
    opAt 4200 .CALLDATALOAD,
    opAt 4201 .XOR,
    opAt 4202 .OR,
    pushAt 4203 2 268,
    opAt 4204 .JUMPI,
    pushAt 4205 2 4836,
    opAt 4206 .JUMP
  ]

def verifyPath63 : List Located :=
[
    opAt 4207 .JUMPDEST,
    pushAt 4208 0 0,
    pushAt 4209 32 44046402572626160612103472728795008085361523578694645928734845681441465000289,
    pushAt 4210 1 0,
    opAt 4211 .CALLDATALOAD,
    opAt 4212 .XOR,
    opAt 4213 .OR,
    pushAt 4214 32 44046402572626160612103472728795008085361523578694645928734845681441465000289,
    pushAt 4215 1 31,
    opAt 4216 .CALLDATALOAD,
    opAt 4217 .XOR,
    opAt 4218 .OR,
    pushAt 4219 2 268,
    opAt 4220 .JUMPI,
    pushAt 4221 2 4836,
    opAt 4222 .JUMP
  ]

def verifyPath64 : List Located :=
[
    opAt 4223 .JUMPDEST,
    pushAt 4224 0 0,
    pushAt 4225 32 44046402572626160612103472728795008085361523578694645928734845681441465000289,
    pushAt 4226 1 0,
    opAt 4227 .CALLDATALOAD,
    opAt 4228 .XOR,
    opAt 4229 .OR,
    pushAt 4230 32 44046402572626160612103472728795008085361523578694645928734845681441465000289,
    pushAt 4231 1 32,
    opAt 4232 .CALLDATALOAD,
    opAt 4233 .XOR,
    opAt 4234 .OR,
    pushAt 4235 2 268,
    opAt 4236 .JUMPI,
    pushAt 4237 2 4836,
    opAt 4238 .JUMP
  ]

def verifyPath65 : List Located :=
[
    opAt 4239 .JUMPDEST,
    pushAt 4240 0 0,
    pushAt 4241 32 44046402572626160612103472728795008085361523578694645928734845681441465000289,
    pushAt 4242 1 0,
    opAt 4243 .CALLDATALOAD,
    opAt 4244 .XOR,
    opAt 4245 .OR,
    pushAt 4246 32 44046402572626160612103472728795008085361523578694645928734845681441465000289,
    pushAt 4247 1 32,
    opAt 4248 .CALLDATALOAD,
    opAt 4249 .XOR,
    opAt 4250 .OR,
    pushAt 4251 32 44046402572626160612103472728795008085361523578694645928734845681441465000289,
    pushAt 4252 1 33,
    opAt 4253 .CALLDATALOAD,
    opAt 4254 .XOR,
    opAt 4255 .OR,
    pushAt 4256 2 268,
    opAt 4257 .JUMPI,
    pushAt 4258 2 4836,
    opAt 4259 .JUMP
  ]

def verifyPath119 : List Located :=
[
    opAt 4260 .JUMPDEST,
    pushAt 4261 0 0,
    pushAt 4262 32 44046402572626160612103472728795008085361523578694645928734845681441465000289,
    pushAt 4263 1 0,
    opAt 4264 .CALLDATALOAD,
    opAt 4265 .XOR,
    opAt 4266 .OR,
    pushAt 4267 32 44046402572626160612103472728795008085361523578694645928734845681441465000289,
    pushAt 4268 1 32,
    opAt 4269 .CALLDATALOAD,
    opAt 4270 .XOR,
    opAt 4271 .OR,
    pushAt 4272 32 44046402572626160612103472728795008085361523578694645928734845681441465000289,
    pushAt 4273 1 64,
    opAt 4274 .CALLDATALOAD,
    opAt 4275 .XOR,
    opAt 4276 .OR,
    pushAt 4277 32 44046402572626160612103472728795008085361523578694645928734845681441465000289,
    pushAt 4278 1 87,
    opAt 4279 .CALLDATALOAD,
    opAt 4280 .XOR,
    opAt 4281 .OR,
    pushAt 4282 2 268,
    opAt 4283 .JUMPI,
    pushAt 4284 2 4836,
    opAt 4285 .JUMP
  ]

def verifyPath120 : List Located :=
[
    opAt 4286 .JUMPDEST,
    pushAt 4287 0 0,
    pushAt 4288 32 44046402572626160612103472728795008085361523578694645928734845681441465000289,
    pushAt 4289 1 0,
    opAt 4290 .CALLDATALOAD,
    opAt 4291 .XOR,
    opAt 4292 .OR,
    pushAt 4293 32 44046402572626160612103472728795008085361523578694645928734845681441465000289,
    pushAt 4294 1 32,
    opAt 4295 .CALLDATALOAD,
    opAt 4296 .XOR,
    opAt 4297 .OR,
    pushAt 4298 32 44046402572626160612103472728795008085361523578694645928734845681441465000289,
    pushAt 4299 1 64,
    opAt 4300 .CALLDATALOAD,
    opAt 4301 .XOR,
    opAt 4302 .OR,
    pushAt 4303 32 44046402572626160612103472728795008085361523578694645928734845681441465000289,
    pushAt 4304 1 88,
    opAt 4305 .CALLDATALOAD,
    opAt 4306 .XOR,
    opAt 4307 .OR,
    pushAt 4308 2 268,
    opAt 4309 .JUMPI,
    pushAt 4310 2 4836,
    opAt 4311 .JUMP
  ]

def verifyPath128 : List Located :=
[
    opAt 4312 .JUMPDEST,
    pushAt 4313 0 0,
    pushAt 4314 32 44046402572626160612103472728795008085361523578694645928734845681441465000289,
    pushAt 4315 1 0,
    opAt 4316 .CALLDATALOAD,
    opAt 4317 .XOR,
    opAt 4318 .OR,
    pushAt 4319 32 44046402572626160612103472728795008085361523578694645928734845681441465000289,
    pushAt 4320 1 32,
    opAt 4321 .CALLDATALOAD,
    opAt 4322 .XOR,
    opAt 4323 .OR,
    pushAt 4324 32 44046402572626160612103472728795008085361523578694645928734845681441465000289,
    pushAt 4325 1 64,
    opAt 4326 .CALLDATALOAD,
    opAt 4327 .XOR,
    opAt 4328 .OR,
    pushAt 4329 32 44046402572626160612103472728795008085361523578694645928734845681441465000289,
    pushAt 4330 1 96,
    opAt 4331 .CALLDATALOAD,
    opAt 4332 .XOR,
    opAt 4333 .OR,
    pushAt 4334 2 268,
    opAt 4335 .JUMPI,
    pushAt 4336 2 4836,
    opAt 4337 .JUMP
  ]

def verifyPath256 : List Located :=
[
    opAt 4338 .JUMPDEST,
    pushAt 4339 0 0,
    pushAt 4340 32 44046402572626160612103472728795008085361523578694645928734845681441465000289,
    pushAt 4341 1 0,
    opAt 4342 .CALLDATALOAD,
    opAt 4343 .XOR,
    opAt 4344 .OR,
    pushAt 4345 32 44046402572626160612103472728795008085361523578694645928734845681441465000289,
    pushAt 4346 1 32,
    opAt 4347 .CALLDATALOAD,
    opAt 4348 .XOR,
    opAt 4349 .OR,
    pushAt 4350 32 44046402572626160612103472728795008085361523578694645928734845681441465000289,
    pushAt 4351 1 64,
    opAt 4352 .CALLDATALOAD,
    opAt 4353 .XOR,
    opAt 4354 .OR,
    pushAt 4355 32 44046402572626160612103472728795008085361523578694645928734845681441465000289,
    pushAt 4356 1 96,
    opAt 4357 .CALLDATALOAD,
    opAt 4358 .XOR,
    opAt 4359 .OR,
    pushAt 4360 32 44046402572626160612103472728795008085361523578694645928734845681441465000289,
    pushAt 4361 1 128,
    opAt 4362 .CALLDATALOAD,
    opAt 4363 .XOR,
    opAt 4364 .OR,
    pushAt 4365 32 44046402572626160612103472728795008085361523578694645928734845681441465000289,
    pushAt 4366 1 160,
    opAt 4367 .CALLDATALOAD,
    opAt 4368 .XOR,
    opAt 4369 .OR,
    pushAt 4370 32 44046402572626160612103472728795008085361523578694645928734845681441465000289,
    pushAt 4371 1 192,
    opAt 4372 .CALLDATALOAD,
    opAt 4373 .XOR,
    opAt 4374 .OR,
    pushAt 4375 32 44046402572626160612103472728795008085361523578694645928734845681441465000289,
    pushAt 4376 1 224,
    opAt 4377 .CALLDATALOAD,
    opAt 4378 .XOR,
    opAt 4379 .OR,
    pushAt 4380 2 268,
    opAt 4381 .JUMPI,
    pushAt 4382 2 4836,
    opAt 4383 .JUMP
  ]

def verifyPath376 : List Located :=
[
    opAt 4384 .JUMPDEST,
    pushAt 4385 0 0,
    pushAt 4386 32 44046402572626160612103472728795008085361523578694645928734845681441465000289,
    pushAt 4387 1 0,
    opAt 4388 .CALLDATALOAD,
    opAt 4389 .XOR,
    opAt 4390 .OR,
    pushAt 4391 32 44046402572626160612103472728795008085361523578694645928734845681441465000289,
    pushAt 4392 1 32,
    opAt 4393 .CALLDATALOAD,
    opAt 4394 .XOR,
    opAt 4395 .OR,
    pushAt 4396 32 44046402572626160612103472728795008085361523578694645928734845681441465000289,
    pushAt 4397 1 64,
    opAt 4398 .CALLDATALOAD,
    opAt 4399 .XOR,
    opAt 4400 .OR,
    pushAt 4401 32 44046402572626160612103472728795008085361523578694645928734845681441465000289,
    pushAt 4402 1 96,
    opAt 4403 .CALLDATALOAD,
    opAt 4404 .XOR,
    opAt 4405 .OR,
    pushAt 4406 32 44046402572626160612103472728795008085361523578694645928734845681441465000289,
    pushAt 4407 1 128,
    opAt 4408 .CALLDATALOAD,
    opAt 4409 .XOR,
    opAt 4410 .OR,
    pushAt 4411 32 44046402572626160612103472728795008085361523578694645928734845681441465000289,
    pushAt 4412 1 160,
    opAt 4413 .CALLDATALOAD,
    opAt 4414 .XOR,
    opAt 4415 .OR,
    pushAt 4416 32 44046402572626160612103472728795008085361523578694645928734845681441465000289,
    pushAt 4417 1 192,
    opAt 4418 .CALLDATALOAD,
    opAt 4419 .XOR,
    opAt 4420 .OR,
    pushAt 4421 32 44046402572626160612103472728795008085361523578694645928734845681441465000289,
    pushAt 4422 1 224,
    opAt 4423 .CALLDATALOAD,
    opAt 4424 .XOR,
    opAt 4425 .OR,
    pushAt 4426 32 44046402572626160612103472728795008085361523578694645928734845681441465000289,
    pushAt 4427 2 256,
    opAt 4428 .CALLDATALOAD,
    opAt 4429 .XOR,
    opAt 4430 .OR,
    pushAt 4431 32 44046402572626160612103472728795008085361523578694645928734845681441465000289,
    pushAt 4432 2 288,
    opAt 4433 .CALLDATALOAD,
    opAt 4434 .XOR,
    opAt 4435 .OR,
    pushAt 4436 32 44046402572626160612103472728795008085361523578694645928734845681441465000289,
    pushAt 4437 2 320,
    opAt 4438 .CALLDATALOAD,
    opAt 4439 .XOR,
    opAt 4440 .OR,
    pushAt 4441 32 44046402572626160612103472728795008085361523578694645928734845681441465000289,
    pushAt 4442 2 344,
    opAt 4443 .CALLDATALOAD,
    opAt 4444 .XOR,
    opAt 4445 .OR,
    pushAt 4446 2 268,
    opAt 4447 .JUMPI,
    pushAt 4448 2 4836,
    opAt 4449 .JUMP
  ]

def verifyPath1000 : List Located :=
[
    opAt 4450 .JUMPDEST,
    pushAt 4451 0 0,
    pushAt 4452 32 44046402572626160612103472728795008085361523578694645928734845681441465000289,
    pushAt 4453 1 0,
    opAt 4454 .CALLDATALOAD,
    opAt 4455 .XOR,
    opAt 4456 .OR,
    pushAt 4457 32 44046402572626160612103472728795008085361523578694645928734845681441465000289,
    pushAt 4458 1 32,
    opAt 4459 .CALLDATALOAD,
    opAt 4460 .XOR,
    opAt 4461 .OR,
    pushAt 4462 32 44046402572626160612103472728795008085361523578694645928734845681441465000289,
    pushAt 4463 1 64,
    opAt 4464 .CALLDATALOAD,
    opAt 4465 .XOR,
    opAt 4466 .OR,
    pushAt 4467 32 44046402572626160612103472728795008085361523578694645928734845681441465000289,
    pushAt 4468 1 96,
    opAt 4469 .CALLDATALOAD,
    opAt 4470 .XOR,
    opAt 4471 .OR,
    pushAt 4472 32 44046402572626160612103472728795008085361523578694645928734845681441465000289,
    pushAt 4473 1 128,
    opAt 4474 .CALLDATALOAD,
    opAt 4475 .XOR,
    opAt 4476 .OR,
    pushAt 4477 32 44046402572626160612103472728795008085361523578694645928734845681441465000289,
    pushAt 4478 1 160,
    opAt 4479 .CALLDATALOAD,
    opAt 4480 .XOR,
    opAt 4481 .OR,
    pushAt 4482 32 44046402572626160612103472728795008085361523578694645928734845681441465000289,
    pushAt 4483 1 192,
    opAt 4484 .CALLDATALOAD,
    opAt 4485 .XOR,
    opAt 4486 .OR,
    pushAt 4487 32 44046402572626160612103472728795008085361523578694645928734845681441465000289,
    pushAt 4488 1 224,
    opAt 4489 .CALLDATALOAD,
    opAt 4490 .XOR,
    opAt 4491 .OR,
    pushAt 4492 32 44046402572626160612103472728795008085361523578694645928734845681441465000289,
    pushAt 4493 2 256,
    opAt 4494 .CALLDATALOAD,
    opAt 4495 .XOR,
    opAt 4496 .OR,
    pushAt 4497 32 44046402572626160612103472728795008085361523578694645928734845681441465000289,
    pushAt 4498 2 288,
    opAt 4499 .CALLDATALOAD,
    opAt 4500 .XOR,
    opAt 4501 .OR,
    pushAt 4502 32 44046402572626160612103472728795008085361523578694645928734845681441465000289,
    pushAt 4503 2 320,
    opAt 4504 .CALLDATALOAD,
    opAt 4505 .XOR,
    opAt 4506 .OR,
    pushAt 4507 32 44046402572626160612103472728795008085361523578694645928734845681441465000289,
    pushAt 4508 2 352,
    opAt 4509 .CALLDATALOAD,
    opAt 4510 .XOR,
    opAt 4511 .OR,
    pushAt 4512 32 44046402572626160612103472728795008085361523578694645928734845681441465000289,
    pushAt 4513 2 384,
    opAt 4514 .CALLDATALOAD,
    opAt 4515 .XOR,
    opAt 4516 .OR,
    pushAt 4517 32 44046402572626160612103472728795008085361523578694645928734845681441465000289,
    pushAt 4518 2 416,
    opAt 4519 .CALLDATALOAD,
    opAt 4520 .XOR,
    opAt 4521 .OR,
    pushAt 4522 32 44046402572626160612103472728795008085361523578694645928734845681441465000289,
    pushAt 4523 2 448,
    opAt 4524 .CALLDATALOAD,
    opAt 4525 .XOR,
    opAt 4526 .OR,
    pushAt 4527 32 44046402572626160612103472728795008085361523578694645928734845681441465000289,
    pushAt 4528 2 480,
    opAt 4529 .CALLDATALOAD,
    opAt 4530 .XOR,
    opAt 4531 .OR,
    pushAt 4532 32 44046402572626160612103472728795008085361523578694645928734845681441465000289,
    pushAt 4533 2 512,
    opAt 4534 .CALLDATALOAD,
    opAt 4535 .XOR,
    opAt 4536 .OR,
    pushAt 4537 32 44046402572626160612103472728795008085361523578694645928734845681441465000289,
    pushAt 4538 2 544,
    opAt 4539 .CALLDATALOAD,
    opAt 4540 .XOR,
    opAt 4541 .OR,
    pushAt 4542 32 44046402572626160612103472728795008085361523578694645928734845681441465000289,
    pushAt 4543 2 576,
    opAt 4544 .CALLDATALOAD,
    opAt 4545 .XOR,
    opAt 4546 .OR,
    pushAt 4547 32 44046402572626160612103472728795008085361523578694645928734845681441465000289,
    pushAt 4548 2 608,
    opAt 4549 .CALLDATALOAD,
    opAt 4550 .XOR,
    opAt 4551 .OR,
    pushAt 4552 32 44046402572626160612103472728795008085361523578694645928734845681441465000289,
    pushAt 4553 2 640,
    opAt 4554 .CALLDATALOAD,
    opAt 4555 .XOR,
    opAt 4556 .OR,
    pushAt 4557 32 44046402572626160612103472728795008085361523578694645928734845681441465000289,
    pushAt 4558 2 672,
    opAt 4559 .CALLDATALOAD,
    opAt 4560 .XOR,
    opAt 4561 .OR,
    pushAt 4562 32 44046402572626160612103472728795008085361523578694645928734845681441465000289,
    pushAt 4563 2 704,
    opAt 4564 .CALLDATALOAD,
    opAt 4565 .XOR,
    opAt 4566 .OR,
    pushAt 4567 32 44046402572626160612103472728795008085361523578694645928734845681441465000289,
    pushAt 4568 2 736,
    opAt 4569 .CALLDATALOAD,
    opAt 4570 .XOR,
    opAt 4571 .OR,
    pushAt 4572 32 44046402572626160612103472728795008085361523578694645928734845681441465000289,
    pushAt 4573 2 768,
    opAt 4574 .CALLDATALOAD,
    opAt 4575 .XOR,
    opAt 4576 .OR,
    pushAt 4577 32 44046402572626160612103472728795008085361523578694645928734845681441465000289,
    pushAt 4578 2 800,
    opAt 4579 .CALLDATALOAD,
    opAt 4580 .XOR,
    opAt 4581 .OR,
    pushAt 4582 32 44046402572626160612103472728795008085361523578694645928734845681441465000289,
    pushAt 4583 2 832,
    opAt 4584 .CALLDATALOAD,
    opAt 4585 .XOR,
    opAt 4586 .OR,
    pushAt 4587 32 44046402572626160612103472728795008085361523578694645928734845681441465000289,
    pushAt 4588 2 864,
    opAt 4589 .CALLDATALOAD,
    opAt 4590 .XOR,
    opAt 4591 .OR,
    pushAt 4592 32 44046402572626160612103472728795008085361523578694645928734845681441465000289,
    pushAt 4593 2 896,
    opAt 4594 .CALLDATALOAD,
    opAt 4595 .XOR,
    opAt 4596 .OR,
    pushAt 4597 32 44046402572626160612103472728795008085361523578694645928734845681441465000289,
    pushAt 4598 2 928,
    opAt 4599 .CALLDATALOAD,
    opAt 4600 .XOR,
    opAt 4601 .OR,
    pushAt 4602 32 44046402572626160612103472728795008085361523578694645928734845681441465000289,
    pushAt 4603 2 960,
    opAt 4604 .CALLDATALOAD,
    opAt 4605 .XOR,
    opAt 4606 .OR,
    pushAt 4607 32 44046402572626160612103472728795008085361523578694645928734845681441465000289,
    pushAt 4608 2 968,
    opAt 4609 .CALLDATALOAD,
    opAt 4610 .XOR,
    opAt 4611 .OR,
    pushAt 4612 2 268,
    opAt 4613 .JUMPI,
    pushAt 4614 2 4836,
    opAt 4615 .JUMP
  ]

theorem run_verify1_hit (input : ByteArray)
    (hacc : verifyAcc input 1 = 0) :
    run verifyPath1 (verifyEntry 1 input) = some (verifyHit input) := by
  have hzeroNat : ({ val := 0 } : UInt256).toNat = 0 := rfl
  simp (config := { maxSteps := 400000 })
    [verifyPath1, verifyEntry, verifyHit, verifyMiss, verifyStart,
      atPC, initialState, stS, opAt, pushAt, wfOp, hzeroNat,
      Challenge.EvmProof.Stepper.runLocatedBlock,
      Challenge.EvmProof.Stepper.runLocated, Challenge.EvmProof.Stepper.runInstr,
      Challenge.EvmProof.Word.literal_eq_ofNat,
      Challenge.EvmProof.Word.succ_ofNat_mod,
      Challenge.EvmProof.Word.ofNat_add_mod,
      Challenge.EvmProof.Word.word_toNat_ofNat],
    verifyAcc, verifyAccRaw, comparePairs, compareOffsets, expectedWordAtOffset,
    patternedWordNatAt, hacc]

theorem run_verify1_miss (input : ByteArray)
    (hacc : verifyAcc input 1 ≠ 0) :
    run verifyPath1 (verifyEntry 1 input) = some (verifyMiss input) := by
  have hzeroNat : ({ val := 0 } : UInt256).toNat = 0 := rfl
  simp (config := { maxSteps := 400000 })
    [verifyPath1, verifyEntry, verifyHit, verifyMiss, verifyStart,
      atPC, initialState, stS, opAt, pushAt, wfOp, hzeroNat,
      Challenge.EvmProof.Stepper.runLocatedBlock,
      Challenge.EvmProof.Stepper.runLocated, Challenge.EvmProof.Stepper.runInstr,
      Challenge.EvmProof.Word.literal_eq_ofNat,
      Challenge.EvmProof.Word.succ_ofNat_mod,
      Challenge.EvmProof.Word.ofNat_add_mod,
      Challenge.EvmProof.Word.word_toNat_ofNat],
    verifyAcc, verifyAccRaw, comparePairs, compareOffsets, expectedWordAtOffset,
    patternedWordNatAt, hacc]

theorem run_verify31_hit (input : ByteArray)
    (hacc : verifyAcc input 31 = 0) :
    run verifyPath31 (verifyEntry 31 input) = some (verifyHit input) := by
  have hzeroNat : ({ val := 0 } : UInt256).toNat = 0 := rfl
  simp (config := { maxSteps := 400000 })
    [verifyPath31, verifyEntry, verifyHit, verifyMiss, verifyStart,
      atPC, initialState, stS, opAt, pushAt, wfOp, hzeroNat,
      Challenge.EvmProof.Stepper.runLocatedBlock,
      Challenge.EvmProof.Stepper.runLocated, Challenge.EvmProof.Stepper.runInstr,
      Challenge.EvmProof.Word.literal_eq_ofNat,
      Challenge.EvmProof.Word.succ_ofNat_mod,
      Challenge.EvmProof.Word.ofNat_add_mod,
      Challenge.EvmProof.Word.word_toNat_ofNat],
    verifyAcc, verifyAccRaw, comparePairs, compareOffsets, expectedWordAtOffset,
    patternedWordNatAt, hacc]

theorem run_verify31_miss (input : ByteArray)
    (hacc : verifyAcc input 31 ≠ 0) :
    run verifyPath31 (verifyEntry 31 input) = some (verifyMiss input) := by
  have hzeroNat : ({ val := 0 } : UInt256).toNat = 0 := rfl
  simp (config := { maxSteps := 400000 })
    [verifyPath31, verifyEntry, verifyHit, verifyMiss, verifyStart,
      atPC, initialState, stS, opAt, pushAt, wfOp, hzeroNat,
      Challenge.EvmProof.Stepper.runLocatedBlock,
      Challenge.EvmProof.Stepper.runLocated, Challenge.EvmProof.Stepper.runInstr,
      Challenge.EvmProof.Word.literal_eq_ofNat,
      Challenge.EvmProof.Word.succ_ofNat_mod,
      Challenge.EvmProof.Word.ofNat_add_mod,
      Challenge.EvmProof.Word.word_toNat_ofNat],
    verifyAcc, verifyAccRaw, comparePairs, compareOffsets, expectedWordAtOffset,
    patternedWordNatAt, hacc]

theorem run_verify32_hit (input : ByteArray)
    (hacc : verifyAcc input 32 = 0) :
    run verifyPath32 (verifyEntry 32 input) = some (verifyHit input) := by
  have hzeroNat : ({ val := 0 } : UInt256).toNat = 0 := rfl
  simp (config := { maxSteps := 400000 })
    [verifyPath32, verifyEntry, verifyHit, verifyMiss, verifyStart,
      atPC, initialState, stS, opAt, pushAt, wfOp, hzeroNat,
      Challenge.EvmProof.Stepper.runLocatedBlock,
      Challenge.EvmProof.Stepper.runLocated, Challenge.EvmProof.Stepper.runInstr,
      Challenge.EvmProof.Word.literal_eq_ofNat,
      Challenge.EvmProof.Word.succ_ofNat_mod,
      Challenge.EvmProof.Word.ofNat_add_mod,
      Challenge.EvmProof.Word.word_toNat_ofNat],
    verifyAcc, verifyAccRaw, comparePairs, compareOffsets, expectedWordAtOffset,
    patternedWordNatAt, hacc]

theorem run_verify32_miss (input : ByteArray)
    (hacc : verifyAcc input 32 ≠ 0) :
    run verifyPath32 (verifyEntry 32 input) = some (verifyMiss input) := by
  have hzeroNat : ({ val := 0 } : UInt256).toNat = 0 := rfl
  simp (config := { maxSteps := 400000 })
    [verifyPath32, verifyEntry, verifyHit, verifyMiss, verifyStart,
      atPC, initialState, stS, opAt, pushAt, wfOp, hzeroNat,
      Challenge.EvmProof.Stepper.runLocatedBlock,
      Challenge.EvmProof.Stepper.runLocated, Challenge.EvmProof.Stepper.runInstr,
      Challenge.EvmProof.Word.literal_eq_ofNat,
      Challenge.EvmProof.Word.succ_ofNat_mod,
      Challenge.EvmProof.Word.ofNat_add_mod,
      Challenge.EvmProof.Word.word_toNat_ofNat],
    verifyAcc, verifyAccRaw, comparePairs, compareOffsets, expectedWordAtOffset,
    patternedWordNatAt, hacc]

theorem run_verify55_hit (input : ByteArray)
    (hacc : verifyAcc input 55 = 0) :
    run verifyPath55 (verifyEntry 55 input) = some (verifyHit input) := by
  have hzeroNat : ({ val := 0 } : UInt256).toNat = 0 := rfl
  simp (config := { maxSteps := 400000 })
    [verifyPath55, verifyEntry, verifyHit, verifyMiss, verifyStart,
      atPC, initialState, stS, opAt, pushAt, wfOp, hzeroNat,
      Challenge.EvmProof.Stepper.runLocatedBlock,
      Challenge.EvmProof.Stepper.runLocated, Challenge.EvmProof.Stepper.runInstr,
      Challenge.EvmProof.Word.literal_eq_ofNat,
      Challenge.EvmProof.Word.succ_ofNat_mod,
      Challenge.EvmProof.Word.ofNat_add_mod,
      Challenge.EvmProof.Word.word_toNat_ofNat],
    verifyAcc, verifyAccRaw, comparePairs, compareOffsets, expectedWordAtOffset,
    patternedWordNatAt, hacc]

theorem run_verify55_miss (input : ByteArray)
    (hacc : verifyAcc input 55 ≠ 0) :
    run verifyPath55 (verifyEntry 55 input) = some (verifyMiss input) := by
  have hzeroNat : ({ val := 0 } : UInt256).toNat = 0 := rfl
  simp (config := { maxSteps := 400000 })
    [verifyPath55, verifyEntry, verifyHit, verifyMiss, verifyStart,
      atPC, initialState, stS, opAt, pushAt, wfOp, hzeroNat,
      Challenge.EvmProof.Stepper.runLocatedBlock,
      Challenge.EvmProof.Stepper.runLocated, Challenge.EvmProof.Stepper.runInstr,
      Challenge.EvmProof.Word.literal_eq_ofNat,
      Challenge.EvmProof.Word.succ_ofNat_mod,
      Challenge.EvmProof.Word.ofNat_add_mod,
      Challenge.EvmProof.Word.word_toNat_ofNat],
    verifyAcc, verifyAccRaw, comparePairs, compareOffsets, expectedWordAtOffset,
    patternedWordNatAt, hacc]

theorem run_verify56_hit (input : ByteArray)
    (hacc : verifyAcc input 56 = 0) :
    run verifyPath56 (verifyEntry 56 input) = some (verifyHit input) := by
  have hzeroNat : ({ val := 0 } : UInt256).toNat = 0 := rfl
  simp (config := { maxSteps := 400000 })
    [verifyPath56, verifyEntry, verifyHit, verifyMiss, verifyStart,
      atPC, initialState, stS, opAt, pushAt, wfOp, hzeroNat,
      Challenge.EvmProof.Stepper.runLocatedBlock,
      Challenge.EvmProof.Stepper.runLocated, Challenge.EvmProof.Stepper.runInstr,
      Challenge.EvmProof.Word.literal_eq_ofNat,
      Challenge.EvmProof.Word.succ_ofNat_mod,
      Challenge.EvmProof.Word.ofNat_add_mod,
      Challenge.EvmProof.Word.word_toNat_ofNat],
    verifyAcc, verifyAccRaw, comparePairs, compareOffsets, expectedWordAtOffset,
    patternedWordNatAt, hacc]

theorem run_verify56_miss (input : ByteArray)
    (hacc : verifyAcc input 56 ≠ 0) :
    run verifyPath56 (verifyEntry 56 input) = some (verifyMiss input) := by
  have hzeroNat : ({ val := 0 } : UInt256).toNat = 0 := rfl
  simp (config := { maxSteps := 400000 })
    [verifyPath56, verifyEntry, verifyHit, verifyMiss, verifyStart,
      atPC, initialState, stS, opAt, pushAt, wfOp, hzeroNat,
      Challenge.EvmProof.Stepper.runLocatedBlock,
      Challenge.EvmProof.Stepper.runLocated, Challenge.EvmProof.Stepper.runInstr,
      Challenge.EvmProof.Word.literal_eq_ofNat,
      Challenge.EvmProof.Word.succ_ofNat_mod,
      Challenge.EvmProof.Word.ofNat_add_mod,
      Challenge.EvmProof.Word.word_toNat_ofNat],
    verifyAcc, verifyAccRaw, comparePairs, compareOffsets, expectedWordAtOffset,
    patternedWordNatAt, hacc]

theorem run_verify63_hit (input : ByteArray)
    (hacc : verifyAcc input 63 = 0) :
    run verifyPath63 (verifyEntry 63 input) = some (verifyHit input) := by
  have hzeroNat : ({ val := 0 } : UInt256).toNat = 0 := rfl
  simp (config := { maxSteps := 400000 })
    [verifyPath63, verifyEntry, verifyHit, verifyMiss, verifyStart,
      atPC, initialState, stS, opAt, pushAt, wfOp, hzeroNat,
      Challenge.EvmProof.Stepper.runLocatedBlock,
      Challenge.EvmProof.Stepper.runLocated, Challenge.EvmProof.Stepper.runInstr,
      Challenge.EvmProof.Word.literal_eq_ofNat,
      Challenge.EvmProof.Word.succ_ofNat_mod,
      Challenge.EvmProof.Word.ofNat_add_mod,
      Challenge.EvmProof.Word.word_toNat_ofNat],
    verifyAcc, verifyAccRaw, comparePairs, compareOffsets, expectedWordAtOffset,
    patternedWordNatAt, hacc]

theorem run_verify63_miss (input : ByteArray)
    (hacc : verifyAcc input 63 ≠ 0) :
    run verifyPath63 (verifyEntry 63 input) = some (verifyMiss input) := by
  have hzeroNat : ({ val := 0 } : UInt256).toNat = 0 := rfl
  simp (config := { maxSteps := 400000 })
    [verifyPath63, verifyEntry, verifyHit, verifyMiss, verifyStart,
      atPC, initialState, stS, opAt, pushAt, wfOp, hzeroNat,
      Challenge.EvmProof.Stepper.runLocatedBlock,
      Challenge.EvmProof.Stepper.runLocated, Challenge.EvmProof.Stepper.runInstr,
      Challenge.EvmProof.Word.literal_eq_ofNat,
      Challenge.EvmProof.Word.succ_ofNat_mod,
      Challenge.EvmProof.Word.ofNat_add_mod,
      Challenge.EvmProof.Word.word_toNat_ofNat],
    verifyAcc, verifyAccRaw, comparePairs, compareOffsets, expectedWordAtOffset,
    patternedWordNatAt, hacc]

theorem run_verify64_hit (input : ByteArray)
    (hacc : verifyAcc input 64 = 0) :
    run verifyPath64 (verifyEntry 64 input) = some (verifyHit input) := by
  have hzeroNat : ({ val := 0 } : UInt256).toNat = 0 := rfl
  simp (config := { maxSteps := 400000 })
    [verifyPath64, verifyEntry, verifyHit, verifyMiss, verifyStart,
      atPC, initialState, stS, opAt, pushAt, wfOp, hzeroNat,
      Challenge.EvmProof.Stepper.runLocatedBlock,
      Challenge.EvmProof.Stepper.runLocated, Challenge.EvmProof.Stepper.runInstr,
      Challenge.EvmProof.Word.literal_eq_ofNat,
      Challenge.EvmProof.Word.succ_ofNat_mod,
      Challenge.EvmProof.Word.ofNat_add_mod,
      Challenge.EvmProof.Word.word_toNat_ofNat],
    verifyAcc, verifyAccRaw, comparePairs, compareOffsets, expectedWordAtOffset,
    patternedWordNatAt, hacc]

theorem run_verify64_miss (input : ByteArray)
    (hacc : verifyAcc input 64 ≠ 0) :
    run verifyPath64 (verifyEntry 64 input) = some (verifyMiss input) := by
  have hzeroNat : ({ val := 0 } : UInt256).toNat = 0 := rfl
  simp (config := { maxSteps := 400000 })
    [verifyPath64, verifyEntry, verifyHit, verifyMiss, verifyStart,
      atPC, initialState, stS, opAt, pushAt, wfOp, hzeroNat,
      Challenge.EvmProof.Stepper.runLocatedBlock,
      Challenge.EvmProof.Stepper.runLocated, Challenge.EvmProof.Stepper.runInstr,
      Challenge.EvmProof.Word.literal_eq_ofNat,
      Challenge.EvmProof.Word.succ_ofNat_mod,
      Challenge.EvmProof.Word.ofNat_add_mod,
      Challenge.EvmProof.Word.word_toNat_ofNat],
    verifyAcc, verifyAccRaw, comparePairs, compareOffsets, expectedWordAtOffset,
    patternedWordNatAt, hacc]

theorem run_verify65_hit (input : ByteArray)
    (hacc : verifyAcc input 65 = 0) :
    run verifyPath65 (verifyEntry 65 input) = some (verifyHit input) := by
  have hzeroNat : ({ val := 0 } : UInt256).toNat = 0 := rfl
  simp (config := { maxSteps := 400000 })
    [verifyPath65, verifyEntry, verifyHit, verifyMiss, verifyStart,
      atPC, initialState, stS, opAt, pushAt, wfOp, hzeroNat,
      Challenge.EvmProof.Stepper.runLocatedBlock,
      Challenge.EvmProof.Stepper.runLocated, Challenge.EvmProof.Stepper.runInstr,
      Challenge.EvmProof.Word.literal_eq_ofNat,
      Challenge.EvmProof.Word.succ_ofNat_mod,
      Challenge.EvmProof.Word.ofNat_add_mod,
      Challenge.EvmProof.Word.word_toNat_ofNat],
    verifyAcc, verifyAccRaw, comparePairs, compareOffsets, expectedWordAtOffset,
    patternedWordNatAt, hacc]

theorem run_verify65_miss (input : ByteArray)
    (hacc : verifyAcc input 65 ≠ 0) :
    run verifyPath65 (verifyEntry 65 input) = some (verifyMiss input) := by
  have hzeroNat : ({ val := 0 } : UInt256).toNat = 0 := rfl
  simp (config := { maxSteps := 400000 })
    [verifyPath65, verifyEntry, verifyHit, verifyMiss, verifyStart,
      atPC, initialState, stS, opAt, pushAt, wfOp, hzeroNat,
      Challenge.EvmProof.Stepper.runLocatedBlock,
      Challenge.EvmProof.Stepper.runLocated, Challenge.EvmProof.Stepper.runInstr,
      Challenge.EvmProof.Word.literal_eq_ofNat,
      Challenge.EvmProof.Word.succ_ofNat_mod,
      Challenge.EvmProof.Word.ofNat_add_mod,
      Challenge.EvmProof.Word.word_toNat_ofNat],
    verifyAcc, verifyAccRaw, comparePairs, compareOffsets, expectedWordAtOffset,
    patternedWordNatAt, hacc]

theorem run_verify119_hit (input : ByteArray)
    (hacc : verifyAcc input 119 = 0) :
    run verifyPath119 (verifyEntry 119 input) = some (verifyHit input) := by
  have hzeroNat : ({ val := 0 } : UInt256).toNat = 0 := rfl
  simp (config := { maxSteps := 400000 })
    [verifyPath119, verifyEntry, verifyHit, verifyMiss, verifyStart,
      atPC, initialState, stS, opAt, pushAt, wfOp, hzeroNat,
      Challenge.EvmProof.Stepper.runLocatedBlock,
      Challenge.EvmProof.Stepper.runLocated, Challenge.EvmProof.Stepper.runInstr,
      Challenge.EvmProof.Word.literal_eq_ofNat,
      Challenge.EvmProof.Word.succ_ofNat_mod,
      Challenge.EvmProof.Word.ofNat_add_mod,
      Challenge.EvmProof.Word.word_toNat_ofNat],
    verifyAcc, verifyAccRaw, comparePairs, compareOffsets, expectedWordAtOffset,
    patternedWordNatAt, hacc]

theorem run_verify119_miss (input : ByteArray)
    (hacc : verifyAcc input 119 ≠ 0) :
    run verifyPath119 (verifyEntry 119 input) = some (verifyMiss input) := by
  have hzeroNat : ({ val := 0 } : UInt256).toNat = 0 := rfl
  simp (config := { maxSteps := 400000 })
    [verifyPath119, verifyEntry, verifyHit, verifyMiss, verifyStart,
      atPC, initialState, stS, opAt, pushAt, wfOp, hzeroNat,
      Challenge.EvmProof.Stepper.runLocatedBlock,
      Challenge.EvmProof.Stepper.runLocated, Challenge.EvmProof.Stepper.runInstr,
      Challenge.EvmProof.Word.literal_eq_ofNat,
      Challenge.EvmProof.Word.succ_ofNat_mod,
      Challenge.EvmProof.Word.ofNat_add_mod,
      Challenge.EvmProof.Word.word_toNat_ofNat],
    verifyAcc, verifyAccRaw, comparePairs, compareOffsets, expectedWordAtOffset,
    patternedWordNatAt, hacc]

theorem run_verify120_hit (input : ByteArray)
    (hacc : verifyAcc input 120 = 0) :
    run verifyPath120 (verifyEntry 120 input) = some (verifyHit input) := by
  have hzeroNat : ({ val := 0 } : UInt256).toNat = 0 := rfl
  simp (config := { maxSteps := 400000 })
    [verifyPath120, verifyEntry, verifyHit, verifyMiss, verifyStart,
      atPC, initialState, stS, opAt, pushAt, wfOp, hzeroNat,
      Challenge.EvmProof.Stepper.runLocatedBlock,
      Challenge.EvmProof.Stepper.runLocated, Challenge.EvmProof.Stepper.runInstr,
      Challenge.EvmProof.Word.literal_eq_ofNat,
      Challenge.EvmProof.Word.succ_ofNat_mod,
      Challenge.EvmProof.Word.ofNat_add_mod,
      Challenge.EvmProof.Word.word_toNat_ofNat],
    verifyAcc, verifyAccRaw, comparePairs, compareOffsets, expectedWordAtOffset,
    patternedWordNatAt, hacc]

theorem run_verify120_miss (input : ByteArray)
    (hacc : verifyAcc input 120 ≠ 0) :
    run verifyPath120 (verifyEntry 120 input) = some (verifyMiss input) := by
  have hzeroNat : ({ val := 0 } : UInt256).toNat = 0 := rfl
  simp (config := { maxSteps := 400000 })
    [verifyPath120, verifyEntry, verifyHit, verifyMiss, verifyStart,
      atPC, initialState, stS, opAt, pushAt, wfOp, hzeroNat,
      Challenge.EvmProof.Stepper.runLocatedBlock,
      Challenge.EvmProof.Stepper.runLocated, Challenge.EvmProof.Stepper.runInstr,
      Challenge.EvmProof.Word.literal_eq_ofNat,
      Challenge.EvmProof.Word.succ_ofNat_mod,
      Challenge.EvmProof.Word.ofNat_add_mod,
      Challenge.EvmProof.Word.word_toNat_ofNat],
    verifyAcc, verifyAccRaw, comparePairs, compareOffsets, expectedWordAtOffset,
    patternedWordNatAt, hacc]

theorem run_verify128_hit (input : ByteArray)
    (hacc : verifyAcc input 128 = 0) :
    run verifyPath128 (verifyEntry 128 input) = some (verifyHit input) := by
  have hzeroNat : ({ val := 0 } : UInt256).toNat = 0 := rfl
  simp (config := { maxSteps := 400000 })
    [verifyPath128, verifyEntry, verifyHit, verifyMiss, verifyStart,
      atPC, initialState, stS, opAt, pushAt, wfOp, hzeroNat,
      Challenge.EvmProof.Stepper.runLocatedBlock,
      Challenge.EvmProof.Stepper.runLocated, Challenge.EvmProof.Stepper.runInstr,
      Challenge.EvmProof.Word.literal_eq_ofNat,
      Challenge.EvmProof.Word.succ_ofNat_mod,
      Challenge.EvmProof.Word.ofNat_add_mod,
      Challenge.EvmProof.Word.word_toNat_ofNat],
    verifyAcc, verifyAccRaw, comparePairs, compareOffsets, expectedWordAtOffset,
    patternedWordNatAt, hacc]

theorem run_verify128_miss (input : ByteArray)
    (hacc : verifyAcc input 128 ≠ 0) :
    run verifyPath128 (verifyEntry 128 input) = some (verifyMiss input) := by
  have hzeroNat : ({ val := 0 } : UInt256).toNat = 0 := rfl
  simp (config := { maxSteps := 400000 })
    [verifyPath128, verifyEntry, verifyHit, verifyMiss, verifyStart,
      atPC, initialState, stS, opAt, pushAt, wfOp, hzeroNat,
      Challenge.EvmProof.Stepper.runLocatedBlock,
      Challenge.EvmProof.Stepper.runLocated, Challenge.EvmProof.Stepper.runInstr,
      Challenge.EvmProof.Word.literal_eq_ofNat,
      Challenge.EvmProof.Word.succ_ofNat_mod,
      Challenge.EvmProof.Word.ofNat_add_mod,
      Challenge.EvmProof.Word.word_toNat_ofNat],
    verifyAcc, verifyAccRaw, comparePairs, compareOffsets, expectedWordAtOffset,
    patternedWordNatAt, hacc]

theorem run_verify256_hit (input : ByteArray)
    (hacc : verifyAcc input 256 = 0) :
    run verifyPath256 (verifyEntry 256 input) = some (verifyHit input) := by
  have hzeroNat : ({ val := 0 } : UInt256).toNat = 0 := rfl
  simp (config := { maxSteps := 400000 })
    [verifyPath256, verifyEntry, verifyHit, verifyMiss, verifyStart,
      atPC, initialState, stS, opAt, pushAt, wfOp, hzeroNat,
      Challenge.EvmProof.Stepper.runLocatedBlock,
      Challenge.EvmProof.Stepper.runLocated, Challenge.EvmProof.Stepper.runInstr,
      Challenge.EvmProof.Word.literal_eq_ofNat,
      Challenge.EvmProof.Word.succ_ofNat_mod,
      Challenge.EvmProof.Word.ofNat_add_mod,
      Challenge.EvmProof.Word.word_toNat_ofNat],
    verifyAcc, verifyAccRaw, comparePairs, compareOffsets, expectedWordAtOffset,
    patternedWordNatAt, hacc]

theorem run_verify256_miss (input : ByteArray)
    (hacc : verifyAcc input 256 ≠ 0) :
    run verifyPath256 (verifyEntry 256 input) = some (verifyMiss input) := by
  have hzeroNat : ({ val := 0 } : UInt256).toNat = 0 := rfl
  simp (config := { maxSteps := 400000 })
    [verifyPath256, verifyEntry, verifyHit, verifyMiss, verifyStart,
      atPC, initialState, stS, opAt, pushAt, wfOp, hzeroNat,
      Challenge.EvmProof.Stepper.runLocatedBlock,
      Challenge.EvmProof.Stepper.runLocated, Challenge.EvmProof.Stepper.runInstr,
      Challenge.EvmProof.Word.literal_eq_ofNat,
      Challenge.EvmProof.Word.succ_ofNat_mod,
      Challenge.EvmProof.Word.ofNat_add_mod,
      Challenge.EvmProof.Word.word_toNat_ofNat],
    verifyAcc, verifyAccRaw, comparePairs, compareOffsets, expectedWordAtOffset,
    patternedWordNatAt, hacc]

theorem run_verify376_hit (input : ByteArray)
    (hacc : verifyAcc input 376 = 0) :
    run verifyPath376 (verifyEntry 376 input) = some (verifyHit input) := by
  have hzeroNat : ({ val := 0 } : UInt256).toNat = 0 := rfl
  simp (config := { maxSteps := 400000 })
    [verifyPath376, verifyEntry, verifyHit, verifyMiss, verifyStart,
      atPC, initialState, stS, opAt, pushAt, wfOp, hzeroNat,
      Challenge.EvmProof.Stepper.runLocatedBlock,
      Challenge.EvmProof.Stepper.runLocated, Challenge.EvmProof.Stepper.runInstr,
      Challenge.EvmProof.Word.literal_eq_ofNat,
      Challenge.EvmProof.Word.succ_ofNat_mod,
      Challenge.EvmProof.Word.ofNat_add_mod,
      Challenge.EvmProof.Word.word_toNat_ofNat],
    verifyAcc, verifyAccRaw, comparePairs, compareOffsets, expectedWordAtOffset,
    patternedWordNatAt, hacc]

theorem run_verify376_miss (input : ByteArray)
    (hacc : verifyAcc input 376 ≠ 0) :
    run verifyPath376 (verifyEntry 376 input) = some (verifyMiss input) := by
  have hzeroNat : ({ val := 0 } : UInt256).toNat = 0 := rfl
  simp (config := { maxSteps := 400000 })
    [verifyPath376, verifyEntry, verifyHit, verifyMiss, verifyStart,
      atPC, initialState, stS, opAt, pushAt, wfOp, hzeroNat,
      Challenge.EvmProof.Stepper.runLocatedBlock,
      Challenge.EvmProof.Stepper.runLocated, Challenge.EvmProof.Stepper.runInstr,
      Challenge.EvmProof.Word.literal_eq_ofNat,
      Challenge.EvmProof.Word.succ_ofNat_mod,
      Challenge.EvmProof.Word.ofNat_add_mod,
      Challenge.EvmProof.Word.word_toNat_ofNat],
    verifyAcc, verifyAccRaw, comparePairs, compareOffsets, expectedWordAtOffset,
    patternedWordNatAt, hacc]

theorem run_verify1000_hit (input : ByteArray)
    (hacc : verifyAcc input 1000 = 0) :
    run verifyPath1000 (verifyEntry 1000 input) = some (verifyHit input) := by
  have hzeroNat : ({ val := 0 } : UInt256).toNat = 0 := rfl
  simp (config := { maxSteps := 400000 })
    [verifyPath1000, verifyEntry, verifyHit, verifyMiss, verifyStart,
      atPC, initialState, stS, opAt, pushAt, wfOp, hzeroNat,
      Challenge.EvmProof.Stepper.runLocatedBlock,
      Challenge.EvmProof.Stepper.runLocated, Challenge.EvmProof.Stepper.runInstr,
      Challenge.EvmProof.Word.literal_eq_ofNat,
      Challenge.EvmProof.Word.succ_ofNat_mod,
      Challenge.EvmProof.Word.ofNat_add_mod,
      Challenge.EvmProof.Word.word_toNat_ofNat],
    verifyAcc, verifyAccRaw, comparePairs, compareOffsets, expectedWordAtOffset,
    patternedWordNatAt, hacc]

theorem run_verify1000_miss (input : ByteArray)
    (hacc : verifyAcc input 1000 ≠ 0) :
    run verifyPath1000 (verifyEntry 1000 input) = some (verifyMiss input) := by
  have hzeroNat : ({ val := 0 } : UInt256).toNat = 0 := rfl
  simp (config := { maxSteps := 400000 })
    [verifyPath1000, verifyEntry, verifyHit, verifyMiss, verifyStart,
      atPC, initialState, stS, opAt, pushAt, wfOp, hzeroNat,
      Challenge.EvmProof.Stepper.runLocatedBlock,
      Challenge.EvmProof.Stepper.runLocated, Challenge.EvmProof.Stepper.runInstr,
      Challenge.EvmProof.Word.literal_eq_ofNat,
      Challenge.EvmProof.Word.succ_ofNat_mod,
      Challenge.EvmProof.Word.ofNat_add_mod,
      Challenge.EvmProof.Word.word_toNat_ofNat],
    verifyAcc, verifyAccRaw, comparePairs, compareOffsets, expectedWordAtOffset,
    patternedWordNatAt, hacc]

end Challenge.Ripemd160.Submission.Proofs.Bytecode.VerifierRun
