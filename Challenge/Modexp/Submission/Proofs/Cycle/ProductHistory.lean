import Challenge.Modexp.Submission.Proofs.Cycle.KernelContract
    set_option warningAsError true
    set_option linter.unusedVariables false
    set_option maxRecDepth 20000
    set_option maxHeartbeats 6000000
    namespace CycleSubmission.WordHistory
    open EvmSemantics CycleSubmission.WordArithmetic CycleSubmission.ColumnWords
    open CycleSubmission.KernelContract
    
def productC0 (inv : UInt256) (a b n : Nat → UInt256) : UInt256 := UInt256.ofNat 0

def productQ0 (inv : UInt256) (a b n : Nat → UInt256) : UInt256 := (UInt256.land (UInt256.ofNat (2^240-1)) (inv * ((a 0) * (b 0))))

def productC1 (inv : UInt256) (a b n : Nat → UInt256) : UInt256 := (UInt256.mulMod (UInt256.ofNat 2048) ((UInt256.mulMod (n 0) (productQ0 inv a b n) P) + (UInt256.mulMod (a 0) (b 0) P)) P)

def productQ1 (inv : UInt256) (a b n : Nat → UInt256) : UInt256 := (UInt256.land (UInt256.ofNat (2^240-1)) ((((productQ0 inv a b n) * (n 1)) + (((b 0) * (a 1)) + (((b 1) * (a 0)) + (productC1 inv a b n)))) * inv))

def productC2 (inv : UInt256) (a b n : Nat → UInt256) : UInt256 := (UInt256.mulMod (UInt256.ofNat 2048) ((UInt256.mulMod (productQ1 inv a b n) (n 0) P) + ((UInt256.mulMod (productQ0 inv a b n) (n 1) P) + ((UInt256.mulMod (b 0) (a 1) P) + ((UInt256.mulMod (b 1) (a 0) P) + (productC1 inv a b n))))) P)

def productQ2 (inv : UInt256) (a b n : Nat → UInt256) : UInt256 := (UInt256.land (UInt256.ofNat (2^240-1)) ((((productQ1 inv a b n) * (n 1)) + (((productQ0 inv a b n) * (n 2)) + (((b 0) * (a 2)) + (((b 1) * (a 1)) + (((b 2) * (a 0)) + (productC2 inv a b n)))))) * inv))

def productC3 (inv : UInt256) (a b n : Nat → UInt256) : UInt256 := (UInt256.mulMod (UInt256.ofNat 2048) ((UInt256.mulMod (productQ2 inv a b n) (n 0) P) + ((UInt256.mulMod (productQ1 inv a b n) (n 1) P) + ((UInt256.mulMod (productQ0 inv a b n) (n 2) P) + ((UInt256.mulMod (b 0) (a 2) P) + ((UInt256.mulMod (b 1) (a 1) P) + ((UInt256.mulMod (b 2) (a 0) P) + (productC2 inv a b n))))))) P)

def productQ3 (inv : UInt256) (a b n : Nat → UInt256) : UInt256 := (UInt256.land (UInt256.ofNat (2^240-1)) ((((productQ2 inv a b n) * (n 1)) + (((productQ1 inv a b n) * (n 2)) + (((productQ0 inv a b n) * (n 3)) + (((b 0) * (a 3)) + (((b 1) * (a 2)) + (((b 2) * (a 1)) + (((b 3) * (a 0)) + (productC3 inv a b n)))))))) * inv))

def productC4 (inv : UInt256) (a b n : Nat → UInt256) : UInt256 := (UInt256.mulMod (UInt256.ofNat 2048) ((UInt256.mulMod (productQ3 inv a b n) (n 0) P) + ((UInt256.mulMod (productQ2 inv a b n) (n 1) P) + ((UInt256.mulMod (productQ1 inv a b n) (n 2) P) + ((UInt256.mulMod (productQ0 inv a b n) (n 3) P) + ((UInt256.mulMod (b 0) (a 3) P) + ((UInt256.mulMod (b 1) (a 2) P) + ((UInt256.mulMod (b 2) (a 1) P) + ((UInt256.mulMod (b 3) (a 0) P) + (productC3 inv a b n))))))))) P)

def productQ4 (inv : UInt256) (a b n : Nat → UInt256) : UInt256 := (UInt256.land (UInt256.ofNat (2^240-1)) ((((productQ3 inv a b n) * (n 1)) + (((productQ2 inv a b n) * (n 2)) + (((productQ1 inv a b n) * (n 3)) + (((productQ0 inv a b n) * (n 4)) + (((b 0) * (a 4)) + (((b 1) * (a 3)) + (((b 2) * (a 2)) + (((b 3) * (a 1)) + (((b 4) * (a 0)) + (productC4 inv a b n)))))))))) * inv))

def productC5 (inv : UInt256) (a b n : Nat → UInt256) : UInt256 := (UInt256.mulMod (UInt256.ofNat 2048) ((UInt256.mulMod (productQ4 inv a b n) (n 0) P) + ((UInt256.mulMod (productQ3 inv a b n) (n 1) P) + ((UInt256.mulMod (productQ2 inv a b n) (n 2) P) + ((UInt256.mulMod (productQ1 inv a b n) (n 3) P) + ((UInt256.mulMod (productQ0 inv a b n) (n 4) P) + ((UInt256.mulMod (b 0) (a 4) P) + ((UInt256.mulMod (b 1) (a 3) P) + ((UInt256.mulMod (b 2) (a 2) P) + ((UInt256.mulMod (b 3) (a 1) P) + ((UInt256.mulMod (b 4) (a 0) P) + (productC4 inv a b n))))))))))) P)

def productQ5 (inv : UInt256) (a b n : Nat → UInt256) : UInt256 := (UInt256.land (UInt256.ofNat (2^240-1)) ((((productQ4 inv a b n) * (n 1)) + (((productQ3 inv a b n) * (n 2)) + (((productQ2 inv a b n) * (n 3)) + (((productQ1 inv a b n) * (n 4)) + (((productQ0 inv a b n) * (n 5)) + (((b 0) * (a 5)) + (((b 1) * (a 4)) + (((b 2) * (a 3)) + (((b 3) * (a 2)) + (((b 4) * (a 1)) + (((b 5) * (a 0)) + (productC5 inv a b n)))))))))))) * inv))

def productC6 (inv : UInt256) (a b n : Nat → UInt256) : UInt256 := (UInt256.mulMod (UInt256.ofNat 2048) ((UInt256.mulMod (productQ5 inv a b n) (n 0) P) + ((UInt256.mulMod (productQ4 inv a b n) (n 1) P) + ((UInt256.mulMod (productQ3 inv a b n) (n 2) P) + ((UInt256.mulMod (productQ2 inv a b n) (n 3) P) + ((UInt256.mulMod (productQ1 inv a b n) (n 4) P) + ((UInt256.mulMod (productQ0 inv a b n) (n 5) P) + ((UInt256.mulMod (b 0) (a 5) P) + ((UInt256.mulMod (b 1) (a 4) P) + ((UInt256.mulMod (b 2) (a 3) P) + ((UInt256.mulMod (b 3) (a 2) P) + ((UInt256.mulMod (b 4) (a 1) P) + ((UInt256.mulMod (b 5) (a 0) P) + (productC5 inv a b n))))))))))))) P)

def productQ6 (inv : UInt256) (a b n : Nat → UInt256) : UInt256 := (UInt256.land (UInt256.ofNat (2^240-1)) ((((productQ5 inv a b n) * (n 1)) + (((productQ4 inv a b n) * (n 2)) + (((productQ3 inv a b n) * (n 3)) + (((productQ2 inv a b n) * (n 4)) + (((productQ1 inv a b n) * (n 5)) + (((productQ0 inv a b n) * (n 6)) + (((b 0) * (a 6)) + (((b 1) * (a 5)) + (((b 2) * (a 4)) + (((b 3) * (a 3)) + (((b 4) * (a 2)) + (((b 5) * (a 1)) + (((b 6) * (a 0)) + (productC6 inv a b n)))))))))))))) * inv))

def productC7 (inv : UInt256) (a b n : Nat → UInt256) : UInt256 := (UInt256.mulMod (UInt256.ofNat 2048) ((UInt256.mulMod (productQ6 inv a b n) (n 0) P) + ((UInt256.mulMod (productQ5 inv a b n) (n 1) P) + ((UInt256.mulMod (productQ4 inv a b n) (n 2) P) + ((UInt256.mulMod (productQ3 inv a b n) (n 3) P) + ((UInt256.mulMod (productQ2 inv a b n) (n 4) P) + ((UInt256.mulMod (productQ1 inv a b n) (n 5) P) + ((UInt256.mulMod (productQ0 inv a b n) (n 6) P) + ((UInt256.mulMod (b 0) (a 6) P) + ((UInt256.mulMod (b 1) (a 5) P) + ((UInt256.mulMod (b 2) (a 4) P) + ((UInt256.mulMod (b 3) (a 3) P) + ((UInt256.mulMod (b 4) (a 2) P) + ((UInt256.mulMod (b 5) (a 1) P) + ((UInt256.mulMod (b 6) (a 0) P) + (productC6 inv a b n))))))))))))))) P)

def productQ7 (inv : UInt256) (a b n : Nat → UInt256) : UInt256 := (UInt256.land (UInt256.ofNat (2^240-1)) ((((productQ6 inv a b n) * (n 1)) + (((productQ5 inv a b n) * (n 2)) + (((productQ4 inv a b n) * (n 3)) + (((productQ3 inv a b n) * (n 4)) + (((productQ2 inv a b n) * (n 5)) + (((productQ1 inv a b n) * (n 6)) + (((n 7) * (productQ0 inv a b n)) + (((b 0) * (a 7)) + (((b 1) * (a 6)) + (((b 2) * (a 5)) + (((b 3) * (a 4)) + (((b 4) * (a 3)) + (((b 5) * (a 2)) + (((b 6) * (a 1)) + (((b 7) * (a 0)) + (productC7 inv a b n)))))))))))))))) * inv))

def productC8 (inv : UInt256) (a b n : Nat → UInt256) : UInt256 := (UInt256.mulMod (UInt256.ofNat 2048) ((UInt256.mulMod (productQ7 inv a b n) (n 0) P) + ((UInt256.mulMod (productQ6 inv a b n) (n 1) P) + ((UInt256.mulMod (productQ5 inv a b n) (n 2) P) + ((UInt256.mulMod (productQ4 inv a b n) (n 3) P) + ((UInt256.mulMod (productQ3 inv a b n) (n 4) P) + ((UInt256.mulMod (productQ2 inv a b n) (n 5) P) + ((UInt256.mulMod (productQ1 inv a b n) (n 6) P) + ((UInt256.mulMod (n 7) (productQ0 inv a b n) P) + ((UInt256.mulMod (b 0) (a 7) P) + ((UInt256.mulMod (b 1) (a 6) P) + ((UInt256.mulMod (b 2) (a 5) P) + ((UInt256.mulMod (b 3) (a 4) P) + ((UInt256.mulMod (b 4) (a 3) P) + ((UInt256.mulMod (b 5) (a 2) P) + ((UInt256.mulMod (b 6) (a 1) P) + ((UInt256.mulMod (b 7) (a 0) P) + (productC7 inv a b n))))))))))))))))) P)

def productQ8 (inv : UInt256) (a b n : Nat → UInt256) : UInt256 := (UInt256.land ((((n 1) * (productQ7 inv a b n)) + (((productQ6 inv a b n) * (n 2)) + (((n 3) * (productQ5 inv a b n)) + (((n 4) * (productQ4 inv a b n)) + (((n 5) * (productQ3 inv a b n)) + (((n 6) * (productQ2 inv a b n)) + (((n 7) * (productQ1 inv a b n)) + (((n 8) * (productQ0 inv a b n)) + (((b 0) * (a 8)) + (((b 1) * (a 7)) + (((b 2) * (a 6)) + (((b 3) * (a 5)) + (((b 4) * (a 4)) + (((b 5) * (a 3)) + (((b 6) * (a 2)) + (((b 7) * (a 1)) + (((b 8) * (a 0)) + (productC8 inv a b n)))))))))))))))))) * inv) (UInt256.ofNat (2^240-1)))

def productC9 (inv : UInt256) (a b n : Nat → UInt256) : UInt256 := (UInt256.mulMod (UInt256.ofNat 2048) ((UInt256.mulMod (n 0) (productQ8 inv a b n) P) + ((UInt256.mulMod (n 1) (productQ7 inv a b n) P) + ((UInt256.mulMod (productQ6 inv a b n) (n 2) P) + ((UInt256.mulMod (productQ5 inv a b n) (n 3) P) + ((UInt256.mulMod (n 4) (productQ4 inv a b n) P) + ((UInt256.mulMod (n 5) (productQ3 inv a b n) P) + ((UInt256.mulMod (n 6) (productQ2 inv a b n) P) + ((UInt256.mulMod (n 7) (productQ1 inv a b n) P) + ((UInt256.mulMod (n 8) (productQ0 inv a b n) P) + ((UInt256.mulMod (b 0) (a 8) P) + ((UInt256.mulMod (b 1) (a 7) P) + ((UInt256.mulMod (b 2) (a 6) P) + ((UInt256.mulMod (b 3) (a 5) P) + ((UInt256.mulMod (b 4) (a 4) P) + ((UInt256.mulMod (b 5) (a 3) P) + ((UInt256.mulMod (b 6) (a 2) P) + ((UInt256.mulMod (b 7) (a 1) P) + ((UInt256.mulMod (b 8) (a 0) P) + (productC8 inv a b n))))))))))))))))))) P)

def productD0 (inv : UInt256) (a b n : Nat → UInt256) : UInt256 := (UInt256.land (UInt256.ofNat (2^240-1)) (((n 1) * (productQ8 inv a b n)) + (((productQ7 inv a b n) * (n 2)) + (((n 3) * (productQ6 inv a b n)) + (((n 4) * (productQ5 inv a b n)) + (((n 5) * (productQ4 inv a b n)) + (((n 6) * (productQ3 inv a b n)) + (((n 7) * (productQ2 inv a b n)) + (((n 8) * (productQ1 inv a b n)) + (((b 1) * (a 8)) + (((b 2) * (a 7)) + (((b 3) * (a 6)) + (((b 4) * (a 5)) + (((b 5) * (a 4)) + (((b 6) * (a 3)) + (((b 7) * (a 2)) + (((b 8) * (a 1)) + (productC9 inv a b n))))))))))))))))))

def productC10 (inv : UInt256) (a b n : Nat → UInt256) : UInt256 := (CycleSubmission.DirectRecovery.carry ((UInt256.mulMod (n 1) (productQ8 inv a b n) P) + ((UInt256.mulMod (productQ7 inv a b n) (n 2) P) + ((UInt256.mulMod (productQ6 inv a b n) (n 3) P) + ((UInt256.mulMod (n 4) (productQ5 inv a b n) P) + ((UInt256.mulMod (n 5) (productQ4 inv a b n) P) + ((UInt256.mulMod (n 6) (productQ3 inv a b n) P) + ((UInt256.mulMod (n 7) (productQ2 inv a b n) P) + ((UInt256.mulMod (n 8) (productQ1 inv a b n) P) + ((UInt256.mulMod (b 1) (a 8) P) + ((UInt256.mulMod (b 2) (a 7) P) + ((UInt256.mulMod (b 3) (a 6) P) + ((UInt256.mulMod (b 4) (a 5) P) + ((UInt256.mulMod (b 5) (a 4) P) + ((UInt256.mulMod (b 6) (a 3) P) + ((UInt256.mulMod (b 7) (a 2) P) + ((UInt256.mulMod (b 8) (a 1) P) + (productC9 inv a b n))))))))))))))))) (((n 1) * (productQ8 inv a b n)) + (((productQ7 inv a b n) * (n 2)) + (((n 3) * (productQ6 inv a b n)) + (((n 4) * (productQ5 inv a b n)) + (((n 5) * (productQ4 inv a b n)) + (((n 6) * (productQ3 inv a b n)) + (((n 7) * (productQ2 inv a b n)) + (((n 8) * (productQ1 inv a b n)) + (((b 1) * (a 8)) + (((b 2) * (a 7)) + (((b 3) * (a 6)) + (((b 4) * (a 5)) + (((b 5) * (a 4)) + (((b 6) * (a 3)) + (((b 7) * (a 2)) + (((b 8) * (a 1)) + (productC9 inv a b n))))))))))))))))))

def productC11 (inv : UInt256) (a b n : Nat → UInt256) : UInt256 := (CycleSubmission.DirectRecovery.carry ((UInt256.mulMod (productQ8 inv a b n) (n 2) P) + ((UInt256.mulMod (productQ7 inv a b n) (n 3) P) + ((UInt256.mulMod (n 4) (productQ6 inv a b n) P) + ((UInt256.mulMod (n 5) (productQ5 inv a b n) P) + ((UInt256.mulMod (n 6) (productQ4 inv a b n) P) + ((UInt256.mulMod (n 7) (productQ3 inv a b n) P) + ((UInt256.mulMod (n 8) (productQ2 inv a b n) P) + ((UInt256.mulMod (b 2) (a 8) P) + ((UInt256.mulMod (b 3) (a 7) P) + ((UInt256.mulMod (b 4) (a 6) P) + ((UInt256.mulMod (b 5) (a 5) P) + ((UInt256.mulMod (b 6) (a 4) P) + ((UInt256.mulMod (b 7) (a 3) P) + ((UInt256.mulMod (a 2) (b 8) P) + (productC10 inv a b n))))))))))))))) (((productQ8 inv a b n) * (n 2)) + (((n 3) * (productQ7 inv a b n)) + (((n 4) * (productQ6 inv a b n)) + (((n 5) * (productQ5 inv a b n)) + (((n 6) * (productQ4 inv a b n)) + (((n 7) * (productQ3 inv a b n)) + (((n 8) * (productQ2 inv a b n)) + (((b 2) * (a 8)) + (((b 3) * (a 7)) + (((b 4) * (a 6)) + (((b 5) * (a 5)) + (((b 6) * (a 4)) + (((b 7) * (a 3)) + (((a 2) * (b 8)) + (productC10 inv a b n))))))))))))))))

def productD1 (inv : UInt256) (a b n : Nat → UInt256) : UInt256 := (UInt256.land (((productQ8 inv a b n) * (n 2)) + (((n 3) * (productQ7 inv a b n)) + (((n 4) * (productQ6 inv a b n)) + (((n 5) * (productQ5 inv a b n)) + (((n 6) * (productQ4 inv a b n)) + (((n 7) * (productQ3 inv a b n)) + (((n 8) * (productQ2 inv a b n)) + (((b 2) * (a 8)) + (((b 3) * (a 7)) + (((b 4) * (a 6)) + (((b 5) * (a 5)) + (((b 6) * (a 4)) + (((b 7) * (a 3)) + (((a 2) * (b 8)) + (productC10 inv a b n))))))))))))))) (UInt256.ofNat (2^240-1)))

def productC12 (inv : UInt256) (a b n : Nat → UInt256) : UInt256 := (CycleSubmission.DirectRecovery.carry ((UInt256.mulMod (productQ8 inv a b n) (n 3) P) + ((UInt256.mulMod (n 4) (productQ7 inv a b n) P) + ((UInt256.mulMod (n 5) (productQ6 inv a b n) P) + ((UInt256.mulMod (n 6) (productQ5 inv a b n) P) + ((UInt256.mulMod (n 7) (productQ4 inv a b n) P) + ((UInt256.mulMod (n 8) (productQ3 inv a b n) P) + ((UInt256.mulMod (b 3) (a 8) P) + ((UInt256.mulMod (b 4) (a 7) P) + ((UInt256.mulMod (b 5) (a 6) P) + ((UInt256.mulMod (b 6) (a 5) P) + ((UInt256.mulMod (b 7) (a 4) P) + ((UInt256.mulMod (b 8) (a 3) P) + (productC11 inv a b n))))))))))))) (((n 3) * (productQ8 inv a b n)) + (((n 4) * (productQ7 inv a b n)) + (((n 5) * (productQ6 inv a b n)) + (((n 6) * (productQ5 inv a b n)) + (((n 7) * (productQ4 inv a b n)) + (((n 8) * (productQ3 inv a b n)) + (((b 3) * (a 8)) + (((b 4) * (a 7)) + (((b 5) * (a 6)) + (((b 6) * (a 5)) + (((b 7) * (a 4)) + (((b 8) * (a 3)) + (productC11 inv a b n))))))))))))))

def productD2 (inv : UInt256) (a b n : Nat → UInt256) : UInt256 := (UInt256.land (((n 3) * (productQ8 inv a b n)) + (((n 4) * (productQ7 inv a b n)) + (((n 5) * (productQ6 inv a b n)) + (((n 6) * (productQ5 inv a b n)) + (((n 7) * (productQ4 inv a b n)) + (((n 8) * (productQ3 inv a b n)) + (((b 3) * (a 8)) + (((b 4) * (a 7)) + (((b 5) * (a 6)) + (((b 6) * (a 5)) + (((b 7) * (a 4)) + (((b 8) * (a 3)) + (productC11 inv a b n))))))))))))) (UInt256.ofNat (2^240-1)))

def productC13 (inv : UInt256) (a b n : Nat → UInt256) : UInt256 := (CycleSubmission.DirectRecovery.carry ((UInt256.mulMod (n 4) (productQ8 inv a b n) P) + ((UInt256.mulMod (n 5) (productQ7 inv a b n) P) + ((UInt256.mulMod (n 6) (productQ6 inv a b n) P) + ((UInt256.mulMod (n 7) (productQ5 inv a b n) P) + ((UInt256.mulMod (n 8) (productQ4 inv a b n) P) + ((UInt256.mulMod (b 4) (a 8) P) + ((UInt256.mulMod (b 5) (a 7) P) + ((UInt256.mulMod (b 6) (a 6) P) + ((UInt256.mulMod (b 7) (a 5) P) + ((UInt256.mulMod (b 8) (a 4) P) + (productC12 inv a b n))))))))))) (((n 4) * (productQ8 inv a b n)) + (((n 5) * (productQ7 inv a b n)) + (((n 6) * (productQ6 inv a b n)) + (((n 7) * (productQ5 inv a b n)) + (((n 8) * (productQ4 inv a b n)) + (((b 4) * (a 8)) + (((b 5) * (a 7)) + (((b 6) * (a 6)) + (((b 7) * (a 5)) + (((b 8) * (a 4)) + (productC12 inv a b n))))))))))))

def productD3 (inv : UInt256) (a b n : Nat → UInt256) : UInt256 := (UInt256.land (((n 4) * (productQ8 inv a b n)) + (((n 5) * (productQ7 inv a b n)) + (((n 6) * (productQ6 inv a b n)) + (((n 7) * (productQ5 inv a b n)) + (((n 8) * (productQ4 inv a b n)) + (((b 4) * (a 8)) + (((b 5) * (a 7)) + (((b 6) * (a 6)) + (((b 7) * (a 5)) + (((b 8) * (a 4)) + (productC12 inv a b n))))))))))) (UInt256.ofNat (2^240-1)))

def productD4 (inv : UInt256) (a b n : Nat → UInt256) : UInt256 := (UInt256.land (UInt256.ofNat (2^240-1)) (((n 5) * (productQ8 inv a b n)) + (((n 6) * (productQ7 inv a b n)) + (((n 7) * (productQ6 inv a b n)) + (((n 8) * (productQ5 inv a b n)) + (((b 5) * (a 8)) + (((b 6) * (a 7)) + (((b 7) * (a 6)) + (((b 8) * (a 5)) + (productC13 inv a b n))))))))))

def productC14 (inv : UInt256) (a b n : Nat → UInt256) : UInt256 := (CycleSubmission.DirectRecovery.carry ((UInt256.mulMod (n 5) (productQ8 inv a b n) P) + ((UInt256.mulMod (n 6) (productQ7 inv a b n) P) + ((UInt256.mulMod (n 7) (productQ6 inv a b n) P) + ((UInt256.mulMod (n 8) (productQ5 inv a b n) P) + ((UInt256.mulMod (b 5) (a 8) P) + ((UInt256.mulMod (b 6) (a 7) P) + ((UInt256.mulMod (b 7) (a 6) P) + ((UInt256.mulMod (b 8) (a 5) P) + (productC13 inv a b n))))))))) (((n 5) * (productQ8 inv a b n)) + (((n 6) * (productQ7 inv a b n)) + (((n 7) * (productQ6 inv a b n)) + (((n 8) * (productQ5 inv a b n)) + (((b 5) * (a 8)) + (((b 6) * (a 7)) + (((b 7) * (a 6)) + (((b 8) * (a 5)) + (productC13 inv a b n))))))))))

def productD5 (inv : UInt256) (a b n : Nat → UInt256) : UInt256 := (UInt256.land (UInt256.ofNat (2^240-1)) (((n 6) * (productQ8 inv a b n)) + (((n 7) * (productQ7 inv a b n)) + (((n 8) * (productQ6 inv a b n)) + (((b 6) * (a 8)) + (((b 7) * (a 7)) + (((b 8) * (a 6)) + (productC14 inv a b n))))))))

def productC15 (inv : UInt256) (a b n : Nat → UInt256) : UInt256 := (CycleSubmission.DirectRecovery.carry ((UInt256.mulMod (n 6) (productQ8 inv a b n) P) + ((UInt256.mulMod (n 7) (productQ7 inv a b n) P) + ((UInt256.mulMod (n 8) (productQ6 inv a b n) P) + ((UInt256.mulMod (b 6) (a 8) P) + ((UInt256.mulMod (b 7) (a 7) P) + ((UInt256.mulMod (b 8) (a 6) P) + (productC14 inv a b n))))))) (((n 6) * (productQ8 inv a b n)) + (((n 7) * (productQ7 inv a b n)) + (((n 8) * (productQ6 inv a b n)) + (((b 6) * (a 8)) + (((b 7) * (a 7)) + (((b 8) * (a 6)) + (productC14 inv a b n))))))))

def productD6 (inv : UInt256) (a b n : Nat → UInt256) : UInt256 := (UInt256.land (UInt256.ofNat (2^240-1)) (((n 7) * (productQ8 inv a b n)) + (((n 8) * (productQ7 inv a b n)) + (((b 7) * (a 8)) + (((b 8) * (a 7)) + (productC15 inv a b n))))))

def productC16 (inv : UInt256) (a b n : Nat → UInt256) : UInt256 := (CycleSubmission.DirectRecovery.carry ((UInt256.mulMod (n 7) (productQ8 inv a b n) P) + ((UInt256.mulMod (n 8) (productQ7 inv a b n) P) + ((UInt256.mulMod (b 7) (a 8) P) + ((UInt256.mulMod (b 8) (a 7) P) + (productC15 inv a b n))))) (((n 7) * (productQ8 inv a b n)) + (((n 8) * (productQ7 inv a b n)) + (((b 7) * (a 8)) + (((b 8) * (a 7)) + (productC15 inv a b n))))))

def productC17 (inv : UInt256) (a b n : Nat → UInt256) : UInt256 := (CycleSubmission.DirectRecovery.carry ((UInt256.mulMod (n 8) (productQ8 inv a b n) P) + ((UInt256.mulMod (b 8) (a 8) P) + (productC16 inv a b n))) (((n 8) * (productQ8 inv a b n)) + (((b 8) * (a 8)) + (productC16 inv a b n))))

def productD7 (inv : UInt256) (a b n : Nat → UInt256) : UInt256 := (UInt256.land (UInt256.ofNat (2^240-1)) (((n 8) * (productQ8 inv a b n)) + (((b 8) * (a 8)) + (productC16 inv a b n))))

def productq (inv : UInt256) (a b n : Nat → UInt256) (i : Nat) : UInt256 :=
  match i with
  | 0 => productQ0 inv a b n
  | 1 => productQ1 inv a b n
  | 2 => productQ2 inv a b n
  | 3 => productQ3 inv a b n
  | 4 => productQ4 inv a b n
  | 5 => productQ5 inv a b n
  | 6 => productQ6 inv a b n
  | 7 => productQ7 inv a b n
  | 8 => productQ8 inv a b n
  | _ => UInt256.ofNat 0

def productc (inv : UInt256) (a b n : Nat → UInt256) (i : Nat) : UInt256 :=
  match i with
  | 0 => productC0 inv a b n
  | 1 => productC1 inv a b n
  | 2 => productC2 inv a b n
  | 3 => productC3 inv a b n
  | 4 => productC4 inv a b n
  | 5 => productC5 inv a b n
  | 6 => productC6 inv a b n
  | 7 => productC7 inv a b n
  | 8 => productC8 inv a b n
  | 9 => productC9 inv a b n
  | 10 => productC10 inv a b n
  | 11 => productC11 inv a b n
  | 12 => productC12 inv a b n
  | 13 => productC13 inv a b n
  | 14 => productC14 inv a b n
  | 15 => productC15 inv a b n
  | 16 => productC16 inv a b n
  | 17 => productC17 inv a b n
  | _ => UInt256.ofNat 0

def productd (inv : UInt256) (a b n : Nat → UInt256) (i : Nat) : UInt256 :=
  match i with
  | 0 => productD0 inv a b n
  | 1 => productD1 inv a b n
  | 2 => productD2 inv a b n
  | 3 => productD3 inv a b n
  | 4 => productD4 inv a b n
  | 5 => productD5 inv a b n
  | 6 => productD6 inv a b n
  | 7 => productD7 inv a b n
  | 8 => productC17 inv a b n
  | _ => UInt256.ofNat 0

def productTrace (inv : UInt256) (a b n : Nat → UInt256) : Trace .product inv a b n where
      q := productq inv a b n
      c := productc inv a b n
      d := productd inv a b n
      zero := rfl
      quotient := by intro i hi; interval_cases i <;> rfl
      carry := by intro i hi; interval_cases i <;> rfl
      digit := by intro i h9 h17; interval_cases i <;> rfl
      top := rfl
    #print axioms productTrace
    end CycleSubmission.WordHistory
    