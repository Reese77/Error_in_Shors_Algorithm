/// # Sample
/// Getting started
///
/// # Description
/// This is a minimal Q# program that can be used to start writing Q# code.
namespace MyQuantumProgram {

    open Microsoft.Quantum.Arrays;
    open Microsoft.Quantum.Math;
    open Microsoft.Quantum.Intrinsic;
    open Microsoft.Quantum.Convert;
    open Microsoft.Quantum.Canon;
    open Error_In_Shor_Algo;
    open Tools;


    @EntryPoint()
    operation Main() : BigInt {
        let p = 5;
        let q = 7;

    

        return findOrderOfAMod_RecycledXRegister(9L, IntAsBigInt(p * q));
    }
}
