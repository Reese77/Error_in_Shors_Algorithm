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
        let p = 11;
        let q = 23;
        let mod = IntAsBigInt(p * q);

        let guess = 16L;
        return findOrderOfAMod_RecycledXRegister(guess, mod);
        //let result = findOrderOfAMod_RecycledXRegister(guess, mod);

        //Message($"Found result: {result}");

        //let candidate = FindOrderFromQFT(guess, mod, result, 2 * BitSizeL(mod), 4);
        //return RemoveEvenMultiples(guess, mod, candidate);
    }
}
