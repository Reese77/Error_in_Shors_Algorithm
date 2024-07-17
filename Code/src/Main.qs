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


    //@EntryPoint()
    operation Main() : (BigInt, BigInt)[] {
        let p = 5;
        let q = 7;
        let len = 10;
        let mod = IntAsBigInt(p * q);

        mutable qftresults = [0L, size = len];
        mutable orderresults = [0L, size = len];
        let guess = 12L;

        for i in 0 .. len-1 {
            Message($"{i}");
            set qftresults w/= i <-findOrderOfAMod_RecycledXRegister(guess, mod);
            set orderresults w/= i <- RemoveEvenMultiples(guess, mod, FindOrderFromQFT(guess, mod, qftresults[i], 2 * BitSizeL(mod), 4, 0L));
        }
        return Zipped(qftresults, orderresults);
        
        //return findOrderOfAMod_RecycledXRegister(guess, mod);
        let result = findOrderOfAMod_RecycledXRegister(guess, mod);

        //Message($"Found result: {result}");

        let candidate = FindOrderFromQFT(guess, mod, result, 2 * BitSizeL(mod), 4, 0L);

        //return (result, candidate);

        //return RemoveEvenMultiples(guess, mod, candidate);
    }
}
