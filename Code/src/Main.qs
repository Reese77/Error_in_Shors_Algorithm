/// # Sample
/// Getting started
///
/// # Description
/// This is a minimal Q# program that can be used to start writing Q# code.
namespace MyQuantumProgram {

    import Microsoft.Quantum.Diagnostics.DumpMachine;
    open Microsoft.Quantum.Arrays;
    open Microsoft.Quantum.Math;
    open Microsoft.Quantum.Intrinsic;
    open Microsoft.Quantum.Convert;
    open Microsoft.Quantum.Canon;
    open Error_In_Shor_Algo;
    open Tools;


    @EntryPoint()
    
    operation Main() : Bool {

        //TODO in the whole library, in every controlled block, run a loop through all controls to cause error with getCTLprob
        let p = 5;
        let q = 3;
        let len = 1;
        let mod = p * q;

        mutable qftresults = [0L, size = len];
        mutable orderresults = [0L, size = len];
        let guess = 2;

        let order = findOrderofAModNaiveI(guess, mod);
        let possibleApproximates = listOfIntegerOverOrder(order);

        // use z = Qubit[6];
        // ApplyXorInPlaceL(35L, z);
        // //DumpMachine();
        


        // for i in 0 .. len-1 {
        //     Message($"{i}");
        //     set qftresults w/= i <-findOrderOfAMod_RecycledXRegister_Error(guess, mod);
        //     set orderresults w/= i <- RemoveEvenMultiples(guess, mod, FindOrderFromQFT(guess, mod, qftresults[i], 2 * BitSizeL(mod), 4, 0L));
        // }


        let qftres = findOrderOfAMod_RecycledXRegisterI(guess, mod);

        //return qftres;

        let continuedFraction = ContinuedFractionExpansionI(qftres, 2^(2 * BitSizeI(mod)));
        let convergents = ConvergentsI(continuedFraction);

        Message($"{qftres}/{2^(2 * BitSizeI(mod))}");
        Message($"1/{order}^2");
        Message($"{convergents}");
        Message($"{closestDistance(possibleApproximates, IntAsDouble(qftres) / IntAsDouble(2^(2 * BitSizeI(mod)) - 1))}");


        //OPTION 1: Bool of if it should be found since qft/2^n1 < 1/den^2
        let (a, b) = closestDistance(possibleApproximates, IntAsDouble(qftres) / IntAsDouble(2^(2 * BitSizeI(mod)) - 1));
        return a < 1.0 / IntAsDouble(order^2);


        //OPTION 2: Int returning order
        let ordres = RemoveEvenMultiplesI(guess, mod, FindOrderFromQFTI(guess, mod, qftres, 2 * BitSizeI(mod), 4, 0));
        
        // if ordres == -1 {
        //     return -qftres;
        // }
        // return ordres;
        

        //OPTION 3: (Int, Int) returning order and qft to check
        // return (ordres, qftres);




        
    }
}
