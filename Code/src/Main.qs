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
    operation Main() :  (Int, Bool) {
        //variables for setup
        //2 safe primes and their product
        let p = 23;
        let q = 47;
        let mod = p * q;
        //number we want to find order of
        let guess = 2;

        //classically find order for debugging purposes
        let order = findOrderofAModNaiveI(guess, mod);
        let possibleApproximates = listOfIntegerOverOrder(order);
        

        let len = 200;
        // OPTION 1: Works similar to histogram repeating len times. 
        // Either return Int[] or (Int[], Int[])
        // First is just the integer you measure immediately after QFT
        // Second is first and whatever order candidate you get when applying fraction expansion to qft result

        // mutable qftresults = [0, size = len];
        // mutable orderresults = [0, size = len];
        // for i in 0 .. len-1 {
        //     Message($"{i}");
        //     set qftresults w/= i <-findOrderOfAMod_RecycledXRegisterI(guess, mod);
        //     // set orderresults w/= i <- RemoveEvenMultiplesI(guess, mod, FindOrderFromQFTI(guess, mod, qftresults[i], 2 * BitSizeL(mod), 4, 0L));
        // }
        // return qftresults;

        //
        let qftres = findOrderOfAMod_RecycledXRegisterI(guess, mod);

        //compute list of fractions that are approximates of qftres/2^n
        let continuedFraction = ContinuedFractionExpansionI(qftres, 2^(2 * BitSizeI(mod)));
        let convergents = ConvergentsI(continuedFraction);

        //Some important information for debugging and seeing what the algo did
        Message($"{qftres}/{2^(2 * BitSizeI(mod))}");
        Message($"1/{order}^2");
        Message($"{convergents}");
        Message($"{closestDistance(possibleApproximates, IntAsDouble(qftres) / IntAsDouble(2^(2 * BitSizeI(mod)) - 1))}");
        Message("");

        //OPTION 2: Bool of if it should be found since qft/2^n1 < 1/den^2
        // You could also just return a if you want
        let (a, b) = closestDistance(possibleApproximates, IntAsDouble(qftres) / IntAsDouble(2^(2 * BitSizeI(mod))));
        //return a < 1.0 / IntAsDouble(order^2);


        //OPTION 3: Int returning order candidate
        let ordres = RemoveEvenMultiplesI(guess, mod, FindOrderFromQFTI(guess, mod, qftres, 2 * BitSizeI(mod), 4, 0));
        
        //if we don't get an order, it's nice to know what the qftres was 
        if ordres == -1 {
            return (-ordres, a < 1.0 / IntAsDouble(order^2));
        }
        return (ordres, a < 1.0 / IntAsDouble(order^2));
        

        //OPTION 4: (Int, Int) returning order and qft to check
        // return (ordres, qftres);
    }
}
