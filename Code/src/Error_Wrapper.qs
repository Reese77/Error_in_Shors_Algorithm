namespace Error_In_Shor_Algo {
    open Tools;
    open Microsoft.Quantum.Intrinsic;
    open Microsoft.Quantum.Canon;
    // open Microsoft.Quantum.Arithmetic;
    open Microsoft.Quantum.Random;
    open Microsoft.Quantum.Convert;
    open Microsoft.Quantum.Diagnostics;
    open Microsoft.Quantum.Math;

    //ProbX is an Int between 0-1 000 000 denoting the probability that X gate is applied after every gate
    //ProbZ is an Int between 0-1 000 000 denoting probability that Z gate is applied after every gate
    newtype QubitError = (q : Qubit, ProbX : Int, ProbZ : Int);

    
    //TODO maybe make multiple probabilities for accidentally applying X or Z gate separately
    newtype LittleEndianError = (Data : QubitError[]);



    operation X_Error(qe : QubitError) : Unit {
        mutable prob = GenerateRandomNumberInRangeI(1000000);
        let (q, x, z) = qe!;
        X(q);

        if prob < x {
            X(q);
        }
        set prob = GenerateRandomNumberInRangeI(1000000);
        if prob < z {
            Z(q);
        }
    }

    operation Z_Error(qe : QubitError) : Unit {
        mutable prob = GenerateRandomNumberInRangeI(1000000);
        let (q, x, z) = qe!;
        Z(q);

        if prob < x {
            X(q);
        }
        set prob = GenerateRandomNumberInRangeI(1000000);
        if prob < z {
            Z(q);
        }
    }

    operation H_Error(qe : QubitError) : Unit {
        mutable prob = GenerateRandomNumberInRangeI(1000000);
        let (q, x, z) = qe!;
        H(q);

        if prob < x {
            X(q);
        }
        set prob = GenerateRandomNumberInRangeI(1000000);
        if prob < z {
            Z(q);
        }
    }
}