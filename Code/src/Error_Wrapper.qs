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
    newtype QubitError = (qubit : Qubit, ProbX : Int, ProbZ : Int);

    
    //TODO maybe make multiple probabilities for accidentally applying X or Z gate separately
    newtype LittleEndianError = (Data : QubitError[]);


    operation X_Error(qe : QubitError) : Unit {
        let (qubit, prob_x_error, prob_z_error) = qe!;

        mutable random_num = GenerateRandomNumberInRangeI(1000000);
        //small chance of causing X gate to happen before intended gate
        if random_num < prob_x_error {
            X(qubit);
        }
        set random_num = GenerateRandomNumberInRangeI(1000000);
        //small chance of causing Z gate to happen before intended gate
        if random_num < prob_z_error {
            Z(qubit);
        }

        //intended gate
        X(qubit);
    }

    operation Z_Error(qe : QubitError) : Unit {
        let (qubit, prob_x_error, prob_z_error) = qe!;

        mutable random_num = GenerateRandomNumberInRangeI(1000000);
        //small chance of causing X gate to happen before intended gate
        if random_num < prob_x_error {
            X(qubit);
        }
        set random_num = GenerateRandomNumberInRangeI(1000000);
        //small chance of causing Z gate to happen before intended gate
        if random_num < prob_z_error {
            Z(qubit);
        }

        //intended gate
        Z(qubit);
    }

    operation H_Error(qe : QubitError) : Unit {
        let (qubit, prob_x_error, prob_z_error) = qe!;

        mutable random_num = GenerateRandomNumberInRangeI(1000000);
        //small chance of causing X gate to happen before intended gate
        if random_num < prob_x_error {
            X(qubit);
        }
        set random_num = GenerateRandomNumberInRangeI(1000000);
        //small chance of causing Z gate to happen before intended gate
        if random_num < prob_z_error {
            Z(qubit);
        }

        //intended gate
        H(qubit);
    }

    operation M_Error(qe : QubitError)  : Unit {
        let (qubit, prob_x_error, prob_z_error) = qe!;

        mutable random_num = GenerateRandomNumberInRangeI(1000000);
        //small chance of causing X gate to happen before intended gate
        if random_num < prob_x_error {
            X(qubit);
        }
        set random_num = GenerateRandomNumberInRangeI(1000000);
        //small chance of causing Z gate to happen before intended gate
        if random_num < prob_z_error {
            Z(qubit);
        }

        //intended gate
        M(qubit);
    }

    operation CNOT_Error(control : QubitError, target : QubitError) : Unit {
        let (qubit1, prob_x_error1, prob_z_error1) = control!;
        let (qubit2, prob_x_error2, prob_z_error2) = target!;

        mutable random_num = GenerateRandomNumberInRangeI(1000000);
        if random_num < prob_x_error1 {
            X(qubit1);
        }
        set random_num = GenerateRandomNumberInRangeI(1000000);
        if random_num < prob_z_error1 {
            Z(qubit1);
        }

        set random_num = GenerateRandomNumberInRangeI(1000000);
        if random_num < prob_x_error2 {
            X(qubit2);
        }
        set random_num = GenerateRandomNumberInRangeI(1000000);
        if random_num < prob_z_error2 {
            Z(qubit2);
        }

        CNOT(qubit1, qubit2);

    }

    operation CCOT_Error(control1 : QubitError, control2 : QubitError, target : QubitError) : Unit {
        let (qubit1, prob_x_error1, prob_z_error1) = control1!;
        let (qubit2, prob_x_error2, prob_z_error2) = control2!;
        let (qubit3, prob_x_error3, prob_z_error3) = target!;

        mutable random_num = GenerateRandomNumberInRangeI(1000000);
        if random_num < prob_x_error1 {
            X(qubit1);
        }
        set random_num = GenerateRandomNumberInRangeI(1000000);
        if random_num < prob_z_error1 {
            Z(qubit1);
        }

        set random_num = GenerateRandomNumberInRangeI(1000000);
        if random_num < prob_x_error2 {
            X(qubit2);
        }
        set random_num = GenerateRandomNumberInRangeI(1000000);
        if random_num < prob_z_error2 {
            Z(qubit2);
        }

        set random_num = GenerateRandomNumberInRangeI(1000000);
        if random_num < prob_x_error3 {
            X(qubit3);
        }
        set random_num = GenerateRandomNumberInRangeI(1000000);
        if random_num < prob_z_error3 {
            Z(qubit3);
        }

        CCNOT(qubit1, qubit2, qubit3);

    }
}