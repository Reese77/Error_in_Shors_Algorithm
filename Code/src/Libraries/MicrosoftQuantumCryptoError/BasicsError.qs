

namespace Microsoft.Quantum.Crypto.Error.Basics {
    open Tools;
    open Microsoft.Quantum.Convert;
    open Microsoft.Quantum.Math;
    open Microsoft.Quantum.Diagnostics;

    //ProbX is an Int between 0-1 000 000 denoting the probability that X gate is applied after every gate
    //ProbZ is an Int between 0-1 000 000 denoting probability that Z gate is applied after every gate
    newtype Qubit_Error = (qubit : Qubit, ProbError : Int[]);

    newtype LittleEndian_Error = (Data : Qubit_Error[]);

    //TODO make this ancilla function
    operation createAncilla(length : Int) : Qubit_Error[] {
        use a = Qubit[length];
        mutable ret_val = [Qubit_Error(a[0], [0, 0]), size = length];

        for i in 0 .. length - 1 {
            set ret_val w/= i <- Qubit_Error(a[i], [0, 0]);
        }
        return ret_val;
    }

    operation createQubitErrorArrayFromQubitArray(qubit_arr : Qubit[]) : Qubit_Error[] {
        mutable ret_val = [Qubit_Error(qubit_arr[0], [0, 0]), size = Length(qubit_arr)];

        for i in 0 .. Length(qubit_arr) - 1 {
            set ret_val w/= i <- Qubit_Error(qubit_arr[i], [0, 0]);
        }
        return ret_val;
    }



    function IsTestable () : Bool {
        return true;
    }

    function IsMinimizeDepthCostMetric () : Bool {
        return false;
	}

    function IsMinimizeTCostMetric () : Bool {
        return true;
	}

    function IsMinimizeWidthCostMetric () : Bool {
        return false;
	}


    operation causeError(q : Qubit, prob_error : Int[]) : Unit {
        mutable random_num = GenerateRandomNumberInRangeI(1000000);

        if (random_num < prob_error[0]) {
            X(q);
        }

        set random_num = GenerateRandomNumberInRangeI(1000000);
        if (random_num < prob_error[1]) {
            Z(q);
        }
    }


    operation X_Gate_Error(qe : Qubit_Error) : Unit is Adj + Ctl{
        let (qubit, prob_error) = qe!;

        causeError(qubit, prob_error);

        //intended gate
        X(qubit);
    }

    operation Z_Gate_Error(qe : Qubit_Error) : Unit is Adj + Ctl{
        let (qubit, prob_error) = qe!;

        causeError(qubit, prob_error);

        //intended gate
        Z(qubit);
    }

    operation H_Gate_Error(qe : Qubit_Error) : Unit is Adj + Ctl{
        let (qubit, prob_error) = qe!;

        causeError(qubit, prob_error);

        //intended gate
        H(qubit);
    }

    operation M_Gate_Error(qe : Qubit_Error)  : Result {
        let (qubit, prob_error) = qe!;

        causeError(qubit, prob_error);

        //intended gate
        return M(qubit);
    }

    operation CNOT_Gate_Error(control : Qubit_Error, target : Qubit_Error) : Unit is Adj + Ctl{
        let (qubit1, prob_error1) = control!;
        let (qubit2, prob_error2) = target!;

        causeError(qubit1, prob_error1);
        causeError(qubit2, prob_error2);

        CNOT(qubit1, qubit2);

    }

    operation CCOT_Gate_Error(control1 : Qubit_Error, control2 : Qubit_Error, target : Qubit_Error) : Unit is Adj + Ctl{
        let (qubit1, prob_error1) = control1!;
        let (qubit2, prob_error2) = control2!;
        let (qubit3, prob_error3) = target!;

        causeError(qubit1, prob_error1);
        causeError(qubit2, prob_error2);
        causeError(qubit3, prob_error3);

        CCNOT(qubit1, qubit2, qubit3);

    }

    operation R_Gate_Error(pauli : Pauli, theta : Double, qe : Qubit_Error) : Unit is Adj + Ctl{
        let (qubit, prob_error) = qe!;

        causeError(qubit, prob_error);

        //intended gate
        R(pauli, theta, qubit);
    }

    operation T_Gate_Error(qe : Qubit_Error) : Unit is Adj + Ctl{
        let (qubit, prob_error) = qe!;

        causeError(qubit, prob_error);

        //intended gate
        T(qubit);
    }


    operation RFrac_Gate_Error(pauli : Pauli, numerator : Int, power : Int, qubit : Qubit_Error) : Unit is Adj + Ctl{
        R_Gate_Error(pauli, -PI() * IntAsDouble(numerator) / IntAsDouble(2 ^ (power - 1)), qubit);
    }

    operation R1Frac_Gate_Error(numerator : Int, power : Int, qubit : Qubit_Error) : Unit is Adj + Ctl{
        RFrac_Gate_Error(PauliZ, -numerator, power + 1, qubit);
        RFrac_Gate_Error(PauliI, numerator, power + 1, qubit);

    }
    
    operation Reset_Error(qubit : Qubit_Error) : Unit is Adj + Ctl{
        let (q, e) = qubit!;
        Reset(q);
    }

    operation ResetAll_Error(le : LittleEndian_Error) : Unit is Adj + Ctl{
        let unwrapped = le!;
        for q in unwrapped {
            Reset_Error(q);
        }
    }

    operation SWAP_Gate_Error(q1 : Qubit_Error, q2 : Qubit_Error) : Unit is Adj + Ctl {
        CNOT_Gate_Error(q1, q2);
        CNOT_Gate_Error(q2, q1);
        CNOT_Gate_Error(q1, q2);
    }

    operation CyclicRotateRegister_Error (xs : LittleEndian_Error) : Unit
    {
        body (...) {
            let nQubits = Length(xs!);
            FanoutSwapReverseRegister(xs!);
            FanoutSwapReverseRegister(xs![1..(nQubits - 1)]);
        }
        adjoint auto;
        controlled auto;
        controlled adjoint auto;
    }

    operation AndWrapper_Error(control1 : Qubit_Error, control2 : Qubit_Error, target : Qubit_Error) : Unit {
        body (...){
            if (IsMinimizeDepthCostMetric()){
                CCOT_Gate_Error(control1, control2, target); // todo!
            } else {
                CCOT_Gate_Error(control1, control2, target); //todo!
            }
        }
        controlled (controls, ...){
            (Controlled CCNOTWrapper_Error)(controls, (control1, control2, target));
        }
        controlled adjoint auto;
    }

    operation ApplyXorInPlaceL_Error(value : BigInt, target : Qubit_Error[]) : Unit is Adj + Ctl {
        body (...) {
            Fact(value >= 0L, "`value` must be non-negative.");
            mutable runningValue = value;
            for q in target {
                if (runningValue &&& 1L) != 0L {
                    X_Gate_Error(q);
                }
                set runningValue >>>= 1;
            }
            Fact(runningValue == 0L, "`value` is too large.");
        }
        adjoint self;
    }

    operation CCNOTWrapper_Error(control1 : Qubit_Error, control2 : Qubit_Error, target : Qubit_Error) : Unit {
        body (...){
            if (IsTestable()){
                CCOT_Gate_Error(control1, control2, target);
            } else {
                if (IsMinimizeWidthCostMetric()){
                    ccnot_T_depth_3_Error(control1, control2, target);
                } else {
                    ccnot_T_depth_1_Error(control1, control2, target);
                }
            }
        }
        controlled (controls, ...){

            CheckIfAllOnes_Error(createQubitErrorArrayFromQubitArray(controls) + [control1, control2], target);
        }
        controlled adjoint auto;
    }

    operation ccnot_T_depth_3_Error (control1 : Qubit_Error, control2 : Qubit_Error, target : Qubit_Error) : Unit is Adj {
        body (...){
            H_Gate_Error(target);
            T_Gate_Error(control2);
            T_Gate_Error(control1);
            T_Gate_Error(target);
            CNOT_Gate_Error(control2, control1);
            CNOT_Gate_Error(target,control2);
            CNOT_Gate_Error(control1,target);
            (Adjoint T_Gate_Error)(control2);
            CNOT_Gate_Error(control1, control2);
            (Adjoint T_Gate_Error)(control1);
            (Adjoint T_Gate_Error)(control2);
            T_Gate_Error(target);
            CNOT_Gate_Error(target, control2);
            CNOT_Gate_Error(control1, target);
            CNOT_Gate_Error(control2, control1);
            H_Gate_Error(target);
        }
    }

    operation ccnot_T_depth_1_Error (control1 : Qubit_Error, control2 : Qubit_Error, target : Qubit_Error) : Unit is Adj + Ctl {
        let auxilliaryReg = createAncilla(4);
        // TODO is this rewriting of the operation okay?
        within{
            TDepthOneCCNOTOuterCircuit_Error(auxilliaryReg + [target, control1, control2]);
        } apply {
            TDepthOneCCNOTInnerCircuit_Error(auxilliaryReg + [target, control1, control2]);
        }
    }

    operation CheckIfAllOnes_Error(xs : Qubit_Error[], output : Qubit_Error) : Unit {
        body (...){
            let nQubits = Length(xs);
            if (nQubits == 0){
                X_Gate_Error(output);
            } elif (nQubits == 1){
                CNOT_Gate_Error(xs[0], output);
            } elif (nQubits == 2){
                CCNOTWrapper_Error(xs[0], xs[1], output);
            } else {
                if (IsMinimizeWidthCostMetric()) {
                    LinearMultiControl_Error(xs, output);
                } else { //high width but log-depth and small T-count
                    use (spareControls, ancillaOutput) = (Qubit[nQubits - 2], Qubit()) {
                        CompressControls_Error(xs, spareControls, ancillaOutput);
                        CNOT_Gate_Error(ancillaOutput, output);
                        (Adjoint CompressControls_Error)(xs, spareControls, ancillaOutput);
                    }
                }
            }
        }
        controlled (controls, ...){
            CheckIfAllOnes_Error(controls + xs, output);
        }
        controlled adjoint auto;
    }

    operation TDepthOneCCNOTOuterCircuit_Error (qs : Qubit_Error[]) : Unit is Adj + Ctl {
        Fact(Length(qs)==7, "7 qubits are expected");
        H_Gate_Error(qs[4]);
        CNOT_Gate_Error(qs[5], qs[1]);
        CNOT_Gate_Error(qs[6], qs[3]);
        CNOT_Gate_Error(qs[5], qs[2]);
        CNOT_Gate_Error(qs[4], qs[1]);
        CNOT_Gate_Error(qs[3], qs[0]);
        CNOT_Gate_Error(qs[6], qs[2]);
        CNOT_Gate_Error(qs[4], qs[0]);
        CNOT_Gate_Error(qs[1], qs[3]);
    }

    operation TDepthOneCCNOTInnerCircuit_Error (qs : Qubit_Error[]) : Unit is Adj + Ctl {
        Fact(Length(qs)== 7, "7 qubits are expected");
        ApplyToEachCA(Adjoint T_Gate_Error, qs[0 .. 2]);
        ApplyToEachCA(T_Gate_Error, qs[3 .. 6]);
    }
}