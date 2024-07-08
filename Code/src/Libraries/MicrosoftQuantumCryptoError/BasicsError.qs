

namespace Microsoft.Quantum.Crypto.Error.Basics {
    open Tools;
    open Microsoft.Quantum.Convert;
    open Microsoft.Quantum.Math;
    open Microsoft.Quantum.Diagnostics;

    ////definitions of new data types

    //ProbX is an Int between 0-1 000 000 denoting the probability that X gate is applied after every gate
    //ProbZ is an Int between 0-1 000 000 denoting probability that Z gate is applied after every gate
    newtype Qubit_Error = (qubit : Qubit, ProbError : Int[]);

    newtype LittleEndian_Error = (Data : Qubit_Error[]);


    ////operations to create or convert things TODO reword this comment

    //TODO make this ancilla function
    operation createAncillaErrorArray(length : Int, probs : Int[]) : Qubit_Error[] {
        use a = Qubit[length];
        mutable ret_val = [Qubit_Error(a[0], probs), size = length];

        for i in 0 .. length - 1 {
            set ret_val w/= i <- Qubit_Error(a[i], probs );
        }
        return ret_val;
    }

    operation createAncillaError(probs : Int[]) : Qubit_Error {
        use a = Qubit();
        let ret_val = Qubit_Error(a, probs);
        return ret_val;
    }

    operation convertQubitErrorToQubit(qe : Qubit_Error) : Qubit {
        let (q, e) = qe!;
        return q;
    }

    operation convertQubitToQubitError(q : Qubit, probs : Int[]) : Qubit_Error {
        return Qubit_Error(q, probs);
    }

    operation convertQubitArrayToQubitErrorArray(qubit_arr : Qubit[], probs : Int[]) : Qubit_Error[] {
        mutable ret_val = [Qubit_Error(qubit_arr[0], probs), size = Length(qubit_arr)];

        for i in 0 .. Length(qubit_arr) - 1 {
            set ret_val w/= i <- Qubit_Error(qubit_arr[i], probs);
        }
        return ret_val;
    }

    operation convertQubitErrorArrayToQubitArray(qe_arr : Qubit_Error[]) : Qubit[] {
        use a = Qubit();
        mutable ret_val = [a, size = Length(qe_arr)];

        for i in 0 .. Length(qe_arr) - 1 {
            let (q, p) = qe_arr[i]!;
            set ret_val w/= i <- q;
        }
        return ret_val;

    }
 

    //necessary functions copied from MicrosoftQuantumCrypto library

    operation ApplyToEachWrapperCA<'T>(singleElementOperation : ('T => Unit is Ctl + Adj), register : 'T[]) : Unit {
        body (...){
            if (IsMinimizeWidthCostMetric()){
                ApplyToEachCA(singleElementOperation, register);
            } else {
                ApplyToEachLowDepthCA(singleElementOperation, register);
            }
        }
        controlled adjoint auto;
    }

    operation ApplyToEachLowDepthCA<'T>(op : ('T => Unit is Ctl + Adj), qubitArray : 'T[]) : Unit {
        body(...){
            ApplyToEachCA(op, qubitArray);
        }
        controlled (controls, ...){
            let nQubits=Length(qubitArray);

            mutable singleControls = createAncillaErrorArray(nQubits, [0, 0]);
            (Controlled X_Gate_Error)(controls, singleControls[0]);
            FanoutToZero_Error(singleControls[0], singleControls[1..nQubits - 1]);
            for idx in 0..nQubits - 1 {

                (Controlled op)([convertQubitErrorToQubit(singleControls[idx])], (qubitArray[idx]));
            }
            (Adjoint FanoutToZero_Error)(singleControls[0], singleControls[1..nQubits - 1]);
            (Controlled X_Gate_Error)(controls, singleControls[0]);
            ResetAll_Error(singleControls);

        }
        controlled adjoint auto;
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


    //operations for replacing fundamental gates with wrappers to cause errors
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

    operation ResetAll_Error(le : Qubit_Error[]) : Unit is Adj + Ctl{
        for q in le {
            Reset_Error(q);
        }
    }

    operation SWAP_Gate_Error(q1 : Qubit_Error, q2 : Qubit_Error) : Unit is Adj + Ctl {
        CNOT_Gate_Error(q1, q2);
        CNOT_Gate_Error(q2, q1);
        CNOT_Gate_Error(q1, q2);
    }

    operation ClassicalCNOT_Error(control : Bool, target : Qubit_Error) : Unit {
        body (...){
            if (control) {
                X_Gate_Error(target);
            }
        }
        controlled (controls, ...){
            if (control) {
                (Controlled X_Gate_Error)(controls, (target));
            }
        }
        controlled adjoint auto;
    }

    operation ClassicalCCNOT_Error(control1 : Bool, control2 : Qubit_Error, target : Qubit_Error) : Unit {
        body (...){
            if (control1){
                CNOT_Gate_Error(control2, target);
            }
        }
        controlled (controls, ...){
            if (control1){
                (Controlled CNOT_Gate_Error)(controls, (control2, target));
            }
        }
        controlled adjoint auto;
    }

    operation ClassicalAND_Error(control1 : Bool, control2 : Qubit_Error, target : Qubit_Error) : Unit {
        body (...){
            if (control1){
                CNOT_Gate_Error(control2, target);
            }
        }
        controlled (controls, ...){
            if (control1){
                (Controlled CNOT_Gate_Error)(controls, (control2, target));
            }
        }
        controlled adjoint auto;
    }


    //wrapped versions of operations required from MicrosoftQuantumCrypto/Basics.qs 
    operation CyclicRotateRegister_Error (xs : LittleEndian_Error) : Unit
    {
        body (...) {
            let nQubits = Length(xs!);
            FanoutSwapReverseRegister_Error(xs!);
            FanoutSwapReverseRegister_Error(xs![1..(nQubits - 1)]);
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

            CheckIfAllOnes_Error(convertQubitArrayToQubitErrorArray(controls, [0, 0]) + [control1, control2], target);
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
        let auxilliaryReg = createAncillaErrorArray(4, [0, 0]);
        // TODO is this rewriting of the operation okay?
        within{
            TDepthOneCCNOTOuterCircuit_Error(auxilliaryReg + [target, control1, control2]);
        } apply {
            TDepthOneCCNOTInnerCircuit_Error(auxilliaryReg + [target, control1, control2]);
        }
        ResetAll_Error(auxilliaryReg);
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
                    mutable spareControls = createAncillaErrorArray(nQubits - 2, [0, 0]);
                    mutable ancillaOutput = createAncillaError([0, 0]);

                    CompressControls_Error(xs, spareControls, ancillaOutput);
                    CNOT_Gate_Error(ancillaOutput, output);
                    (Adjoint CompressControls_Error)(xs, spareControls, ancillaOutput);

                    ResetAll_Error(spareControls);
                    Reset_Error(ancillaOutput);
                }
            }
        }
        controlled (controls, ...){
            CheckIfAllOnes_Error(convertQubitArrayToQubitErrorArray(controls, [0, 0]) + xs, output);
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

    operation LinearMultiControl_Error(controlQubits : Qubit_Error[], output : Qubit_Error) : Unit {
        body (...){
            let nQubits = Length(controlQubits);
            if (nQubits == 0){
                //do nothing
            } elif (nQubits == 1){
                CNOT_Gate_Error(controlQubits[0], output);
            } elif (nQubits == 2){
                CCNOTWrapper_Error(controlQubits[0], controlQubits[1], output);
            } elif (nQubits <= 4){
                mutable ancillaControl = createAncillaError([0, 0]);
                LinearMultiControl_Error(controlQubits[0.. nQubits -2], ancillaControl);
                CCNOTWrapper_Error(controlQubits[nQubits - 1], ancillaControl, output);
                LinearMultiControl_Error(controlQubits[0.. nQubits -2], ancillaControl);
                CCNOTWrapper_Error(controlQubits[nQubits - 1], ancillaControl, output);

                Reset_Error(ancillaControl);

            } elif (nQubits == 5) {
                mutable ancillaControl = createAncillaError([0, 0]);
                LinearMultiControl_Error(controlQubits[0 .. nQubits - 3], ancillaControl);
                LinearMultiControl_Error(controlQubits[nQubits - 2 .. nQubits - 1] + [ancillaControl], output);
                LinearMultiControl_Error(controlQubits[0 .. nQubits - 3], ancillaControl);
                LinearMultiControl_Error(controlQubits[nQubits - 2 .. nQubits - 1] + [ancillaControl], output);
                Reset_Error(ancillaControl);

            } else {
                mutable ancillaControl = createAncillaError([0, 0]);
                let m = (nQubits + 1) / 2;
                CascadeControl_Error(controlQubits[0 .. m - 1], ancillaControl);
                CascadeControl_Error(controlQubits[m .. nQubits - 1] + [ancillaControl], output);
                CascadeControl_Error(controlQubits[0 .. m - 1], ancillaControl);
                CascadeControl_Error(controlQubits[m .. nQubits - 1] + [ancillaControl], output);
                Reset_Error(ancillaControl);
            }
        }
        controlled (controls, ...){
            LinearMultiControl_Error(convertQubitArrayToQubitErrorArray(controls, [0, 0]) + controlQubits, output);
        }
        controlled adjoint auto;
    }

    operation FanoutSwapReverseRegister_Error(xs : Qubit_Error[]) : Unit{
        body (...){
            SwapReverseRegister_Error(xs);
        }
        controlled (controls, ...){
            if (IsMinimizeWidthCostMetric()) { //don't fanout with low width
                (Controlled SwapReverseRegister_Error)(controls, (xs));
            } else {
                let nQubits = Length(xs);
                let nControls = nQubits / 2;
                if (nQubits == 2){
                    (Controlled SWAP_Gate_Error)(controls, (xs[0], xs[1]));
                } elif (nQubits > 2){
                    mutable singleControls = createAncillaErrorArray(nControls, [0, 0]);

                    (Controlled FanoutControls_Error)(controls,(singleControls));
                    for idxSwap in 0..nControls - 1 {
                        (Controlled SWAP_Gate_Error)([convertQubitErrorToQubit(singleControls[idxSwap])], (xs[idxSwap], xs[nQubits - 1 - idxSwap]));
                    }
                    (Controlled Adjoint FanoutControls_Error)(controls,(singleControls));

                    ResetAll_Error(singleControls);

                }
            }
        }
        controlled adjoint auto;
    }

    operation FanoutControls_Error(singleControls : Qubit_Error[]) : Unit {
        body (...){
            // With no control, nothing to fanout
        }
        controlled (controls, ...){
            (Controlled X_Gate_Error)(controls, singleControls[0]);
            FanoutToZero_Error(singleControls[0], singleControls[1..Length(singleControls) - 1]);
        }
        controlled adjoint auto;
    }

    operation CompressControls_Error(controlQubits : Qubit_Error[], blankControlQubits : Qubit_Error[], output : Qubit_Error) : Unit {
        body (...){
            let nControls = Length(controlQubits);
            let nNewControls = Length(blankControlQubits);
            if (nControls == 2){
                AndWrapper_Error(controlQubits[0], controlQubits[1], output);
            } else {
                Fact(nNewControls >= nControls/2, $"Cannot compress {nControls}
                    control qubits to {nNewControls} qubits without more ancilla");
                Fact(nNewControls <= nControls, 
                    $"Cannot compress {nControls} control qubits into
                    {nNewControls} qubits because there are too few controls");
                let compressLength = nControls - nNewControls;
                for idx in 0.. 2 .. nControls - 2 {
                    AndWrapper_Error(controlQubits[idx], controlQubits[idx + 1], blankControlQubits[idx/2]);
                }
                if (nControls % 2 == 0){
                    CompressControls_Error(blankControlQubits[0.. nControls/2 - 1], blankControlQubits[nControls/2 .. nNewControls - 1], output);
                } else {
                    CompressControls_Error([controlQubits[nControls - 1]] + blankControlQubits[0.. nControls/2 - 1], blankControlQubits[nControls/2 .. nNewControls - 1], output);
                }
            }
        }
        adjoint auto;
    }

    operation CascadeControl_Error(controlQubits : Qubit_Error[], output : Qubit_Error) : Unit {
        body (...){
            let nQubits = Length(controlQubits);
            if (nQubits <= 2){
                LinearMultiControl_Error(controlQubits, output);
            } else {
                mutable ancillaControls = createAncillaErrorArray(nQubits - 2, [0, 0]);


                let ancillaTargets = [output] + ancillaControls;
                for idx in 0 .. nQubits - 3 {
                    CCNOTWrapper_Error(controlQubits[idx], ancillaControls[idx], ancillaTargets[idx]);
                }
                CCNOTWrapper_Error(controlQubits[nQubits - 2], controlQubits[nQubits -1], ancillaControls[nQubits - 3]);
                for idx in nQubits - 3 .. (-1) .. 0 {
                    CCNOTWrapper_Error(controlQubits[idx], ancillaControls[idx], ancillaTargets[idx]);
                }
                for idx in 1 .. nQubits - 3 {
                    CCNOTWrapper_Error(controlQubits[idx], ancillaControls[idx], ancillaTargets[idx]);
                }
                CCNOTWrapper_Error(controlQubits[nQubits - 2], controlQubits[nQubits -1], ancillaControls[nQubits - 3]);
                for idx in nQubits - 3 .. (-1) .. 1 {
                    CCNOTWrapper_Error(controlQubits[idx], ancillaControls[idx], ancillaTargets[idx]);
                }

                ResetAll_Error(ancillaControls);
                
            }
        }
        controlled (controls, ...){
            CascadeControl_Error(convertQubitArrayToQubitErrorArray(controls, [0, 0]) + controlQubits, output);
        }
        controlled adjoint auto;
    }

    operation SwapReverseRegister_Error(register : Qubit_Error[]) : Unit is Adj + Ctl {
        let length = Length(register);
        for i in 0..length / 2 - 1 {
            SWAP_Gate_Error(register[i], register[(length - i) - 1]);
        }
    }

    operation FanoutToZero_Error(input : Qubit_Error, outputs : Qubit_Error[]) : Unit {
        body (...){
            let nQubits = Length(outputs);
            if (nQubits == 1){
                CNOT_Gate_Error(input, outputs[0]);
            } elif (nQubits >= 2){
                let middle = nQubits / 2;
                CNOT_Gate_Error(input, outputs[middle]);
                FanoutToZero_Error(input, outputs[0..middle - 1]);
                FanoutToZero_Error(outputs[middle], outputs[middle + 1..nQubits - 1]);
            }
        }
        controlled (controls, ...){
            let nQubits = Length(outputs);
            if (nQubits >= 1){
                (Controlled X_Gate_Error)(controls + [convertQubitErrorToQubit(input)], (outputs[0]));
                FanoutToZero_Error(outputs[0], outputs[1..nQubits - 1]);
            }
        }
        controlled adjoint auto;
    }


    function PropArrays_Error(props : Qubit_Error[], ys : Qubit_Error[]) : Qubit_Error[][] {
        let nQubits = Length(ys);
        let logn = Floor(Lg(IntAsDouble(nQubits)));
        // Here props is a placeholder value to indicate type
        mutable propArrays = [props, size = logn];
        mutable idxProps=0;
        set propArrays w/= 0 <- ys;
        for level in 1..logn - 1 {
            let levelSize = nQubits/2^level - 1;
            mutable levelProps = [props[0], size = levelSize + 1];
            for idm in 1..levelSize {
                set levelProps w/= idm <- props[idxProps];
                set idxProps = idxProps + 1;
            }
            set propArrays w/= level <- levelProps;
        }
        return propArrays;
    }
}