

namespace Microsoft.Quantum.Crypto.Error.Basics {
    open Tools;
    open Microsoft.Quantum.Convert;
    open Microsoft.Quantum.Math;
    open Microsoft.Quantum.Diagnostics;
    open Microsoft.Quantum.Random;
    open QIR.Intrinsic;

    ///IMPORTANT all comments starting with 3 slashes were copied over from original and may need to be edited

    //ProbX is an Int between 0-1 000 000 denoting the probability that X gate is applied after every gate
    //ProbZ is an Int between 0-1 000 000 denoting probability that Z gate is applied after every gate
    newtype Qubit_Error = (qubit : Qubit, ProbError : Int[]);

    newtype LittleEndian_Error = (Data : Qubit_Error[]);

    ////functions to get error probability arrays

    function get_X_Prob() : Int[] {
        return [0, 0];
    }

    function get_Y_Prob() : Int[] {
        return [0, 0];
    }

    function get_Ancilla_Prob() : Int[] {
        return [0, 0];
    }

    function get_Ctrl_Prob() : Int[] {
        return [0, 0];
    }

    function get_Prob() : Int[] {
        return [0, 0];
    }

    ////operations to create or convert things TODO reword this comment

    //
    function wrapAncillaErrorArray(q_arr : Qubit[], probs : Int[]) : Qubit_Error[] {
        
        mutable ret_val = [Qubit_Error(q_arr[0], probs), size = Length(q_arr)];

        for i in 0 .. Length(q_arr) - 1 {
            set ret_val w/= i <- Qubit_Error(q_arr[i], probs );
        }
        return ret_val;
    }

    function wrapAncillaError(q : Qubit, probs : Int[]) : Qubit_Error {
        return Qubit_Error(q, probs);
    }

    function convertQubitErrorToQubit(qe : Qubit_Error) : Qubit {
        let (q, e) = qe!;
        return q;
    }

    function convertQubitToQubitError(q : Qubit, probs : Int[]) : Qubit_Error {
        return Qubit_Error(q, probs);
    }

    function convertQubitArrayToQubitErrorArray(qubit_arr : Qubit[], probs : Int[]) : Qubit_Error[] {
        if Length(qubit_arr) == 0 {
            return [];
        }
        mutable ret_val = [Qubit_Error(qubit_arr[0], probs), size = Length(qubit_arr)];
        
        for i in 0 .. Length(qubit_arr) - 1 {
            set ret_val w/= i <- Qubit_Error(qubit_arr[i], probs);
        }
        return ret_val;
    }

    function convertQubitErrorArrayToQubitArray(qe_arr : Qubit_Error[]) : Qubit[] {
        if Length(qe_arr) == 0 {
            return [];
        }
        let (a, b) = qe_arr[0]!;
        mutable ret_val = [a, size = Length(qe_arr)];

        for i in 0 .. Length(qe_arr) - 1 {
            let (q, p) = qe_arr[i]!;
            set ret_val w/= i <- q;
        }
        return ret_val;

    }

    operation causeError(q: Qubit, prob_error: Int[]) : Unit is Adj{
        body(...){
            _causeError(q,prob_error);
        }
        controlled (controls, ...) {
            for i in controls {
                _causeError(i, get_Ctrl_Prob());
            }

        }
        adjoint(...){
        }
    }

    //operation to cause errors before ErrorWrapped gates
    //prob_error is currently of length 2 for X and Z errors
    //if you want to cause different types of errors, add more if statements after and
    //change the get_(insert_type)_Prob() functions to give an Int[] of the appropriate length
    operation _causeError(q : Qubit, prob_error : Int[]) : Unit{
        mutable random_num = DrawRandomInt(0, 1000000);

        if (random_num < prob_error[0]) {
            Message("X error");
            X(q);
        }

        set random_num = DrawRandomInt(0, 1000000);
        if (random_num < prob_error[1]) {
            Message("Z error");
            Z(q);
        }
    }

    ////basic gates that operate directly on Qubit_Errors


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

    

    operation MeasureReset_Error(qubit : Qubit_Error) : Unit is Adj + Ctl {
        body(...) {
            let (q, e) = qubit!;
            if M(q) == One {
                X(q);
            }
            
        }
        controlled (controls, ...) {
            MeasureReset_Error(qubit);
        }
        adjoint (...) {
            MeasureReset_Error(qubit);
        }
        controlled adjoint (...) {
            MeasureReset_Error(qubit);
        }
    }

    operation MeasureResetAll_Error(le : Qubit_Error[]) : Unit is Adj + Ctl {
        body (...){
            for q in le {
                MeasureReset_Error(q);
            }
        }
        controlled (controls, ...){
            MeasureResetAll_Error(le);
        }
        adjoint (...) {
            MeasureResetAll_Error(le);
        }
        controlled adjoint (controls, ...){
            MeasureResetAll_Error(le);
        }
    }
    
    operation Reset_Error(qubit : Qubit_Error) : Unit {
        body(...) {
            let (q, e) = qubit!;
            Reset(q);
        }
        controlled (controls, ...) {
            Reset_Error(qubit);
        }
        adjoint (...) {
            Reset_Error(qubit);
        }
        controlled adjoint (...) {
            Reset_Error(qubit);
        }
        
    }

    operation ResetAll_Error(le : Qubit_Error[]) : Unit is Adj + Ctl{
        body (...){
            for q in le {
                Reset_Error(q);
            }
        }
        controlled (controls, ...){
            ResetAll_Error(le);
        }
        adjoint (...) {
            ResetAll_Error(le);
        }
        controlled adjoint (controls, ...){
            ResetAll_Error(le);
        }
        
    }

    operation SWAP_Gate_Error(q1 : Qubit_Error, q2 : Qubit_Error) : Unit is Adj + Ctl {
        CNOT_Gate_Error(q1, q2);
        CNOT_Gate_Error(q2, q1);
        CNOT_Gate_Error(q1, q2);
    }

 

    //necessary functions copied from MicrosoftQuantumCrypto library

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


    // some changes due to ancilla
    /// # Summary
    /// Applies a single-qubit operation to each element in a register. 
    /// Wrapper to choose different operations depending on the cost metric.
    
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

    /// # Summary
    /// Applies the doubly-controlled NOT (CCNOT) gate
    /// to three qubits. Wrapper for alternative CCNOT
    /// circuits.
    ///
    /// # Inputs
    /// ## control1
    /// The first control qubit
    /// ## control2		
    /// The second control qubit
    /// ## target
    /// The output qubit 
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


    //------Low-T circuits-----//

    // /// # Summary
    // /// CCNOT gate over the Clifford+T gate set, in T-depth 1, according to Selinger
    // /// # Remarks
    // ///
    // /// # References
    // /// - [ *P. Selinger*,
    // ///        Phys. Rev. A 87: 042302 (2013)](http://doi.org/10.1103/PhysRevA.87.042302)
    // /// # See Also
    // /// - For the circuit diagram see Figure 1 on
    // ///   [ Page 3 of arXiv:1210.0974v2 ](https://arxiv.org/pdf/1210.0974v2.pdf#page=2)
    operation ccnot_T_depth_1_Error (control1 : Qubit_Error, control2 : Qubit_Error, target : Qubit_Error) : Unit is Adj + Ctl {
        use temp = Qubit[4] {
            mutable auxillaryRegister = wrapAncillaErrorArray(temp, get_Ancilla_Prob());
            MeasureResetAll_Error(auxillaryRegister);

            // apply UVU† where U is outer circuit and V is inner circuit
            within{
                TDepthOneCCNOTOuterCircuit_Error(auxillaryRegister + [target, control1, control2]);
            } apply {
                TDepthOneCCNOTInnerCircuit_Error(auxillaryRegister + [target, control1, control2]);
            }


            MeasureResetAll_Error(auxillaryRegister);
        }
    }

    /// # See Also
    /// - Used as a part of @"Microsoft.Quantum.Samples.UnitTesting.TDepthOneCCNOT"
    /// - For the circuit diagram see Figure 1 on
    ///   [ Page 3 of arXiv:1210.0974v2 ](https://arxiv.org/pdf/1210.0974v2.pdf#page=2)
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

    /// # See Also
    /// - Used as a part of @"Microsoft.Quantum.Samples.UnitTesting.TDepthOneCCNOT"
    /// - For the circuit diagram see Figure 1 on
    ///   [ Page 3 of arXiv:1210.0974v2 ](https://arxiv.org/pdf/1210.0974v2.pdf#page=2)

    operation TDepthOneCCNOTInnerCircuit_Error (qs : Qubit_Error[]) : Unit is Adj + Ctl {
        Fact(Length(qs)== 7, "7 qubits are expected");
        ApplyToEachCA(Adjoint T_Gate_Error, qs[0 .. 2]);
        ApplyToEachCA(T_Gate_Error, qs[3 .. 6]);
    }

    /// # Summary
    /// Computes the logical AND of two qubit inputs, 
    /// setting a target qubit to the result. The target
    /// qubit must be initialized to 0.
    ///
    /// # Inputs
    /// ## control1
    /// The first bit in the AND
    /// ## control2
    /// The second bit in the AND
    /// ## target
    /// The output qubit which must be 0
    ///
    /// # Remarks
    /// This has the same action as CCNOTWrapper when the target is 0.
    /// This function is a wrapper that may use circuits optimized 
    /// for AND, rather than a general CCNOTWrapper.
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
    /// # Summary
    /// Sequential QRAM look-up, where a qubit register storing an 
    /// address controls which element of a classical array is written 
    /// to a quantum registers
    ///
    /// # Description
    /// Sequentially iterates through all addresses, compares the address to 
    /// the address register, and if they are equal, it writes the value from the 
    /// classical array to a quantum register. The type of the classical array,
    /// and the action within the classical array are left unspecified. The quantum
    /// register is implicit in the `QuantumWrite` operation.
    ///
    /// Bits in the table beyond the range of address are ignored.
    /// It is assumed that the address will never store a value beyond the end of the table.
    /// Invalid addresses cause undefined behavior.
    ///
    /// # Input
    /// ## table
    /// The classical table whose values will be indexed and written into the target register.
    /// ## QuantumWrite
    /// A controllable operation which will write a specific value to some quantum register. 
    /// This could be an in-place XOR, for example.
    /// ## address
    /// Determines which integer from the table will be xored into the target.
    /// 
    /// # References
    /// Much of this code is directly adapted from the following reference, with slight
    /// modifications to fit with the rest of the Microsoft.Quantum.Crypto library:
    /// Craig Gidney. 2019. "Windowed Quantum Arithmetic", https://arxiv.org/abs/1905.07682
    operation EqualLookup_Error<'T> (table: 'T[], QuantumWrite : (('T) => Unit is Ctl + Adj), address: LittleEndian_Error) : Unit {
        body (...) {
            Controlled EqualLookup_Error([], (table, QuantumWrite, address));
        }
        controlled (cs, ...) {
            if (Length(table) == 0) {
                fail "Can't lookup values in an empty table.";
            }
            // Compress controls: we only want a single control at one time
            if (Length(cs) > 1){
                use temp = Qubit() {
                    mutable controlQubit = wrapAncillaError(temp, get_Ancilla_Prob());
                    MeasureReset_Error(controlQubit);

                    CheckIfAllOnes_Error(wrapAncillaErrorArray(cs, get_Prob()), controlQubit);
                    (Controlled EqualLookup_Error)([temp], (table, QuantumWrite, address));
                    (Adjoint CheckIfAllOnes_Error)(wrapAncillaErrorArray(cs, get_Prob()), controlQubit);

                    MeasureReset_Error(controlQubit);
                }
            } else {

                // Drop high bits that would place us beyond the range of the table.
                let maxAddressLen = BitSizeI(Length(table));
                if (maxAddressLen < Length(address!)) {
                    let kept = LittleEndian_Error(address![0..maxAddressLen - 1]);
                    (Controlled EqualLookup_Error)(cs, (table, QuantumWrite, kept));
                } else {

                    // Drop inaccessible parts of table.
                    let maxTableLen = 1 <<< Length(address!);
                    if (maxTableLen < Length(table)) {
                        let kept = table[0..maxTableLen-1];
                        (Controlled EqualLookup_Error)(cs, (kept, QuantumWrite, address));
                    } elif (Length(table) == 1) {

                        // Base case: singleton table.
                        ApplyToEachWrapperCA(X_Gate_Error, address!);
                        (Controlled QuantumWrite)(cs + convertQubitErrorArrayToQubitArray(address!), (table[0]));
                        ApplyToEachWrapperCA(Adjoint X_Gate_Error, address!);
                    } else {

                        // Recursive case: divide and conquer.
                        let highBit = address![Length(address!) - 1];
                        let restAddress = LittleEndian_Error(address![0..Length(address!) - 2]);
                        let h = 1 <<< (Length(address!) - 1);
                        let lowTable = table[0..h-1];
                        let highTable = table[h..Length(table)-1];
                        use temp = Qubit() {
                            mutable q = wrapAncillaError(temp, get_Ancilla_Prob());
                            MeasureReset_Error(q);

                            // Store 'all(controls) and not highBit' in q.
                            X_Gate_Error(highBit);
                            if (Length(cs) > 0){
                                 AndWrapper_Error(convertQubitToQubitError(cs[0], get_Prob()), highBit, q);
                            } else {
                                CNOT_Gate_Error(highBit, q);
                            }
                            X_Gate_Error(highBit);

                            // Do lookup for half of table where highBit is 0.
                            (Controlled EqualLookup_Error)([temp], (lowTable, QuantumWrite, restAddress));

                            // Flip q to storing 'all(controls) and highBit'.
                            if (Length(cs) > 0){
                                CNOT_Gate_Error(convertQubitToQubitError(cs[0], get_Prob()), q);
                            } else {
                                X_Gate_Error(q);
                            }

                            // Do lookup for half of table where highBit is 1.
                            (Controlled EqualLookup_Error)([temp], (highTable, QuantumWrite, restAddress));

                            // Eager uncompute 'q = all(controls) and highBit'.
                            if (Length(cs) > 0){
                                 (Adjoint AndWrapper_Error)(convertQubitToQubitError(cs[0], get_Prob()), highBit, q);
                            } else {
                                CNOT_Gate_Error(highBit, q);
                            }

                            MeasureReset_Error(q);
                        }
                    }
                }
            }
        }
        adjoint (...) {
            (Controlled EqualLookup_Error)([], (table, (Adjoint QuantumWrite), address));
        }
        controlled adjoint (controls, ...){
            (Controlled EqualLookup_Error)(controls, (table, (Adjoint QuantumWrite), address));
        }
    }

    /// # Summary
    /// Acts like a CCNOTWrapper, but with one input classical.
    /// It flips the target if the logical AND
    /// of the first two inputs is 1.
    ///
    /// # Inputs
    /// ## control1
    /// Classical bit input
    /// ## control2
    /// Qubit input
    /// ## target
    /// Qubit output
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

    /// # Summary
    /// Acts like a CNOT, but with one input classical.
    /// It flips the target if the first input is true.
    ///
    /// # Inputs
    /// ## control1
    /// Classical bit input
    /// ## target
    /// Qubit output
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

    /// # Summary
    /// Acts like an AND, but with one input classical.
    /// It flips the target if the logical AND
    /// of the first two inputs is 1. Assumes the
    /// target starts in the 0 state.
    ///
    /// # Inputs
    /// ## control1
    /// Classical bit input
    /// ## control2
    /// Qubit input
    /// ## target
    /// Qubit output
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


    //EvenlyPartitionedArray not copied over

    //RandomBigInt not copied over

    //RandomBoundedBigInt not copied over

    //AssertEnoughQubits not copied over

    //DummyIntegerWrapper not copied over

    //ConcatenateOperations not copied over

    //HammingWeightL not copied over

    /// # Summary
    /// Applies a single qubit operation to 
    /// every qubit in an array.
    ///
    /// # Inputs
    /// ## op
    /// The operation to be applied.
    /// ## qubitArray
    /// The qubit array to which `op` is applied.
    ///
    /// # Remarks
    /// The function is identical to ApplyToEachWrapperCA
    /// but has a higher width and lower depth when controlled, 
    /// thanks to a fanout tree.
    operation ApplyToEachLowDepthCA<'T>(op : ('T => Unit is Ctl + Adj), qubitArray : 'T[]) : Unit {
        body(...){
            ApplyToEachCA(op, qubitArray);
        }
        controlled (controls, ...){
            let nQubits=Length(qubitArray);

            use temp = Qubit[nQubits] {
                mutable singleControls = wrapAncillaErrorArray(temp, get_Ancilla_Prob());
                MeasureResetAll_Error(singleControls);

                (Controlled X_Gate_Error)(controls, singleControls[0]);
                FanoutToZero_Error(singleControls[0], singleControls[1..nQubits - 1]);
                for idx in 0..nQubits - 1 {
                    (Controlled op)([temp[idx]], (qubitArray[idx]));
                }
                (Adjoint FanoutToZero_Error)(singleControls[0], singleControls[1..nQubits - 1]);
                (Controlled X_Gate_Error)(controls, singleControls[0]);

                MeasureResetAll_Error(singleControls);
            }

        }
        controlled adjoint auto;
    }

    

    /// # Summary
    /// Rotates a register `xs` of qubits in place by shifting all qubits from the least
    /// significant towards the most significant qubit by one step, placing the
    /// most significant qubit into the least significant postion : 
    /// `(xs[0], xs[1], ..., xs[nQubits-1]) -> (xs[nQubits-1], xs[0], ..., xs[nQubits-2])`
    ///
    /// # Input
    /// ## xs
    /// Qubit register, is replaced with its rotation.
    ///
    /// # Remarks
    /// If the register `xs` encodes an integer, this operation computes a doubling 
    /// modulo `2^Length(xs)-1`.
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

    //CyclicRotateRegisterMultiple not copied over


    /// # Summary
    /// Reverses the order of qubits in a register.
    /// When controlled, it uses
    /// a large number of ancillas but low depth.
    ///
    /// # Input
    /// ## xs
    /// The qubit array to be reversed.
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
                    use temp = Qubit[nControls] {
                        mutable singleControls = wrapAncillaErrorArray(temp, get_Ancilla_Prob());
                        MeasureResetAll_Error(singleControls);

                        (Controlled FanoutControls_Error)(controls,(singleControls));
                        for idxSwap in 0..nControls - 1 {
                            (Controlled SWAP_Gate_Error)([temp[idxSwap]], (xs[idxSwap], xs[nQubits - 1 - idxSwap]));
                        }
                        (Controlled Adjoint FanoutControls_Error)(controls,(singleControls));

                        MeasureResetAll_Error(singleControls);
                    }

                }
            }
        }
        controlled adjoint auto;
    }

    /// # Summary
    /// Uses a tree of CNOT gates to "copy" an input qubit
    /// to an array of output qubits assumed to be 0.
    ///
    /// # Inputs
    /// ## input
    /// The qubit whose state (0 or 1) will be copied
    /// ## outputs
    /// An array of qubits initialized to 0 that will 
    /// be set to the same boolean value as `input`.
    ///
    /// # Reference
    /// Chrisopher Moore. "Quantum circuits : Fanout, 
    ///    Parity, and Counting."
    ///    https : //arxiv.org/pdf/quant-ph/9903046.pdf
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

    /// # Summary
    /// When controlled, fans out the state of the control(s)
    /// to all of the input qubits with CNOTs.
    ///
    /// # Inputs
    /// ## singleControls
    /// Qubits assumed to be 0 which will be returned either all
    /// 1 (if the controls are all 1) or 0 (otherwise).
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

    //FanoutRegister not copied over

    //OppositeCheck not copied over


    /// # Summary
    /// Flips a blank output qubit if and only if all input
    /// control qubits are in the 1 state. Uses clean ancilla
    /// which are returned dirty.
    ///
    /// # Inputs
    /// ## controlQubits
    /// Array of qubits acting like a controlled X on the output
    /// ## blankControlQubits
    /// Qubits initialized to 0 which are used as ancilla.
    /// ## output 
    /// A qubit, assumed to be 0, which is flipped if all control
    /// qubits are 1
    ///
    /// # Remarks
    /// Identical in function to (Controlled X)(controlQubits, (output))
    /// except the depth is lower, the output must be 0, and it uses
    /// ancilla which are not uncomputed.
    /// If controlQubits has n qubits, then this needs n-2 
    /// blankControlQubits.
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

    //checkIfAllZero not copied over


    /// # Summary
    /// Checks if the input register is all ones, and if so, 
    /// flips the output qubit from 0 to 1.
    /// # Inputs
    /// ## xs
    /// Qubit register being checked against all-zeros
    /// ## output
    /// The qubit that will be flipped
    ///
    /// # Remarks
    /// This has the same function as (Controlled X)(xs, (output))
    /// but this explicitly forms a binary tree to achieve a logarithmic
    /// depth. This means it borrows n-1 clean qubits.
    /// It also means that if xs has length 0, it flips the output
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
                    use (temp1, temp2) = (Qubit[nQubits - 2], Qubit()) {
                        mutable spareControls = wrapAncillaErrorArray(temp1, get_Ancilla_Prob());
                        mutable ancillaOutput = wrapAncillaError(temp2, get_Ancilla_Prob());

                        MeasureResetAll_Error(spareControls);
                        MeasureReset_Error(ancillaOutput);

                        CompressControls_Error(xs, spareControls, ancillaOutput);
                        CNOT_Gate_Error(ancillaOutput, output);
                        (Adjoint CompressControls_Error)(xs, spareControls, ancillaOutput);

                        MeasureResetAll_Error(spareControls);
                        MeasureReset_Error(ancillaOutput);
                    }
                }
            }
        }
        controlled (controls, ...){
            CheckIfAllOnes_Error(convertQubitArrayToQubitErrorArray(controls, [0, 0]) + xs, output);
        }
        controlled adjoint auto;
    }

    /// # Summary
    /// Flips the output qubit if and only if all the input qubits are 1.
    /// Uses a method with only 1 ancilla, but linear depth.
    ///
    /// # Inputs
    /// ## controlQubits
    /// Input qubits to check if 1
    /// ## output
    /// Output qubit to flip
    ///
    /// ## References
    /// A. Barenco, C.H. Bennett, R. Cleve, D.P. DiVincenzo, N. Margolus, 
    /// 	P. Shor, T. Sleator, J. Smolin, H. Weinfurter.
    /// 	"Elementary Gates for Quantum Computation"
    ///		https://arxiv.org/abs/quant-ph/9503016v1
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
                borrow temp = Qubit() {
                    mutable ancillaControl = wrapAncillaError(temp, get_Ancilla_Prob());
                    MeasureReset_Error(ancillaControl);

                    LinearMultiControl_Error(controlQubits[0.. nQubits -2], ancillaControl);
                    CCNOTWrapper_Error(controlQubits[nQubits - 1], ancillaControl, output);
                    LinearMultiControl_Error(controlQubits[0.. nQubits -2], ancillaControl);
                    CCNOTWrapper_Error(controlQubits[nQubits - 1], ancillaControl, output);

                    MeasureReset_Error(ancillaControl);
                }

            } elif (nQubits == 5) {
                borrow temp = Qubit() {
                    mutable ancillaControl = wrapAncillaError(temp, get_Ancilla_Prob());
                    MeasureReset_Error(ancillaControl);

                    LinearMultiControl_Error(controlQubits[0 .. nQubits - 3], ancillaControl);
                    LinearMultiControl_Error(controlQubits[nQubits - 2 .. nQubits - 1] + [ancillaControl], output);
                    LinearMultiControl_Error(controlQubits[0 .. nQubits - 3], ancillaControl);
                    LinearMultiControl_Error(controlQubits[nQubits - 2 .. nQubits - 1] + [ancillaControl], output);

                    MeasureReset_Error(ancillaControl);
                }

            } else {
                borrow temp = Qubit() {
                    mutable ancillaControl = wrapAncillaError(temp, get_Ancilla_Prob());
                    MeasureReset_Error(ancillaControl);

                    let m = (nQubits + 1) / 2;
                    CascadeControl_Error(controlQubits[0 .. m - 1], ancillaControl);
                    CascadeControl_Error(controlQubits[m .. nQubits - 1] + [ancillaControl], output);
                    CascadeControl_Error(controlQubits[0 .. m - 1], ancillaControl);
                    CascadeControl_Error(controlQubits[m .. nQubits - 1] + [ancillaControl], output);

                    MeasureReset_Error(ancillaControl);
                }
            }
        }
        controlled (controls, ...){
            LinearMultiControl_Error(convertQubitArrayToQubitErrorArray(controls, [0, 0]) + controlQubits, output);
        }
        controlled adjoint auto;
    }


    /// # Summary
    /// Flips an output qubit if and only if all inputs are 1.
    /// Uses a linear structure which uses 4n Toffoli gates.
    ///
    /// # Inputs
    /// ## controlQubits
    /// Qubits which must be all 1 to flip the output
    /// ## output
    /// Qubit to flip
    ///
    /// ## References
    /// A. Barenco, C.H. Bennett, R. Cleve, D.P. DiVincenzo, N. Margolus, 
    /// 	P. Shor, T. Sleator, J. Smolin, H. Weinfurter.
    /// 	"Elementary Gates for Quantum Computation"
    ///		https://arxiv.org/abs/quant-ph/9503016v1
    operation CascadeControl_Error(controlQubits : Qubit_Error[], output : Qubit_Error) : Unit {
        body (...){
            let nQubits = Length(controlQubits);
            if (nQubits <= 2){
                LinearMultiControl_Error(controlQubits, output);
            } else {
                borrow temp = Qubit[nQubits - 2] {
                    mutable ancillaControls = wrapAncillaErrorArray(temp, get_Ancilla_Prob());
                    MeasureResetAll_Error(ancillaControls);

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

                    MeasureResetAll_Error(ancillaControls);
                }
                
            }
        }
        controlled (controls, ...){
            CascadeControl_Error(convertQubitArrayToQubitErrorArray(controls, [0, 0]) + controlQubits, output);
        }
        controlled adjoint auto;
    }



    //From Microsoft.Quantum.Canon
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


    //From Microsoft.Quantum.Canon
    operation SwapReverseRegister_Error(register : Qubit_Error[]) : Unit is Adj + Ctl {
        let length = Length(register);
        for i in 0..length / 2 - 1 {
            SWAP_Gate_Error(register[i], register[(length - i) - 1]);
        }
    }

    //from Microsoft.Quantum.Measurement
    operation MeasureEachZ_Error(register : Qubit_Error[]) : Result[] {
        mutable results = [];

        for qubit in register {
            set results += [M_Gate_Error(qubit)];
        }
        return results;
    }

    //from Microsoft.Quantum.Measurement
    operation MResetZ_Error(target : Qubit_Error) : Result {
        let (q, p) = target!;
        _causeError(q, p);
        return __quantum__qis__mresetz__body(q);
    }
    
}