
namespace Microsoft.Quantum.Crypto.Error.Arithmetic {
    open Tools;
    open Microsoft.Quantum.Convert;
    open Microsoft.Quantum.Canon;
    open Microsoft.Quantum.Math;
    open Microsoft.Quantum.Diagnostics;
    //open Microsoft.Quantum.Crypto.Basics;
    open Microsoft.Quantum.Crypto.Arithmetic;
    open Microsoft.Quantum.Crypto.Error.Basics;

    //IMPORTANT comments starting with /// were copied over and may not be accurate

    /// # Summary
    /// Carries out a strictly greater than comparison of two integers x
    /// and y encoded in quantum registers. If x>y, then the
    /// result qubit will be flipped, otherwise retain its state.
    ///
    /// # Inputs
    /// ## xs
    /// Qubit register encoding the first integer $x$.
    /// ## ys
    /// Qubit register encoding the second integer $y$
    /// ## carry
    /// Single qubit that will be flipped if $x>y$.
    operation GreaterThanWrapper_Error(xs : LittleEndian_Error, ys : LittleEndian_Error, result : Qubit_Error) : Unit {
        body (...){
            if (IsMinimizeDepthCostMetric()){
                GreaterThanLookAhead_Error(xs, ys, result);
            } elif (IsMinimizeTCostMetric()){
                CKDMGGreaterThan_Error(xs, ys, result);
            } else {
                GreaterThanTTK_Error(xs, ys, result);
            }
        }
        controlled adjoint auto;
    }

    /// Placeholder until we implement the real TTK adder
    operation GreaterThanTTK_Error(xs: LittleEndian_Error, ys: LittleEndian_Error, result: Qubit_Error) : Unit {
        body (...){
            CKDMGGreaterThan_Error(xs, ys, result);
        }
        controlled adjoint auto;
    }

    //GreaterThanConstant not copied over
    //LessThanConstant not copied over

    /// # Summary
    /// Reversible, in-place adder with carry. Given two n-bit integers
    /// `xs` and `ys` encoded in qubit Registers and a
    /// qubit carry, computes the sum of the two
    /// integers where the n least significant bits of the 
    /// result are held in `ys` and the carry out is xored to the
    /// qubit `carry`.
    ///
    /// # Inputs
    /// ## xs
    /// Qubit register encoding the first integer summand.
    /// ## ys
    /// Qubit register encoding the second integer
    /// summand, modified to hold the n least significant bits of
    /// the sum.
    /// ## carry
    /// Carry qubit, xored with the most significant bit of the sum.
    operation AddInteger_Error(xs : LittleEndian_Error, ys : LittleEndian_Error, carry : Qubit_Error) : Unit {
        body (...){
            if (IsMinimizeDepthCostMetric()) {
                CarryLookAheadAdder_Error(xs, ys, carry);	
            } elif (IsMinimizeTCostMetric()) {
                CDKMGAdder_Error(xs, ys, carry);	
            } else {
                RippleCarryAdderTTK_Error(xs, ys, carry);
            }							
        }
        // controlled (controls, ...){
        // 	//(Controlled CarryLookAheadAdder)(controls, (xs, ys, carry));	//low depth
        // 	//(Controlled RippleCarryAdderTTK(xs, ys, carry));				//low width
        // }
        controlled adjoint auto;
    }
    /// Todo: replace with real TTK adder
    operation RippleCarryAdderTTK_Error(xs: LittleEndian_Error, ys: LittleEndian_Error, carry: Qubit_Error) : Unit{
        body (...){
            CDKMGAdder_Error(xs, ys, carry);
        }
        controlled adjoint auto;
    }

    /// # Summary
    /// Reversible, in-place adder with no carry. Given two n-bit integers
    /// `xs` and `ys` encoded in qubit registers and a
    /// qubit carry, computes the sum of the two
    /// integers modulo 2^n, where the result is held in `ys`.
    ///
    /// # Inputs
    /// ## xs
    /// Qubit register encoding the first integer summand.
    /// ## ys
    /// Qubit register encoding the second integer
    /// summand, modified to hold the n least significant bits of
    /// the sum.
    operation AddIntegerNoCarry_Error(xs : LittleEndian_Error, ys : LittleEndian_Error) : Unit {
        body (...){
            if (IsMinimizeDepthCostMetric()) {
                CarryLookAheadAdderNoCarry_Error(xs, ys);
            } elif (IsMinimizeTCostMetric()) {
                CDKMGAdderNoCarry_Error(xs, ys);
            } else {
                RippleCarryAdderNoCarryTTK_Error(xs, ys);
            }
        }
        // controlled (controls, ...){
        // 	(Controlled CarryLookAheadAdderNoCarry)(controls, (xs, ys));
        // }
        controlled adjoint auto;
    }

    /// Todo: replace with real TTK adder
    operation RippleCarryAdderNoCarryTTK_Error(xs: LittleEndian_Error, ys: LittleEndian_Error) : Unit{
        body (...){
            CDKMGAdderNoCarry_Error(xs, ys);
        }
        controlled adjoint auto;
    }

    /// # Summary
    /// Reversible, in-place addition of an integer constant to the integer encoded in the qubit
    /// register `xs`. Given an integer constant and an integer x encoded in the LittleEndian qubit
    /// register `xs`, this operation computes the sum without carry-out, i.e. x + constant mod 2^n, 
    /// where n is the length of `xs`.
    ///
    /// # Input
    /// ## constant
    /// Integer constant.
    /// ## xs
    /// Qubit register encoding the integer $x$.
    ///
    /// # Remarks
    /// Uses one of three internal versions, optimized for width, depth, or T-count.
    /// Currently uses the depth-optimized version.
    operation AddConstant_Error (constant : BigInt, xs : LittleEndian_Error) : Unit
    {
        body (...) {
            if (IsMinimizeDepthCostMetric()) {
                CarryLookAheadAddConstant_Error(constant, xs);
            } elif (IsMinimizeTCostMetric()) {
                CDKMGAddConstant_Error(constant, xs);
            } else {
                _AddConstantLowWidth_Error(constant, xs);
            }
        }
        adjoint auto;
        controlled auto;
        controlled adjoint auto;
    }

    ////////////// End of wrappers /////////////

    /// # Summary
    /// Swaps two little-endian registers of the same length.
    ///
    /// # Inputs
    /// ## xs
    /// Qubit register.
    /// ## ys
    /// Qubit register.
    ///
    /// # Remarks
    /// For n-qubit inputs, the controlled version allocates n ancillas
    /// to fan-out the controls and achieve log(n) depth.
    operation SwapLE_Error(xs : LittleEndian_Error, ys : LittleEndian_Error) : Unit {
        body (...){
            Fact(Length(xs!) == Length(ys!), $"Registers must have equal lengths to swap (current lengths : {Length(xs!)} and {Length(ys!)})");
            for idx in 0..Length(xs!) - 1 {
                SWAP_Gate_Error(xs![idx], ys![idx]);
            }
        }
        controlled(controls, ...){
            Fact(Length(xs!) == Length(ys!), $"Registers must have equal lengths to swap (current lengths : {Length(xs!)} and {Length(ys!)})");
            if (IsMinimizeWidthCostMetric()) {
                for idx in 0 .. Length(xs!) - 1 {
                    (Controlled SWAP_Gate_Error)(controls, (xs![idx], ys![idx]));
                }
            } else {
                use temp = Qubit[Length(xs!)] {
                    mutable singleControls = wrapAncillaErrorArray(temp, get_Ancilla_Prob());

                    (Controlled FanoutControls_Error)(controls, (singleControls));
                    for idx in 0..Length(xs!) - 1 {
                        (Controlled SWAP_Gate_Error)([temp[idx]], (xs![idx], ys![idx]));
                    }
                    (Controlled Adjoint FanoutControls_Error)(controls, (singleControls));
                }
            }
        }
        controlled adjoint auto;
    }
    

    //CopyLittleEndian not copied over

    //PositionsOfOnesInBigInt not copied over

    //MeasureBigInteger not copeid over


    /// # Summary
    /// Reversible, in-place increment operation. Given an integer $x$ encoded 
    /// in the LittleEndian qubit register `xs`, this operation adds the constant $1$ 
    /// to the integer. The result is computed without carry-out, i.e. the operation
    /// computes x + 1 mod 2^n, where n is the length of the register `xs`.
    ///
    /// # Input
    /// ## xs
    /// Qubit register encoding the integer x.
    ///
    /// # References
    /// - Craig Gidney : Constructing large increment gates, Blog post, 2015
    ///   http : //algassert.com/circuits/2015/06/12/Constructing-Large-Increment-Gates.html
    ///
    /// # Remarks
    /// The operation requires n dirty ancilla qubits that are borrowed and returned 
    /// in the same state they are received.
    operation Increment_Error (xs : LittleEndian_Error) : Unit
    {
        body (...) {
            let nQubits = Length(xs!);

            borrow temp = Qubit[nQubits] {

                mutable g = wrapAncillaErrorArray(temp, get_Ancilla_Prob());
                let gs = LittleEndian_Error(g);

                if ( nQubits > 3) {
                    (Adjoint AddIntegerNoCarry_Error) (gs, xs);
                    ApplyToEachWrapperCA(X_Gate_Error, gs!);
                    (Adjoint AddIntegerNoCarry_Error) (gs, xs);
                    ApplyToEachWrapperCA(X_Gate_Error, gs!);
                } elif (nQubits == 3) {
                    CCNOTWrapper_Error (xs![0], xs![1], xs![2]);
                    CNOT_Gate_Error (xs![0], xs![1]);
                    X_Gate_Error (xs![0]);
                } elif (nQubits == 2) {
                    CNOT_Gate_Error (xs![0], xs![1]);
                    X_Gate_Error (xs![0]);
                } elif (nQubits == 1) {
                    X_Gate_Error (xs![0]);
                }
            }
            
        }
        adjoint auto;
        controlled auto;
        controlled adjoint auto;
    }


    /// # Summary
    /// Forward operation to compute the carry when adding an integer constant
    /// to an integer x encoded in a qubit register.
    ///
    /// # Input
    /// ## constant
    /// Integer constant.
    /// ## xs
    /// Qubit register encoding the integer x.
    /// ## gs
    /// Qubit register of dirty qubits, are returned in the same state as received.
    ///
    /// # References
    /// - Thomas Haener, Martin Roetteler, Krysta M. Svore : "Factoring using 2n + 2 qubits
    ///     with Toffoli based modular multiplication", 2016
    ///     https : //arxiv.org/abs/1611.07995
    ///
    /// # Remarks
    /// This operation is used in the ComputeCarry operation below together with its adjoint
    /// to compute the carry and uncompute the corresponding addition. It explicitly takes a
    /// qubit register of dirty qubits as input. 
    operation _ComputeCarryCascade_Error (constant : BigInt, xs : LittleEndian_Error, gs : LittleEndian_Error) : Unit
    { 
        body (...) {
            (Controlled _ComputeCarryCascade_Error) ([], (constant, xs, gs));
        }
        adjoint auto;
        controlled (controls, ...) {
            let nQubits = Length(xs!);
            let constantbittemp = BigIntAsBoolArray(constant, BitSizeL(constant));
            let bitextension = MaxI(nQubits-Length(constantbittemp), 1);
            let constantbits = constantbittemp + [false, size = bitextension];
            for idx in (nQubits-1)..(-1)..2 {
                if (constantbits[idx]) {
                    (Controlled CNOT_Gate_Error) (controls, (xs![idx], gs![idx-1]));
                    (Controlled X_Gate_Error) (controls, (xs![idx]));
                }
                CCNOTWrapper_Error (gs![idx-2], xs![idx], gs![idx-1]);
            }
            if (constantbits[1]) {
                (Controlled CNOT_Gate_Error) (controls, (xs![1], gs![0]));
            }
            if (constantbits[0]) {
                if (constantbits[1]) {
                    (Controlled X_Gate_Error) (controls, (xs![1]));
                }
                (Controlled CCNOTWrapper_Error) (controls, (xs![0], xs![1], gs![0]));
            }

            for idx in 1..(nQubits-2) {
                CCNOTWrapper_Error (gs![idx-1], xs![idx + 1], gs![idx]);
            }
        }
        controlled adjoint auto;
    }

    /// # Summary
    /// Computes the carry when adding the integer constant given in the first argument to the
    /// integer x encoded in the qubit register `xs`, using borrowed qubits.
    /// 
    /// # Input
    /// ## constant
    /// Integer constant.
    /// ## xs
    /// Qubit register encoding the integer x.
    ///
    /// # References
    /// - Thomas Haener, Martin Roetteler, Krysta M. Svore : "Factoring using 2n + 2 qubits
    ///     with Toffoli based modular multiplication", 2016
    ///     https : //arxiv.org/abs/1611.07995
    ///
    /// # Remarks
    /// The specified control operation uses symmetry and mutual cancellation of operations 
    /// to improve on the default implementation that adds a control to every operation.
    operation ComputeCarry_Error (constant : BigInt, xs : LittleEndian_Error, carry : Qubit_Error) : Unit
    {
        body (...) {
            (Controlled ComputeCarry_Error) ([], (constant, xs, carry));
        }
        adjoint auto;
        controlled (controls, ...) {
            let nQubits = Length(xs!);
    
            if (nQubits == 1) {
                if ((constant % 2L) == 1L) {
                    (Controlled CNOT_Gate_Error) (controls, (xs![0], carry));
                }
            } else {
                borrow temp = Qubit[nQubits-1] {
                    mutable gs = wrapAncillaErrorArray(temp, get_Ancilla_Prob());

                    (Controlled CNOT_Gate_Error) (controls, (gs[nQubits - 2], carry));
                    _ComputeCarryCascade_Error(constant, xs, LittleEndian_Error(gs));
                    (Controlled CNOT_Gate_Error) (controls, (gs[nQubits - 2], carry));
                    (Adjoint _ComputeCarryCascade_Error) (constant, xs, 
                                                    LittleEndian_Error(gs));
                }
            }
        }
        controlled adjoint auto;
    }


    /// # Summary
    /// Recursive operation to compute carries in the AddConstant operation below.
    /// Uses a divide-and-conquer approach to recursively compute the carries on one 
    /// half of the qubits while using the other half as dirty ancilla qubits.
    ///
    /// # Input
    /// ## constant
    /// Integer constant.
    /// ## xs
    /// Qubit register encoding the integer x.
    ///
    /// # References
    /// - Thomas Haener, Martin Roetteler, Krysta M. Svore : "Factoring using 2n + 2 qubits
    ///     with Toffoli based modular multiplication", 2016
    ///     https : //arxiv.org/abs/1611.07995
    ///
    /// # Remarks
    /// The specified control operation makes use of symmetry and mutual cancellation of operations 
    /// to improve on the default implementation that adds a control to every operation.
    operation _CarryAndDivide_Error (constant : BigInt, xs : LittleEndian_Error) : Unit
    {
        body (...) {
            (Controlled _CarryAndDivide_Error) ([], (constant, xs));
        }
        adjoint auto;
        controlled (controls, ...) {
            let nQubits = Length(xs!);

            if (nQubits > 1) {
                let lengthLower = nQubits - nQubits/2;
                let lengthHigher = nQubits - lengthLower;
                let xsLower = LittleEndian_Error(xs![0..(lengthLower-1)]);
                let xsHigher = LittleEndian_Error(xs![lengthLower..(nQubits-1)]);
                let constantLower = constant % 2L ^ lengthLower;
                let constantHigher = constant / 2L ^ lengthLower;

                borrow temp = Qubit() {
                    mutable gs = wrapAncillaError(temp, get_Ancilla_Prob());

                    Increment_Error(LittleEndian_Error([gs] + xsHigher!));
                    X_Gate_Error(gs);

                    ApplyToEachWrapperCA(CNOT_Gate_Error(gs, _), xsHigher!);

                    (Controlled ComputeCarry_Error)(controls, (constantLower, xsLower, gs));

                    Increment_Error(LittleEndian_Error([gs] + xsHigher!));
                    X_Gate_Error(gs);

                    (Controlled ComputeCarry_Error)(controls, (constantLower, xsLower, gs));

                    ApplyToEachWrapperCA(CNOT_Gate_Error(gs, _), xsHigher!);
                }
                
                (Controlled _CarryAndDivide_Error)(controls, (constantLower, xsLower));
                (Controlled _CarryAndDivide_Error)(controls, (constantHigher, xsHigher));
            }
        }
        controlled adjoint auto;
    }

    /// # Summary
    /// Reversible, in-place addition of an integer constant to the integer encoded in the qubit
    /// register `xs`. Given an integer constant and an integer x encoded in the LittleEndian qubit
    /// register `xs`, this operation computes the sum without carry-out, i.e. x + constant mod 2^n, 
    /// where n is the length of `xs`.
    ///
    /// # Input
    /// ## constant
    /// Integer constant.
    /// ## xs
    /// Qubit register encoding the integer x.
    ///
    /// # References
    /// - Thomas Haener, Martin Roetteler, Krysta M. Svore : "Factoring using 2n + 2 qubits
    ///     with Toffoli based modular multiplication", 2016
    ///     https : //arxiv.org/abs/1611.07995
    operation _AddConstantLowWidth_Error (constant : BigInt, xs : LittleEndian_Error) : Unit
    {
        body (...) {
            let nQubits = Length(xs!);
            _CarryAndDivide_Error(constant, xs);
            ApplyXorInPlaceL_Error(constant, xs!);
        }
        adjoint auto;
        controlled auto;
        controlled adjoint auto;
    }

    //_AddConstantLowT not copied over


    /// # Summary
    /// Reversible, in-place adder with carry, that uses 
    /// a linear depth circuit, n ancilla qubits, and 
    /// 4n T gates.
    ///
    /// # Description
    /// Given two n-bit integers
    /// encoded in LittleEndian Registers `xs` and `ys`, and a
    /// qubit arry, the operation computes the sum of the two
    /// integers where the n least significant bits of the 
    /// result are held in `ys` and the carry out is xored to the
    /// qubit `carry`.
    ///
    /// # Inputs
    /// ## xs
    /// Qubit register encoding the first integer summand.
    /// ## ys
    /// Qubit register encoding the second integer
    /// summand, is modified to hold the $n$ least significant bits of
    /// the sum.
    /// ## carry
    /// Carry qubit, is xored with the most significant bit of the sum.
    ///
    /// # Remarks
    /// This operation has the same functionality as RippleCarryAdderD, 
    /// RippleCarryAdderCDKM, and RippleCarryAdderTTK.
    ///
    /// # References
    /// Craig Gidney : 
    ///    "Halving the cost of quantum addition"
    ///    Quantum, 2018
    ///    https://arxiv.org/pdf/1709.06648.pdf
    operation CDKMGAdder_Error (xs : LittleEndian_Error, ys : LittleEndian_Error, carry : Qubit_Error) : Unit {
        body (...){
            _CDKMGAdderInner_Error(true, xs, ys, [carry]);
        }
        controlled adjoint auto;
    }

    /// # Summary
    /// Reversible, in-place adder without carry, that uses 
    /// a linear depth circuit, n ancilla qubits, and 
    /// 4n T gates.
    ///
    /// # Description
    /// Given two n-bit integers
    /// encoded in LittleEndian Registers `xs` and `ys`, and a
    /// qubit arry, the operation computes the sum of the two
    /// integers, modulo 2^n, where the n least significant bits of the 
    /// result are held in `ys`
    ///
    /// # Inputs
    /// ## xs
    /// Qubit register encoding the first integer summand.
    /// ## ys
    /// Qubit register encoding the second integer
    /// summand, is modified to hold the $n$ least significant bits of
    /// the sum.
    ///
    /// # Remarks
    /// This operation has the same functionality as RippleCarryAdderNoCarryD, 
    /// RippleCarryAdderNoCarryCDKM, and RippleCarryAdderNoCarryTTK.
    ///
    /// # References
    /// Craig Gidney : 
    ///    "Halving the cost of quantum addition"
    ///    Quantum, 2018
    ///    https://arxiv.org/pdf/1709.06648.pdf
    operation CDKMGAdderNoCarry_Error (xs : LittleEndian_Error, ys : LittleEndian_Error) : Unit {
        body (...){
            _CDKMGAdderInner_Error(false, xs, ys, []);
        }
        controlled adjoint auto;
    }


    /// # Summary
    /// Reversible, in-place adder for a quantum register
    /// and a classical constant, that uses 
    /// a linear depth circuit, n ancilla qubits, and 
    /// less than 4n T gates.
    ///
    /// # Description
    /// Given two n-bit integers, one
    /// encoded in a LittleEndian Registers `xs` and the other
    /// as a classical BigInt, the operation computes the sum of the two
    /// integers modulo 2^n, where the result is written over `xs`
    ///
    /// # Inputs
    /// ## constant
    /// The classical integer summand
    /// ## xs
    /// Qubit register encoding the quantum integer summand.
    ///
    /// # Remarks
    /// The method here is to allocate ancilla qubits to store
    /// the constant, control writing the constant in, and then
    /// do an uncontrolled addition.
    ///
    /// # References
    /// Craig Gidney : 
    ///    "Halving the cost of quantum addition"
    ///    Quantum, 2018
    ///    https://arxiv.org/pdf/1709.06648.pdf
    operation CDKMGAddConstant_Error (constant : BigInt, xs : LittleEndian_Error) : Unit {
        body (...){
            (Controlled CDKMGAddConstant_Error)([], (constant, xs));
        }
        controlled (controls, ...){
            let nQubits = Length(xs!);
            Fact(nQubits>=BitSizeL(constant), $"{constant} is too big to add to a {nQubits} - qubit register");
            
            use temp = Qubit[nQubits] {
                mutable constantQubits = wrapAncillaErrorArray(temp, get_Ancilla_Prob());
                let constants = LittleEndian_Error(constantQubits);
                (Controlled ApplyXorInPlaceL_Error)(controls, (constant, constants!));
                _CDKMGAdderInner_Error(false, constants, xs, []);
                (Controlled Adjoint ApplyXorInPlaceL_Error)(controls, (constant, constants!));
            }
        }
        controlled adjoint auto;
    }

    /// # Summary
    /// Computes a single "block" of addition for the CDKM-Gidney
    /// adder. Takes one bit from each summand and the previous carry,
    /// correctly computes the next carry, and XORs the previous carry
    /// with the bits of the summands.
    ///
    /// # Inputs
    /// ## previousCarry
    /// The previous carry qubit 
    /// ## xQubit
    /// The qubit of the summand that is not overwritten
    /// ## yQubit
    /// The qubit of the summand which is overwritten with the sum
    /// ## nextCarry
    /// The next carry qubit
    ///
    /// # Remarks
    /// `_CDKMGBlockBackward` is almost the inverse of `_CDKMGBlockForward`, except
    /// the backward block will alter the yQubit. However, if they are controlled by 0, then 
    /// they are inverses of each other. This saves in controlled operations, but makes both
    /// operations ill-defined when controlled by 0.
    ///
    /// # References
    /// Figure 2 from Craig Gidney : 
    ///    "Halving the cost of quantum addition"
    ///    Quantum, 2018
    ///    https://arxiv.org/pdf/1709.06648.pdf
    operation _CDKMGBlockForward_Error (previousCarry : Qubit_Error, xQubit : Qubit_Error, yQubit : Qubit_Error, nextCarry : Qubit_Error) : Unit {
        body (...){
            (Controlled _CDKMGBlockForward_Error)([], (previousCarry, xQubit, yQubit, nextCarry));
        }
        controlled (controls, ...){
            CNOT_Gate_Error(previousCarry, xQubit);
            (Controlled CNOT_Gate_Error)(controls, (previousCarry, yQubit));
            AndWrapper_Error(xQubit, yQubit, nextCarry);
            CNOT_Gate_Error(previousCarry, nextCarry);
        }
        controlled adjoint auto;

    }

    /// # Summary
    /// Computes a single backward "block" of addition for the CDKM-Gidney
    /// adder. Uncomputes the next carry qubit, restores the qubit 
    /// from the first summand to its initial value, and writes the 
    /// correct sum value to the the qubit of the second summand.
    ///
    /// # Inputs
    /// ## previousCarry
    /// The previous carry qubit 
    /// ## xQubit
    /// The qubit of the summand that is not overwritten
    /// ## yQubit
    /// The qubit of the summand which is overwritten with the sum
    /// ## nextCarry
    /// The next carry qubit
    ///
    /// # Remarks
    /// `_CDKMGBlockBackward` is almost the inverse of `_CDKMGBlockForward`, except
    /// the backward block will alter the yQubit. However, if they are controlled by 0, then 
    /// they are inverses of each other. This saves in controlled operations, but makes both
    /// operations ill-defined when controlled by 0.
    ///
    /// # References
    /// Figure 2 from Craig Gidney : 
    ///    "Halving the cost of quantum addition"
    ///    Quantum, 2018
    ///    https://arxiv.org/pdf/1709.06648.pdf
    operation _CDKMGBlockBackward_Error (previousCarry : Qubit_Error, xQubit : Qubit_Error, yQubit : Qubit_Error, nextCarry : Qubit_Error) : Unit {
        body (...){
            (Controlled _CDKMGBlockBackward_Error)([], (previousCarry, xQubit, yQubit, nextCarry));
        }
        controlled (controls, ...){
            CNOT_Gate_Error(previousCarry, nextCarry);
            (Adjoint AndWrapper_Error)(xQubit, yQubit, nextCarry);
            CNOT_Gate_Error(previousCarry, xQubit);
            (Controlled CNOT_Gate_Error)(controls, (xQubit, yQubit));
        }
        controlled adjoint auto;
    }


    /// # Summary
    /// Generic operation used for addition with or without carry.
    /// Adds two quantum integers in-place.
    //
    // # Inputs
    /// ## useCarry
    /// If true, the operation will copy out the carry bit.
    /// ## xs
    /// The first quantun integer summand
    /// ## ys
    /// The second quantum integer summand, to be overwritten with the sum.
    /// ## carry
    /// Qubit array for the carry qubit. Should be either length 0 (if useCarry is false)
    /// or length 1 (if useCarry is true).
    ///
    ///
    /// # References
    /// Craig Gidney : 
    ///    "Halving the cost of quantum addition"
    ///    Quantum, 2018
    ///    https://arxiv.org/pdf/1709.06648.pdf
    operation _CDKMGAdderInner_Error(useCarry : Bool, xs : LittleEndian_Error, ys : LittleEndian_Error, carry : Qubit_Error[]) : Unit {
        body (...) {
            (Controlled _CDKMGAdderInner_Error)([], (useCarry, xs, ys, carry));
        }
        controlled (controls, ...) {
            if (useCarry){
                Fact(Length(carry) == 1, $"Expected 1 carry qubit but got {Length(carry)}");
            } else {
                Fact(Length(carry) == 0, $"Expected 0 carry qubits but got {Length(carry)}");
            }
            let nQubits = Length(xs!);
            Fact(nQubits == Length(ys!), $"Qubit registers must have the same size to add");
            if (nQubits == 1){// special case
                if (useCarry){
                    (Controlled RippleCarryAdderTTK_Error)(controls, (xs, ys, carry[0]));
                } else {
                    (Controlled RippleCarryAdderNoCarryTTK_Error)(controls, (xs, ys));
                }
            }
            else {
                use temp = Qubit[nQubits] {
                    mutable carries = wrapAncillaErrorArray(temp, get_Ancilla_Prob());

                    AndWrapper_Error(xs![0], ys![0], carries[0]);
                    for idx in 1..nQubits - 1 {
                        (Controlled _CDKMGBlockForward_Error)(controls, (carries[idx - 1], xs![idx], ys![idx], carries[idx]));
                    }
                    if (useCarry){
                        (Controlled CNOT_Gate_Error)(controls, (carries[nQubits - 1], carry[0]));
                    }
                    for idx in (nQubits - 1)..(-1)..1 {
                        (Controlled _CDKMGBlockBackward_Error)(controls, (carries[idx - 1], xs![idx], ys![idx], carries[idx]));
                    }
                    (Adjoint AndWrapper_Error)(xs![0], ys![0], carries[0]);
                    (Controlled CNOT_Gate_Error)(controls, (xs![0], ys![0]));
                }
            }
        }
        controlled adjoint auto;
    }

    /// # Summary
    /// Carries out a strictly greater than comparison of two integers x
    /// and y, encoded in qubit registers xs and ys. If x>y, then the
    /// restult qubit will be flipped, otherwise retain its state.
    ///
    /// # Inputs
    /// ## xs
    /// Qubit register encoding the first integer x.
    /// ## ys
    /// Qubit register encoding the second integer y
    /// ## carry
    /// Single qubit that will be flipped if x>y.
    ///
    /// # Remarks
    /// This operation has the same functionality as GreaterThan.
    /// Uses the trick that $x - y = (x' + y)'$, where ' denotes one's
    /// complement.
    ///
    /// # References
    /// Craig Gidney : 
    ///    "Halving the cost of quantum addition"
    ///    Quantum, 2018
    ///    https://arxiv.org/pdf/1709.06648.pdf
    operation CKDMGGreaterThan_Error (xs : LittleEndian_Error, ys : LittleEndian_Error, carry : Qubit_Error) : Unit {
        body (...){
            _CDKMGCompareInner_Error(xs, ys, carry);
        }
        controlled adjoint auto;
    }

    //CompareToConstant not copied over



    /// # Summary
    /// Internal function to compare two quantum integers, 
    /// flipping the carry qubit if and only if the first integer
    /// is greater than the second
    ///
    /// # Inputs
    /// ## xs
    /// Qubit register encoding the first integer x.
    /// ## ys
    /// Qubit register encoding the second integer y
    /// ## carry
    /// Single qubit that will be flipped if x>y.
    ///
    /// # Remarks
    /// This operation has the same functionality as GreaterThan.
    /// Uses the trick that $x - y = (x' + y)'$, where ' denotes one's
    /// complement.
    ///
    /// # References
    /// Craig Gidney : 
    ///    "Halving the cost of quantum addition"
    ///    Quantum, 2018
    ///    https://arxiv.org/pdf/1709.06648.pdf
    operation _CDKMGCompareInner_Error (xs : LittleEndian_Error, ys : LittleEndian_Error, carry : Qubit_Error) : Unit {
    body (...) {
            (Controlled _CDKMGCompareInner_Error)([], (xs, ys, carry));
        }
        controlled (controls, ...) {
            let nQubits = Length(xs!);
            if (nQubits == 1){
                X_Gate_Error(ys![0]);
                (Controlled AndWrapper_Error)(controls, (xs![0], ys![0], carry));
                X_Gate_Error(ys![0]);
            } else {
                ApplyToEachCA(X_Gate_Error, ys!);

                use temp = Qubit[nQubits] {
                    mutable carries = wrapAncillaErrorArray(temp, get_Ancilla_Prob());

                    AndWrapper_Error(xs![0], ys![0], carries[0]);
                    for idx in 1..nQubits - 1 {
                        _CDKMGBlockForward_Error (carries[idx - 1], xs![idx], ys![idx], carries[idx]);
                    }
                    (Controlled CNOT_Gate_Error)(controls, (carries[nQubits - 1], carry));
                    for idx in (nQubits - 1)..(-1)..1 {
                        (Adjoint _CDKMGBlockForward_Error)(carries[idx - 1], xs![idx], ys![idx], carries[idx]);
                    }
                    (Adjoint AndWrapper_Error)(xs![0], ys![0], carries[0]);
                }
                
                ApplyToEachCA(Adjoint X_Gate_Error, ys!);
            }
        }
        controlled adjoint auto;
    }


    /// # Summary
    /// Reversible, in-place adder with carry, that uses 
    /// a logarithmic depth carry look-ahead circuit with
    /// 2n - o(n) ancilla qubits. 
    ///
    /// # Description
    /// Given two n-bit integers
    /// encoded in LittleEndian Registers `xs` and `ys`, and a
    /// qubit arry, the operation computes the sum of the two
    /// integers where the n least significant bits of the 
    /// result are held in `ys` and the carry out is xored to the
    /// qubit `carry`.
    ///
    /// # Inputs
    /// ## xs
    /// Qubit register encoding the first integer summand.
    /// ## ys
    /// Qubit register encoding the second integer
    /// summand, is modified to hold the $n$ least significant bits of
    /// the sum.
    /// ## carry
    /// Carry qubit, is xored with the most significant bit of the sum.
    ///
    /// # Remarks
    /// This operation has the same functionality as RippleCarryAdderD, 
    /// RippleCarryAdderCDKM, and RippleCarryAdderTTK, but uses ancilla qubits
    /// and has logarithmic depth.
    ///
    /// If `ys` has more qubits than `xs`, the adder would simply ignore the leading
    /// bits of `ys`. Since this is likely undesired behaviour, the operation
    /// instead throws an exception if they are not the same size.
    ///
    /// # References
    /// Thomas G. Graper, Samuel A. Kutin, Eric M. Rains, Krysta M. Svore : 
    ///    "A Logarithmic-Depth Quantum Carry - Lookahead Adder"
    ///    Quantum Information and Computation, 2006
    ///    https : //arxiv.org/abs/quant - ph/0406142
    operation CarryLookAheadAdder_Error(xs : LittleEndian_Error, ys : LittleEndian_Error, carry : Qubit_Error) : Unit {
        body (...){
            //Odd bit-lengths are much less expensive so we add an extra qubit
            // and do everything as an even bit-length addition
            if (Length(xs!) % 2 == 0){
                use temp = Qubit() {
                    mutable bonusQubit = wrapAncillaError(temp, get_Ancilla_Prob());

                    _CLAAdderImpl_Error(CNOT_Gate_Error, CCNOTWrapper_Error, AndWrapper_Error, false, xs! + [bonusQubit], ys! + [carry], []);
                }
            } else {
                _CLAAdderImpl_Error(CNOT_Gate_Error, CCNOTWrapper_Error, AndWrapper_Error, true, xs!, ys!,  [carry]);
            }
        }
        controlled adjoint auto;
    }


    /// # Summary
    /// Reversible, in-place adder with no carry, that uses 
    /// a logarithmic depth carry look-ahead circuit with
    /// 2n - o(n) ancilla qubits. 
    ///
    /// #Description
    /// Given two n-bit integers
    /// encoded in LittleEndian Registers `xs` and `ys`, and a
    /// qubit arry, the operation computes the sum of the two
    /// integers modulo 2^n, where the result is held in `ys`.
    ///
    /// # Inputs
    /// ## xs
    /// Qubit register encoding the first integer summand.
    /// ## ys
    /// Qubit register encoding the second integer
    /// summand, is modified to hold the n least significant bits of
    /// the sum.
    ///
    /// # Remarks
    /// This operation has the same functionality as RippleCarryAdderNoCarryD, 
    /// RippleCarryAdderNoCarryCDKM, and RippleCarryAdderNoCarryTTK, but uses 
    /// ancilla qubits and has logarithmic depth.
    ///
    /// If `ys` has more qubits than `xs`, the adder would simply ignore the leading
    /// bits of `ys`. Since this is likely undesired behaviour, the operation
    /// instead throws an exception if they are not the same size.
    ///
    /// # References
    /// Thomas G. Graper, Samuel A. Kutin, Eric M. Rains, Krysta M. Svore : 
    ///    "A Logarithmic - Depth Quantum Carry - Lookahead Adder"
    ///    Quantum Information and Computation, 2006
    ///    https : //arxiv.org/abs/quant - ph/0406142

    operation CarryLookAheadAdderNoCarry_Error(xs : LittleEndian_Error, ys : LittleEndian_Error) : Unit {
        body(...){
            _CLAAdderImpl_Error(CNOT_Gate_Error, CCNOTWrapper_Error, AndWrapper_Error, false, xs!, ys!, []);
        }
        controlled adjoint auto;
    }


    /// # Summary
    /// Reversible, in - place addition of an integer constant to the integer encoded in the qubit
    /// register `xs`. Given an integer constant and an integer $x$ encoded in the LittleEndian qubit
    /// register `xs`, this operation computes the sum without carry - out, i.e. $x + constant \mod 2 ^ n$, 
    /// where $n$ is the length of `xs`.
    ///
    /// # Input
    /// ## constant
    /// Integer constant.
    /// ## xs
    /// LittleEndian qubit register encoding the integer $x$.
    ///
    /// # Remarks
    /// This has the same function as _AddConstantLowT and _AddConstantLowWidth
    /// but this has logarithmic depth and 2n - o(n) ancilla.
    operation CarryLookAheadAddConstant_Error(constant : BigInt, xs : LittleEndian_Error) : Unit {
        body(...){
            let nQubits = Length(xs!);
            Fact(nQubits>=BitSizeL(constant), $"{constant} is too big to add to a {nQubits} - qubit register");
            let constantArray = BigIntAsBoolArray(constant, BitSizeL(constant)) + [false, size = nQubits - BitSizeL(constant)];
            _CLAAdderImpl_Error(
                ClassicalCNOT_Error, 
                ClassicalCCNOT_Error, 
                ClassicalAND_Error, 
                false, 
                constantArray[0.. nQubits - 1], 
                xs!, 
                []
            );
        }
        controlled adjoint auto;
    }



    /// # Summary
    /// Internal function for carry-look ahead adding. 
    /// Adds a classical or quantum input
    /// to a quantum input, using a carry
    /// if `useCarry` is true.
    ///
    /// # Inputs
    /// ## cqCNOT
    /// Acts like a CNOT, but the first input can
    /// be either a Bool or a Qubit. If it is a Qubit,
    /// it is a CNOT; if it is a Bool, then its a conditional
    /// X gate
    /// ## cqCCNOTWrapper
    /// Acts like a CCNOTWrapper, but the first input can
    /// be either a Bool or a Qubit. If it is a Qubit,
    /// it is a CCNOTWrapper; if it is a Bool, then its a conditional
    /// CNOT gate (between the remaining Qubit inputs)
    /// ## cqAND
    /// The same action as cqCCNOTWrapper, but we can use a function
    /// optimized for the case where we are guaranteed that the
    /// target qubit starts in the 0 state.
    /// ## useCarry
    /// Determines whether the function uses a carry (if true)
    /// or does not use a carry (addition mod 2^n) (if false)
    /// ## xs
    /// Array of the first integer to be added (classical or quantum)
    /// ## ys 
    /// Qubit register of the second integer to be added (to contain 
    /// output)
    /// ## carry
    /// Single qubit for the carry (if `useCarry` is true) or 
    /// length-0 qubit array (if `useCarry` is false). Other lengths
    /// will cause errors
    operation _CLAAdderImpl_Error <'T> (
        cqCNOT : (('T, Qubit_Error) => Unit is Ctl + Adj),
        cqCCNOTWrapper : (('T, Qubit_Error, Qubit_Error) => Unit is Ctl + Adj),
        cqAND : (('T, Qubit_Error, Qubit_Error) => Unit is Ctl + Adj),
        useCarry : Bool, 
        xs : 'T[], 
        ys : Qubit_Error[], 
        carry : Qubit_Error[]
    ) : Unit {
        body(...){
            (Controlled _CLAAdderImpl_Error)([], (cqCNOT,cqCCNOTWrapper, cqAND, useCarry, xs, ys, carry));
        }
        controlled(controls, ...){
            //Control logic : The circuit can be split into 5 steps : 
            // 1) Prepare the initial carries
            // 2) Compute all carries
            // 3) Compute the sum
            // 4) Uncompute the carries
            // 5) Uncompute the initial carries
            //
            // We only need to control step 3, since the others
            // will uncompute themselves.
            // However : The uncompute steps don't apply
            // every operation to the first and last qubits, 
            // so those operations are controlled.
            let nQubits = Length(xs);
            
            Fact(nQubits == Length(ys), $"Qubit registers must have the same length to add;
                first has length {Length(xs)} and second has length {Length(ys)}");

            if (useCarry){
                Fact(Length(carry) == 1, $"Carry lookahead adder can only use one carry;
                    {Length(carry)} qubits given");
            } else {
                Fact(Length(carry) == 0, $"Carry lookahead adder must have zero-length
                    carry array for no-carry addition");
            }

            if (nQubits==1){// special case
                if (useCarry){
                    (Controlled cqCCNOTWrapper)(controls, (xs[0], ys[0], carry[0]));
                }
                (Controlled cqCNOT)(controls, (xs[0], ys[0]));
            } else {
                let logn = Floor(Lg(IntAsDouble(nQubits)));
                let ancillaSize = 2 * nQubits - HammingWeightI(nQubits) - logn;

                use temp1 = Qubit[ancillaSize] {
                    mutable ancillaQubits = wrapAncillaErrorArray(temp1, get_Ancilla_Prob());

                    let gens = ancillaQubits[0..nQubits - 2] + carry;
                    let propArrays = PropArrays_Error(ancillaQubits[nQubits - 1..ancillaSize - 1], ys);
                    // 1) Compute initial carries
                
                    cqAND(xs[0], ys[0], gens[0]);
                    (Controlled cqCNOT)(controls, (xs[0], ys[0]));//will not be uncomputed
                    for idx in 1..nQubits - 2 {
                        cqAND(xs[idx], ys[idx], gens[idx]);
                        cqCNOT(xs[idx], ys[idx]);
                    }
                    if (useCarry){
                        (Controlled cqCCNOTWrapper)(controls, (xs[nQubits - 1], ys[nQubits -1], gens[nQubits - 1]));//will not be uncomputed
                    }
                    (Controlled cqCNOT)(controls, (xs[nQubits - 1], ys[nQubits -1]));//will not be uncomputed

                    // 2) Compute all carries
                    if (useCarry){
                        (Controlled _LookAheadAndComputePropagateCarries_Error)(controls, (nQubits, propArrays));
                        (Controlled _LookAheadAndComputeGenerateCarries_Error)(controls, (nQubits, propArrays, gens));
                        (Controlled _LookAheadTurnCarriesIntoSum_Error)(controls, (nQubits, propArrays, gens));
                        (Controlled Adjoint _LookAheadAndComputePropagateCarries_Error)(controls, (nQubits, propArrays));
                    } else {
                        _LookAheadAndComputePropagateCarries_Error(nQubits - 1, propArrays);
                        _LookAheadAndComputeGenerateCarries_Error(nQubits - 1, propArrays, gens);
                        _LookAheadTurnCarriesIntoSum_Error(nQubits - 1, propArrays, gens);
                        (Adjoint _LookAheadAndComputePropagateCarries_Error)(nQubits - 1, propArrays);
                    }
                    // 3) Compute the sum
                    // If it's controlled, it needs to fanout
                    // into ancilla to keep the depth low
                    if (Length(controls)>0){
                        use temp2 = Qubit[nQubits - 1] {
                            mutable singleControls = wrapAncillaErrorArray(temp2, get_Ancilla_Prob());

                            (Controlled FanoutControls_Error)(controls, (singleControls));
                            CNOT_Gate_Error(singleControls[0], ys[0]);
                            CCNOTWrapper_Error(singleControls[0], gens[0], ys[1]);
                            for ids in 1..nQubits - 2 {
                                CCNOTWrapper_Error(singleControls[ids], gens[ids], ys[ids + 1]);
                                CNOT_Gate_Error(singleControls[ids], ys[ids]);
                                cqCCNOTWrapper(xs[ids], singleControls[ids], ys[ids]);
                            }
                            (Controlled Adjoint FanoutControls_Error)(controls, (singleControls));
                        }
                    } else {//without controls
                        X_Gate_Error(ys[0]);
                        CNOT_Gate_Error(gens[0], ys[1]);
                        for ids in 1..nQubits - 2 {
                            CNOT_Gate_Error(gens[ids], ys[ids + 1]);
                            X_Gate_Error(ys[ids]);
                            cqCNOT(xs[ids], ys[ids]);
                        }
                    }

                    // 4) Uncompute all carries
                     _LookAheadAndComputePropagateCarries_Error(nQubits - 1, propArrays);
                    (Adjoint _LookAheadTurnCarriesIntoSum_Error)(nQubits - 1, propArrays, gens);
                    (Adjoint _LookAheadAndComputeGenerateCarries_Error)(nQubits - 1, propArrays, gens);
                    (Adjoint _LookAheadAndComputePropagateCarries_Error)(nQubits - 1, propArrays);

                    // 5) Uncompute initial carries
                    (Adjoint cqAND)(xs[0], ys[0], gens[0]);
                    for ids in 1..nQubits - 2 {
                        cqCNOT(xs[ids], ys[ids]);
                        (Adjoint cqAND)(xs[ids], ys[ids], gens[ids]);
                    }
                        
                    //This final negation had no inverse in step (1)
                    (Controlled ApplyToEachWrapperCA)(controls, (X_Gate_Error, ys[0..nQubits - 2]));
                }
            }
        }
        controlled adjoint auto;
    }
    

    /// # Summary
    /// Carries out a strictly greater than comparison of two integers x
    /// and y, encoded in qubit registers xs and ys. If x>y, then the
    /// restult qubit will be flipped, otherwise retain its state.
    ///
    /// # Inputs
    /// ## xs
    /// Qubit register encoding the first integer x.
    /// ## ys
    /// Qubit register encoding the second integer y
    /// ## carry
    /// Single qubit that will be flipped if x>y.
    ///
    /// # Remarks
    /// This operation has the same functionality as GreaterThan.
    /// Uses the trick that $x - y = (x' + y)'$, where ' denotes one's
    /// complement.
    ///
    /// # References
    /// Thomas G. Graper, Samuel A. Kutin, Eric M. Rains, Krysta M. Svore : 
    ///    "A Logarithmic - Depth Quantum Carry - Lookahead Adder"
    ///    Quantum Information and Computation, 2006
    ///    https : //arxiv.org/abs/quant - ph/0406142
    /// This does not implement the comparator described in the reference, 
    /// but simply alters the addition circuit to only output the carry.
    operation GreaterThanLookAhead_Error(xs : LittleEndian_Error, ys : LittleEndian_Error, carry : Qubit_Error) : Unit {
        body (...){
            (Controlled GreaterThanLookAhead_Error)([], (xs, ys, carry));
        }
        controlled (controls, ...){
            if (Length(xs!) % 2 == 0){
                use temp = Qubit[2] {	
                    mutable bonusQubits = wrapAncillaErrorArray(temp, get_Ancilla_Prob());

                    (Controlled GreaterThanLookAhead_Error)(controls, (
                        LittleEndian_Error(xs! + [bonusQubits[0]]),
                        LittleEndian_Error(ys! + [bonusQubits[1]]),
                        carry)
                    );
                }

            } else {
                ApplyToEachWrapperCA(X_Gate_Error, ys!);
                (Controlled _CompareLookAheadImpl_Error)(controls,  (
                    CNOT_Gate_Error,
                    CCNOTWrapper_Error,
                    AndWrapper_Error,
                    xs!, 
                    ys!, 
                    carry
                ));
                ApplyToEachWrapperCA(X_Gate_Error, ys!);
            }
        }
        controlled adjoint auto;
    }

    //GreaterThanConstantLookAhead not copied over

    //LessThanConstantLookAhead not copied over


    /// # Summary
    /// Computes the only the carry of the sum of
    /// a quantum/classical integer and a quantum integer.
    /// Used internally for comparators.
    ///
    /// # Inputs
    /// ## cqCNOT
    /// Acts like a CNOT, but the first input can
    /// be either a Bool or a Qubit. If it is a Qubit,
    /// it is a CNOT; if it is a Bool, then its a conditional
    /// X gate
    /// ## cqCCNOTWrapper
    /// Acts like a CCNOTWrapper, but the first input can
    /// be either a Bool or a Qubit. If it is a Qubit,
    /// it is a CCNOTWrapper; if it is a Bool, then its a conditional
    /// CNOT gate (between the remaining Qubit inputs)
    /// ## cqAND
    /// The same action as cqCCNOTWrapper, but we can use a function
    /// optimized for the case where we are guaranteed that the
    /// target qubit starts in the 0 state.
    /// ## xs
    /// Array of the first integer to be compared (classical or quantum)
    /// Assumed to be already complemented (all bits flipped)
    /// ## ys 
    /// Qubit register of the second integer to be compared (to contain 
    /// output)
    /// ## carry
    /// Single qubit for the carry; flipped if the 
    /// second input is strictly greater than the first
    ///
    /// # Remarks
    /// The comparators use the fact that (c' + x)'=x-c
    /// to the comparison; this circuit asssumes that 
    /// `xs` is already complemented.
    operation _CompareLookAheadImpl_Error<'T>(
        cqCNOT : (('T, Qubit_Error) => Unit is Ctl + Adj),
        cqCCNOTWrapper : (('T, Qubit_Error, Qubit_Error) => Unit is Ctl + Adj),
        cqAND : (('T, Qubit_Error, Qubit_Error) => Unit is Ctl + Adj),
        xs : 'T[], //pre-complemented
        ys : Qubit_Error[], 
        carry : Qubit_Error
    ) : Unit {
        body(...){
            (Controlled _CompareLookAheadImpl_Error)([], (
                cqCNOT,
                cqCCNOTWrapper,
                cqAND,
                xs, 
                ys, 
                carry
            ));
        }
        controlled(controls, ...){
            let nQubits = Length(xs);
            if (nQubits==1){//edge case
                (Controlled cqCCNOTWrapper)(controls, (xs[0], ys[0], carry));
            } else {
                let logn = Floor(Lg(IntAsDouble(nQubits)));
                let ancillaSize = 2 * nQubits - Floor(Lg(IntAsDouble(nQubits - 1))) - 3;

                use temp1 = Qubit[ancillaSize] {
                    mutable ancillaQubits = wrapAncillaErrorArray(temp1, get_Ancilla_Prob());

                    let gens = ancillaQubits[0..nQubits - 2] + [carry];
                    let propArrays = PropArrays_Error(ancillaQubits[nQubits - 1..ancillaSize - 1], ys);
                

                    // 1) Compute initial carries
                    for idx in 0..nQubits - 2 {
                        cqAND(xs[idx], ys[idx], gens[idx]);
                        cqCNOT(xs[idx], ys[idx]);			
                    }
                    (Controlled cqCCNOTWrapper)(controls, (xs[nQubits - 1], ys[nQubits - 1], gens[nQubits - 1]));//will not be uncomputed
                    cqCNOT(xs[nQubits - 1], ys[nQubits - 1]);

                    // 2) Compute all carries
                    _LookAheadAndComputePropagateCarries_Error(nQubits, propArrays);
                    (Controlled _LookAheadAndComputeGenerateCarries_Error)(controls, (nQubits, propArrays, gens));
                    (Controlled _LookAheadTurnCarriesIntoSum_Error)(controls, (nQubits, propArrays, gens));
                    (Adjoint _LookAheadTurnCarriesIntoSum_Error)(nQubits - 1, propArrays, gens);
                    (Adjoint _LookAheadAndComputeGenerateCarries_Error)(nQubits - 1, propArrays, gens);
                    (Adjoint _LookAheadAndComputePropagateCarries_Error)(nQubits, propArrays);

                     
                    // 5) Uncompute initial carries
                    for ids in 0..nQubits - 2 {	
                        cqCNOT(xs[ids], ys[ids]);
                        (Adjoint cqAND)(xs[ids], ys[ids], gens[ids]);
                    }
                    cqCNOT(xs[nQubits - 1], ys[nQubits - 1]);
                }
            }
        }
        controlled adjoint auto;
    }

    /// # Summary
    /// Divides an array of qubits into a two-dimensional array
    /// necessary for running a lookahead carry addition.
    /// Since the indexing is complicated, rather than
    /// compute it directly, it simply iterates over all
    /// carry propagation bits and sequential assigns them
    /// a bit in the input array.
    ///
    /// # Inputs
    /// ## props
    /// A blank qubit array to be reassigned.
    /// ## ys
    /// A qubit array expected to contain P_0, the 0th level
    /// of carry propagation qubits
    ///
    /// # Outputs
    /// A two-dimensional qubit array such that Proparrays[t][x] corresponds
    /// to the xth element in level t, where t ranges from 0 to 
    /// Floor(log n) - 1 and x ranges from 1 to Floor(n/2^t)-1.
    /// Note that Proparrays[0][x] references elements of ysarray.
    /// 
    /// # References
    /// Thomas G. Graper, Samuel A. Kutin, Eric M. Rains, Krysta M. Svore, 
    ///    A Logarithmic-Depth Quantum Carry-Lookahead Adder
    ///    https : //arxiv.org/abs/quant-ph/0406142
    ///	   This operation prepares the set of arrays P as described in
    ///    Section 3.
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
    

    /// # Summary
    /// Given carry propagation bits for sequential elements, 
    /// this computes the rest of the carry propagation bits.
    /// 
    ///
    /// # Inputs
    /// ## nQubits
    /// The number of qubits to carry on (which can be
    /// less than the number of qubits in gens)
    /// ## propArrays
    /// A two-dimensional array referencing different levels of
    /// carry propagation qubits (intended to be the output of
    /// PropArrays), with the 0th level computed.
    ///
    /// # References
    /// Thomas G. Graper, Samuel A. Kutin, Eric M. Rains, Krysta M. Svore, 
    ///    A Logarithmic-Depth Quantum Carry-Lookahead Adder
    ///    https : //arxiv.org/abs/quant-ph/0406142
    ///	   This operation computes step 1 from Section 3.
    ///		(the blue gates in Figure 5)
    operation _LookAheadAndComputePropagateCarries_Error(nQubits : Int, propArrays : Qubit_Error[][]) : Unit {
        body (...){
            let logn = Floor(Lg(IntAsDouble(nQubits)));
            for idxRound in 1..logn-1 {
                for idxProps in 1..nQubits / (2 ^ idxRound) - 1 {
                        AndWrapper_Error(propArrays[idxRound - 1][2 * idxProps], propArrays[idxRound - 1][2 * idxProps + 1], propArrays[idxRound][idxProps]);
                }
            }
        }
        controlled (controls, ...){
        //The full adder must uncompute these carries at the end, 
        //so we save controls by not controlling this operation.
        //However : When uncomputing, the adder only calls
        //this operation with nQubits-1. Thus, we must
        //control the individual operations that use
        //qubits in the n-1 position.
        //Hence, each of the "rounds" must check whether the
        //indices are high enough to need the controls.
            let logn = Floor(Lg(IntAsDouble(nQubits)));
            // P rounds
            for idxRound in 1..logn - 1 {
                let lognMin1 = Floor(Lg(IntAsDouble(nQubits - 1)));
                for idxProps in 1..nQubits / (2 ^ idxRound) - 1 {
                    if (idxRound > lognMin1 - 1 or idxProps > (nQubits - 1) / (2 ^ idxRound) - 1){
                        (Controlled X_Gate_Error)(controls + convertQubitErrorArrayToQubitArray(propArrays[idxRound-1][2 * idxProps..2 * idxProps + 1]), propArrays[idxRound][idxProps]);
                    } else {
                        AndWrapper_Error(propArrays[idxRound - 1][2 * idxProps], propArrays[idxRound - 1][2 * idxProps + 1], propArrays[idxRound][idxProps]);
                    }
                }
            }
        }
        controlled adjoint auto;
    }


    /// # Summary
    /// Given carry propagation bits and carry generations for
    /// sequential elements, this computes the rest of the
    /// generator carries.
    ///
    /// # Inputs
    /// ## nQubits
    /// The number of qubits to carry on (which can be
    /// less than the number of qubits in gens)
    /// ## propArrays
    /// A two-dimensional array referencing different levels of
    /// carry propagation qubits, pre-computed.
    /// ## gens 
    /// A qubit array of the carry generation qubits, 
    /// initialized with the sequential elements.
    ///
    /// # References
    /// Thomas G. Graper, Samuel A. Kutin, Eric M. Rains, Krysta M. Svore, 
    ///    A Logarithmic-Depth Quantum Carry-Lookahead Adder
    ///    https : //arxiv.org/abs/quant-ph/0406142
    ///	   This operation computes steps 2 from Section 3.
    ///		(the red gates in Figure 5)
    operation _LookAheadAndComputeGenerateCarries_Error(nQubits : Int, propArrays : Qubit_Error[][], gens : Qubit_Error[]) : Unit {
        body (...){
            let logn = Floor(Lg(IntAsDouble(nQubits)));
            for idxRound in 1..logn {
                for idxGens in 0..(nQubits / 2 ^ idxRound) - 1 {
                    CCNOTWrapper_Error(propArrays[idxRound - 1][2 * idxGens + 1], 
                        gens[idxGens * 2 ^ idxRound + 2 ^ (idxRound - 1) - 1],
                        gens[(idxGens + 1) * 2 ^ idxRound - 1]
                    );
                }
            }
        }
        controlled (controls, ...){
            //The full adder must uncompute these carries at the end, 
            //so we save controls by not controlling this operation.
            //However : When uncomputing, the adder only calls
            //this operation with nQubits-1. Thus, we must
            //control the individual operations that use
            //qubits in the n-1 position.
            //Hence, each of the "rounds" must check whether the
            //indices are high enough to need the controls.
            let logn = Floor(Lg(IntAsDouble(nQubits)));
            for idxRound in 1..logn {
                let lognmin1 = Floor(Lg(IntAsDouble(nQubits - 1)));
                for idxGens in 0..(nQubits / 2 ^ idxRound) - 1 {
                    if (idxRound > lognmin1 or idxGens > (nQubits - 1)/(2 ^ idxRound) - 1){
                        (Controlled X_Gate_Error)(controls + [convertQubitErrorToQubit(propArrays[idxRound - 1][2 * idxGens + 1]),
                            convertQubitErrorToQubit(gens[idxGens * (2 ^ idxRound) + 2 ^ (idxRound - 1) - 1])], 
                            (gens[(idxGens + 1) * 2 ^ idxRound - 1])
                        );
                    }  else {
                        CCNOTWrapper_Error(propArrays[idxRound - 1][2 * idxGens + 1], 
                            gens[idxGens * (2 ^ idxRound) + 2^(idxRound - 1) - 1],
                            gens[(idxGens + 1) * (2 ^ idxRound) - 1]
                        );
                    }
                }
            }
        }
        controlled adjoint auto;
    }


    /// # Summary
    /// Given pre-computed carry propagation bits and carry 
    /// generation bits, this computes the carries for the sum
    /// of two integers.
    ///
    /// # Inputs
    /// ## nQubits
    /// The number of qubits to carry on (which can be
    /// less than the number of qubits in gens)
    /// ## propArrays
    /// A two-dimensional array referencing different levels of
    /// carry propagation qubits, fully computed.
    /// ## gens
    /// A qubit array of the carry generation qubits.
    ///
    /// # References
    /// Thomas G. Graper, Samuel A. Kutin, Eric M. Rains, Krysta M. Svore, 
    ///    A Logarithmic-Depth Quantum Carry-Lookahead Adder
    ///    https : //arxiv.org/abs/quant-ph/0406142
    ///	   This operation computes step 3 from Section 3.
    ///	(the green parts of the circuit in Figure 5)
    operation _LookAheadTurnCarriesIntoSum_Error(nQubits : Int, propArrays : Qubit_Error[][], gens : Qubit_Error[]) : Unit {
        body (...){
            let log2nover3 = Floor(Lg(2.0 * IntAsDouble(nQubits) / 3.0));
            for idxRound in log2nover3..(-1)..1 {
                for idxSum in 1.. (nQubits - 2 ^ (idxRound - 1)) / 2 ^ idxRound {
                        CCNOTWrapper_Error(gens[idxSum * (2 ^ idxRound) - 1], 
                            propArrays[idxRound - 1][2 * idxSum],
                            gens[idxSum * (2 ^ idxRound) + 2 ^ (idxRound - 1) - 1]
                        );
                }
            }
        }
        controlled (controls, ...){
            //The full adder must uncompute these carries at the end, 
            //so we save controls by not controlling this operation.
            //However : When uncomputing, the adder only calls
            //this operation with nQubits-1. Thus, we must
            //control the individual operations that use
            //qubits in the n-1 position.
            //Hence, each of the "rounds" must check whether the
            //indices are high enough to need the controls.
            let log2nover3 = Floor(Lg(2.0 * IntAsDouble(nQubits) / 3.0));	
            for idxRound in log2nover3..( - 1)..1 {
                let log2nmin1over3 = Floor(Lg(2.0 * IntAsDouble(nQubits - 1) / 3.0));
                for idc in 1.. (nQubits - 2 ^ (idxRound - 1)) / 2 ^ idxRound {
                    if (idxRound > log2nmin1over3 or idc > (nQubits - 1 - 2 ^ (idxRound - 1)) / 2 ^ idxRound){
                        (Controlled X_Gate_Error)(controls + 
                            [convertQubitErrorToQubit(gens[idc * 2 ^ idxRound - 1]), convertQubitErrorToQubit(propArrays[idxRound - 1][2 * idc])],
                            (gens[idc * 2 ^ idxRound + 2 ^ (idxRound - 1) - 1])
                        );
                    } else {
                        CCNOTWrapper_Error(gens[idc * 2 ^ idxRound - 1], 
                            propArrays[idxRound - 1][2 * idc], 
                            gens[idc * 2 ^ idxRound + 2 ^ (idxRound - 1) - 1]
                        );
                    }
                }
            }
        }
        controlled adjoint auto;
    }

    
}