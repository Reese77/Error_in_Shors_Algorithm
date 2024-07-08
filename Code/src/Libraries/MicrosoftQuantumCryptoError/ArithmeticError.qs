
namespace Microsoft.Quantum.Crypto.Error.Arithmetic {
    open Tools;
    open Microsoft.Quantum.Convert;
    open Microsoft.Quantum.Canon;
    open Microsoft.Quantum.Math;
    open Microsoft.Quantum.Diagnostics;
    //open Microsoft.Quantum.Crypto.Basics;
    open Microsoft.Quantum.Crypto.Arithmetic;
    open Microsoft.Quantum.Crypto.Error.Basics;


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
                mutable singleControls = createAncillaErrorArray(Length(xs!), [0, 0]);
                (Controlled FanoutControls_Error)(controls, (singleControls));
                for idx in 0..Length(xs!) - 1 {
                    (Controlled SWAP_Gate_Error)([convertQubitErrorToQubit(singleControls[idx])], (xs![idx], ys![idx]));
                }
                (Controlled Adjoint FanoutControls_Error)(controls, (singleControls));

                ResetAll_Error(singleControls);
            }
        }
        controlled adjoint auto;
    }
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

    operation GreaterThanLookAhead_Error(xs : LittleEndian_Error, ys : LittleEndian_Error, carry : Qubit_Error) : Unit {
        body (...){
            (Controlled GreaterThanLookAhead_Error)([], (xs, ys, carry));
        }
        controlled (controls, ...){
            if (Length(xs!) % 2 == 0){
                mutable bonusQubits = createAncillaErrorArray(2, [0, 0]);

                (Controlled GreaterThanLookAhead_Error)(controls, (
                    LittleEndian_Error(xs! + [bonusQubits[0]]),
                    LittleEndian_Error(ys! + [bonusQubits[1]]),
                    carry)
                );
                ResetAll_Error(bonusQubits);

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

    operation GreaterThanTTK_Error(xs: LittleEndian_Error, ys: LittleEndian_Error, result: Qubit_Error) : Unit {
        body (...){
            CKDMGGreaterThan_Error(xs, ys, result);
        }
        controlled adjoint auto;
    }

    operation CKDMGGreaterThan_Error (xs : LittleEndian_Error, ys : LittleEndian_Error, carry : Qubit_Error) : Unit {
        body (...){
            _CDKMGCompareInner_Error(xs, ys, carry);
        }
        controlled adjoint auto;
    }

    operation CarryLookAheadAdder_Error(xs : LittleEndian_Error, ys : LittleEndian_Error, carry : Qubit_Error) : Unit {
        body (...){
            //Odd bit-lengths are much less expensive so we add an extra qubit
            // and do everything as an even bit-length addition
            if (Length(xs!) % 2 == 0){
                mutable bonusQubit = createAncillaError([0, 0]);
                
                _CLAAdderImpl_Error(CNOT_Gate_Error, CCNOTWrapper_Error, AndWrapper_Error, false, xs! + [bonusQubit], ys! + [carry], []);
                Reset_Error(bonusQubit);
            } else {
                _CLAAdderImpl_Error(CNOT_Gate_Error, CCNOTWrapper_Error, AndWrapper_Error, true, xs!, ys!,  [carry]);
            }
        }
        controlled adjoint auto;
    }

    operation CDKMGAdder_Error (xs : LittleEndian_Error, ys : LittleEndian_Error, carry : Qubit_Error) : Unit {
        body (...){
            _CDKMGAdderInner_Error(true, xs, ys, [carry]);
        }
        controlled adjoint auto;
    }

    operation RippleCarryAdderTTK_Error(xs: LittleEndian_Error, ys: LittleEndian_Error, carry: Qubit_Error) : Unit{
        body (...){
            CDKMGAdder_Error(xs, ys, carry);
        }
        controlled adjoint auto;
    }

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
                mutable carries = createAncillaErrorArray(nQubits, [0, 0]);

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
                
                ResetAll_Error(carries);
            }
        }
        controlled adjoint auto;
    }

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

    operation CDKMGAddConstant_Error (constant : BigInt, xs : LittleEndian_Error) : Unit {
        body (...){
            (Controlled CDKMGAddConstant_Error)([], (constant, xs));
        }
        controlled (controls, ...){
            let nQubits = Length(xs!);
            Fact(nQubits>=BitSizeL(constant), $"{constant} is too big to add to a {nQubits} - qubit register");
            
            mutable constantQubits = createAncillaErrorArray(nQubits, [0, 0]);

            let constants = LittleEndian_Error(constantQubits);
            (Controlled ApplyXorInPlaceL_Error)(controls, (constant, constants!));
            _CDKMGAdderInner_Error(false, constants, xs, []);
            (Controlled Adjoint ApplyXorInPlaceL_Error)(controls, (constant, constants!));

            ResetAll_Error(constantQubits);
        }
        controlled adjoint auto;
    }

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

                mutable gs = createAncillaError([0, 0]);

                
                Increment_Error(LittleEndian_Error([gs] + xsHigher!));
                X_Gate_Error(gs);

                ApplyToEachWrapperCA(CNOT_Gate_Error(gs, _), xsHigher!);

                (Controlled ComputeCarry_Error)(controls, (constantLower, xsLower, gs));

                Increment_Error(LittleEndian_Error([gs] + xsHigher!));
                X_Gate_Error(gs);

                (Controlled ComputeCarry_Error)(controls, (constantLower, xsLower, gs));

                ApplyToEachWrapperCA(CNOT_Gate_Error(gs, _), xsHigher!);

                Reset_Error(gs);
                
                (Controlled _CarryAndDivide_Error)(controls, (constantLower, xsLower));
                (Controlled _CarryAndDivide_Error)(controls, (constantHigher, xsHigher));
            }
        }
        controlled adjoint auto;
    }

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
                mutable gs = createAncillaErrorArray(nQubits-1, [0, 0]);
                
                (Controlled CNOT_Gate_Error) (controls, (gs[nQubits - 2], carry));
                _ComputeCarryCascade_Error(constant, xs, LittleEndian_Error(gs));
                (Controlled CNOT_Gate_Error) (controls, (gs[nQubits - 2], carry));
                (Adjoint _ComputeCarryCascade_Error) (constant, xs, 
                                                LittleEndian_Error(gs));
                
                ResetAll_Error(gs);
            }
        }
        controlled adjoint auto;
    }

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

                mutable carries = createAncillaErrorArray(nQubits, [0, 0]);

                AndWrapper_Error(xs![0], ys![0], carries[0]);
                for idx in 1..nQubits - 1 {
                    _CDKMGBlockForward_Error (carries[idx - 1], xs![idx], ys![idx], carries[idx]);
                }
                (Controlled CNOT_Gate_Error)(controls, (carries[nQubits - 1], carry));
                for idx in (nQubits - 1)..(-1)..1 {
                    (Adjoint _CDKMGBlockForward_Error)(carries[idx - 1], xs![idx], ys![idx], carries[idx]);
                }
                (Adjoint AndWrapper_Error)(xs![0], ys![0], carries[0]);

                ResetAll_Error(carries);
                
                ApplyToEachCA(Adjoint X_Gate_Error, ys!);
            }
        }
        controlled adjoint auto;
    }

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

    operation RippleCarryAdderNoCarryTTK_Error(xs: LittleEndian_Error, ys: LittleEndian_Error) : Unit{
        body (...){
            CDKMGAdderNoCarry_Error(xs, ys);
        }
        controlled adjoint auto;
    }

    operation CDKMGAdderNoCarry_Error (xs : LittleEndian_Error, ys : LittleEndian_Error) : Unit {
        body (...){
            _CDKMGAdderInner_Error(false, xs, ys, []);
        }
        controlled adjoint auto;
    }

    operation Increment_Error (xs : LittleEndian_Error) : Unit
    {
        body (...) {
            let nQubits = Length(xs!);

            mutable g = createAncillaErrorArray(nQubits, [0, 0]);

            
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

            ResetAll_Error(g);
            
        }
        adjoint auto;
        controlled auto;
        controlled adjoint auto;
    }

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

    operation CarryLookAheadAdderNoCarry_Error(xs : LittleEndian_Error, ys : LittleEndian_Error) : Unit {
        body(...){
            _CLAAdderImpl_Error(CNOT_Gate_Error, CCNOTWrapper_Error, AndWrapper_Error, false, xs!, ys!, []);
        }
        controlled adjoint auto;
    }


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

                mutable ancillaQubits = createAncillaErrorArray(ancillaSize, [0, 0]);

                
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
                
                ResetAll_Error(ancillaQubits);
            }
        }
        controlled adjoint auto;
    }

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

                mutable ancillaQubits = createAncillaErrorArray(ancillaSize, [0, 0]);
                
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

                    mutable singleControls = createAncillaErrorArray(nQubits-1, [0, 0]);
                    
                    (Controlled FanoutControls_Error)(controls, (singleControls));
                    CNOT_Gate_Error(singleControls[0], ys[0]);
                    CCNOTWrapper_Error(singleControls[0], gens[0], ys[1]);
                    for ids in 1..nQubits - 2 {
                        CCNOTWrapper_Error(singleControls[ids], gens[ids], ys[ids + 1]);
                        CNOT_Gate_Error(singleControls[ids], ys[ids]);
                        cqCCNOTWrapper(xs[ids], singleControls[ids], ys[ids]);
                    }
                    (Controlled Adjoint FanoutControls_Error)(controls, (singleControls));
                    ResetAll_Error(singleControls);
                    
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
                
                ResetAll_Error(ancillaQubits);
            }
        }
        controlled adjoint auto;
    }

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


    /////
    //operations copied over exactly
    
}