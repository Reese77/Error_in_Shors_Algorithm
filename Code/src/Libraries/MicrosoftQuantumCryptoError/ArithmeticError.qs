
namespace Microsoft.Quantum.Crypto.Error.Arithmetic {
    open Tools;
    open Microsoft.Quantum.Convert;
    open Microsoft.Quantum.Math;
    open Microsoft.Quantum.Diagnostics;
    open Microsoft.Quantum.Crypto.Basics;
    open Microsoft.Quantum.Crypto.Arithmetic;
    open Microsoft.Quantum.Crypto.Error.Basics;


    operation SwapLE_Error(xs : LittleEndian_Error, ys : LittleEndian_Error) : Unit {
        body (...){
            Fact(Length(xs!) == Length(ys!), $"Registers must have equal lengths to swap (current lengths : {Length(xs!)} and {Length(ys!)})");
            for idx in 0..Length(xs!) - 1 {
                SWAP_Error(xs![idx], ys![idx]);
            }
        }
        controlled(controls, ...){
            Fact(Length(xs!) == Length(ys!), $"Registers must have equal lengths to swap (current lengths : {Length(xs!)} and {Length(ys!)})");
            if (IsMinimizeWidthCostMetric()) {
                for idx in 0 .. Length(xs!) - 1 {
                    (Controlled SWAP_Error)(controls, (xs![idx], ys![idx]));
                }
            } else {
                use singleControls = Qubit[Length(xs!)] {
                    (Controlled FanoutControls)(controls, (singleControls));
                    for idx in 0..Length(xs!) - 1 {
                        (Controlled SWAP_Error)([singleControls[idx]], (xs![idx], ys![idx]));
                    }
                    (Controlled Adjoint FanoutControls)(controls, (singleControls));
                }
            }
        }
        controlled adjoint auto;
    }
    operation AddInteger_Error(xs : LittleEndian_Error, ys : LittleEndian_Error, carry : Qubit) : Unit {
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

    operation GreaterThanWrapper_Error(xs : LittleEndian_Error, ys : LittleEndian_Error, result : Qubit) : Unit {
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

    operation GreaterThanLookAhead_Error(xs : LittleEndian_Error, ys : LittleEndian_Error, carry : Qubit) : Unit {
        body (...){
            (Controlled GreaterThanLookAhead_Error)([], (xs, ys, carry));
        }
        controlled (controls, ...){
            if (Length(xs!) % 2 == 0){
                use bonusQubits = Qubit[2] {		
                    (Controlled GreaterThanLookAhead_Error)(controls, (
                        LittleEndian_Error(xs! + [bonusQubits[0]]),
                        LittleEndian_Error(ys! + [bonusQubits[1]]),
                        carry)
                    );
                }
            } else {
                ApplyToEachWrapperCA(X, ys!);
                (Controlled _CompareLookAheadImpl)(controls,  (
                    CNOT,
                    CCNOTWrapper,
                    AndWrapper,
                    xs!, 
                    ys!, 
                    carry
                ));
                ApplyToEachWrapperCA(X, ys!);
            }
        }
        controlled adjoint auto;
    }

    operation GreaterThanTTK_Error(xs: LittleEndian_Error, ys: LittleEndian_Error, result: Qubit) : Unit {
        body (...){
            CKDMGGreaterThan_Error(xs, ys, result);
        }
        controlled adjoint auto;
    }

    operation CKDMGGreaterThan_Error (xs : LittleEndian_Error, ys : LittleEndian_Error, carry : Qubit) : Unit {
        body (...){
            _CDKMGCompareInner_Error(xs, ys, carry);
        }
        controlled adjoint auto;
    }

    operation CarryLookAheadAdder_Error(xs : LittleEndian_Error, ys : LittleEndian_Error, carry : Qubit) : Unit {
        body (...){
            //Odd bit-lengths are much less expensive so we add an extra qubit
            // and do everything as an even bit-length addition
            if (Length(xs!) % 2 == 0){
                use bonusQubits = Qubit[1] {
                    _CLAAdderImpl(CNOT, CCNOTWrapper, AndWrapper, false, xs! + [bonusQubits[0]], ys! + [carry], []);
                }
            } else {
                _CLAAdderImpl(CNOT, CCNOTWrapper, AndWrapper, true, xs!, ys!,  [carry]);
            }
        }
        controlled adjoint auto;
    }

    operation CDKMGAdder_Error (xs : LittleEndian_Error, ys : LittleEndian_Error, carry : Qubit) : Unit {
        body (...){
            _CDKMGAdderInner_Error(true, xs, ys, [carry]);
        }
        controlled adjoint auto;
    }

    operation RippleCarryAdderTTK_Error(xs: LittleEndian_Error, ys: LittleEndian_Error, carry: Qubit) : Unit{
        body (...){
            CDKMGAdder_Error(xs, ys, carry);
        }
        controlled adjoint auto;
    }

    operation _CDKMGAdderInner_Error(useCarry : Bool, xs : LittleEndian_Error, ys : LittleEndian_Error, carry : Qubit[]) : Unit {
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
                use carries = Qubit[nQubits] {
                    AndWrapper_Error(xs![0], ys![0], carries[0]);
                    for idx in 1..nQubits - 1 {
                        (Controlled _CDKMGBlockForward_Error)(controls, (carries[idx - 1], xs![idx], ys![idx], carries[idx]));
                    }
                    if (useCarry){
                        (Controlled CNOT)(controls, (carries[nQubits - 1], carry[0]));
                    }
                    for idx in (nQubits - 1)..(-1)..1 {
                        (Controlled _CDKMGBlockBackward_Error)(controls, (carries[idx - 1], xs![idx], ys![idx], carries[idx]));
                    }
                    (Adjoint AndWrapper)(xs![0], ys![0], carries[0]);
                    (Controlled CNOT)(controls, (xs![0], ys![0]));
                }
            }
        }
        controlled adjoint auto;
    }

    operation CarryLookAheadAddConstant_Error(constant : BigInt, xs : LittleEndian_Error) : Unit {
        body(...){
            let nQubits = Length(xs!);
            Fact(nQubits>=BitSizeL(constant), $"{constant} is too big to add to a {nQubits} - qubit register");
            let constantArray = BigIntAsBoolArray(constant, BitSizeL(constant)) + [false, size = nQubits - BitSizeL(constant)];
            _CLAAdderImpl(
                ClassicalCNOT, 
                ClassicalCCNOT, 
                ClassicalAND, 
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
            use constantQubits = Qubit[nQubits] {
                let constants = LittleEndian_Error(constantQubits);
                (Controlled ApplyXorInPlaceL_Error)(controls, (constant, constants!));
                _CDKMGAdderInner_Error(false, constants, xs, []);
                (Controlled Adjoint ApplyXorInPlaceL_Error)(controls, (constant, constants!));
            }
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

                borrow gs = Qubit[1] {
                    Increment_Error(LittleEndian_Error([gs[0]] + xsHigher!));
                    X(gs[0]);

                    ApplyToEachWrapperCA(CNOT(gs[0], _), xsHigher!);

                    (Controlled ComputeCarry_Error)(controls, (constantLower, xsLower, gs[0]));

                    Increment_Error(LittleEndian_Error([gs[0]] + xsHigher!));
                    X(gs[0]);

                    (Controlled ComputeCarry_Error)(controls, (constantLower, xsLower, gs[0]));

                    ApplyToEachWrapperCA(CNOT(gs[0], _), xsHigher!);
                }
                (Controlled _CarryAndDivide_Error)(controls, (constantLower, xsLower));
                (Controlled _CarryAndDivide_Error)(controls, (constantHigher, xsHigher));
            }
        }
        controlled adjoint auto;
    }

    operation ComputeCarry_Error (constant : BigInt, xs : LittleEndian_Error, carry : Qubit) : Unit
    {
        body (...) {
            (Controlled ComputeCarry_Error) ([], (constant, xs, carry));
        }
        adjoint auto;
        controlled (controls, ...) {
            let nQubits = Length(xs!);
    
            if (nQubits == 1) {
                if ((constant % 2L) == 1L) {
                    (Controlled CNOT) (controls, (xs![0], carry));
                }
            } else {
                borrow gs = Qubit[nQubits-1] {
                    (Controlled CNOT) (controls, (gs[nQubits - 2], carry));
                    _ComputeCarryCascade_Error(constant, xs, LittleEndian_Error(gs));
                    (Controlled CNOT) (controls, (gs[nQubits - 2], carry));
                    (Adjoint _ComputeCarryCascade_Error) (constant, xs, 
                                                    LittleEndian_Error(gs));
                }
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
                    (Controlled CNOT) (controls, (xs![idx], gs![idx-1]));
                    (Controlled X) (controls, (xs![idx]));
                }
                CCNOTWrapper (gs![idx-2], xs![idx], gs![idx-1]);
            }
            if (constantbits[1]) {
                (Controlled CNOT) (controls, (xs![1], gs![0]));
            }
            if (constantbits[0]) {
                if (constantbits[1]) {
                    (Controlled X) (controls, (xs![1]));
                }
                (Controlled CCNOTWrapper) (controls, (xs![0], xs![1], gs![0]));
            }

            for idx in 1..(nQubits-2) {
                CCNOTWrapper (gs![idx-1], xs![idx + 1], gs![idx]);
            }
        }
        controlled adjoint auto;
    }

    operation _CDKMGCompareInner_Error (xs : LittleEndian_Error, ys : LittleEndian_Error, carry : Qubit) : Unit {
    body (...) {
            (Controlled _CDKMGCompareInner_Error)([], (xs, ys, carry));
        }
        controlled (controls, ...) {
            let nQubits = Length(xs!);
            if (nQubits == 1){
                X(ys![0]);
                (Controlled AndWrapper)(controls, (xs![0], ys![0], carry));
                X(ys![0]);
            } else {
                ApplyToEachCA(X, ys!);
                use carries = Qubit[nQubits] {
                    AndWrapper(xs![0], ys![0], carries[0]);
                    for idx in 1..nQubits - 1 {
                        _CDKMGBlockForward_Error (carries[idx - 1], xs![idx], ys![idx], carries[idx]);
                    }
                    (Controlled CNOT)(controls, (carries[nQubits - 1], carry));
                    for idx in (nQubits - 1)..(-1)..1 {
                        (Adjoint _CDKMGBlockForward_Error)(carries[idx - 1], xs![idx], ys![idx], carries[idx]);
                    }
                    (Adjoint AndWrapper)(xs![0], ys![0], carries[0]);
                }
                ApplyToEachCA(Adjoint X, ys!);
            }
        }
        controlled adjoint auto;
    }

    operation _CDKMGBlockForward_Error (previousCarry : Qubit, xQubit : Qubit, yQubit : Qubit, nextCarry : Qubit) : Unit {
        body (...){
            (Controlled _CDKMGBlockForward_Error)([], (previousCarry, xQubit, yQubit, nextCarry));
        }
        controlled (controls, ...){
            CNOT(previousCarry, xQubit);
            (Controlled CNOT)(controls, (previousCarry, yQubit));
            AndWrapper(xQubit, yQubit, nextCarry);
            CNOT(previousCarry, nextCarry);
        }
        controlled adjoint auto;

    }

    operation _CDKMGBlockBackward_Error (previousCarry : Qubit, xQubit : Qubit, yQubit : Qubit, nextCarry : Qubit) : Unit {
        body (...){
            (Controlled _CDKMGBlockBackward_Error)([], (previousCarry, xQubit, yQubit, nextCarry));
        }
        controlled (controls, ...){
            CNOT(previousCarry, nextCarry);
            (Adjoint AndWrapper)(xQubit, yQubit, nextCarry);
            CNOT(previousCarry, xQubit);
            (Controlled CNOT)(controls, (xQubit, yQubit));
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

            borrow g = Qubit[nQubits] {
                let gs = LittleEndian_Error(g);

                if ( nQubits > 3) {
                    (Adjoint AddIntegerNoCarry_Error) (gs, xs);
                    ApplyToEachWrapperCA(X, gs!);
                    (Adjoint AddIntegerNoCarry_Error) (gs, xs);
                    ApplyToEachWrapperCA(X, gs!);
                } elif (nQubits == 3) {
                    CCNOTWrapper (xs![0], xs![1], xs![2]);
                    CNOT (xs![0], xs![1]);
                    X (xs![0]);
                } elif (nQubits == 2) {
                    CNOT (xs![0], xs![1]);
                    X (xs![0]);
                } elif (nQubits == 1) {
                    X (xs![0]);
                }
            }
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
            _CLAAdderImpl(CNOT, CCNOTWrapper, AndWrapper, false, xs!, ys!, []);
        }
        controlled adjoint auto;
    }




    /////
    //operations copied over exactly
    
}