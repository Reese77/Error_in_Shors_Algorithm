namespace Microsoft.Quantum.Crypto.Error.ModularArithmetic {
    open Tools;
    open Microsoft.Quantum.Convert;
    open Microsoft.Quantum.Math;
    open Microsoft.Quantum.Diagnostics;
    open Microsoft.Quantum.Canon;
    open Microsoft.Quantum.Crypto.Basics;
    open Microsoft.Quantum.Crypto.Error.Arithmetic;
    open Microsoft.Quantum.Crypto.Error.Basics;

    operation ModularMulByConstantConstantModulusInPlace_Error(modulus : BigInt, constant : BigInt, xs : LittleEndian_Error) : Unit {
        body (...) {
            (Controlled ModularMulByConstantConstantModulusInPlace_Error)([], (modulus, constant, xs));
        }
        controlled (controls, ...) {
            Fact(GreatestCommonDivisorL(constant, modulus)==1L, 
                $"Cannot multiply by {constant} in-place modulo {modulus} because they are not co-prime"
            );
            let constantinv = InverseModL(constant, modulus);
            use ys = Qubit[Length(xs!)] {
                let ysLE = LittleEndian_Error(ys);
                (Controlled SwapLE_Error)(controls, (xs, ysLE));
                (Controlled ModularMulByConstantConstantModulus_Error)(controls, (modulus, constant, ysLE, xs));
                (Adjoint Controlled ModularMulByConstantConstantModulus_Error)(controls, (modulus, constantinv, xs, ysLE));
            }
        }
        controlled adjoint auto;
    }

    operation ModularMulByConstantConstantModulus_Error(modulus : BigInt, constant : BigInt, xs : LittleEndian_Error, ys : LittleEndian_Error) : Unit{
        body (...) { 
            (Controlled ModularMulByConstantConstantModulus_Error) ([], (modulus, constant, xs, ys));
        }
        controlled (controls, ... ){
            let constantAsArray = BigIntAsBoolArray(constant, BitSizeL(constant));
            for idx in Length(constantAsArray)-1 ..(-1)..1 {
                if (constantAsArray[idx]){
                    (Controlled ModularAddConstantModulus_Error)(controls, (modulus, xs, ys));
                }
                (Controlled ModularDblConstantModulus_Error)(controls, (modulus, ys));
            }
            if (constantAsArray[0]){
                (Controlled ModularAddConstantModulus_Error)(controls, (modulus, xs, ys));
            }
        }
        controlled adjoint auto;
    }

    operation ModularAddConstantModulus_Error (modulus : BigInt, xs : LittleEndian_Error, ys : LittleEndian_Error) : Unit
    {
        body (...) {
            (Controlled ModularAddConstantModulus_Error) ([], (modulus, xs, ys));
        }
        adjoint auto;
        controlled (controls, ...) {
            let nQubits = Length(xs!);

            Fact(
                nQubits == Length(ys!), 
                "Input register xs and ys must have the same number of qubits." );

            use carry = Qubit[1] {
                (Controlled AddInteger_Error) (controls, (xs, ys, carry[0])); 
                (Adjoint AddConstant_Error)(modulus, LittleEndian_Error(ys! + carry));
                (Controlled AddConstant_Error) (carry, (modulus, ys));
                (Controlled GreaterThanWrapper_Error) (controls, (xs, ys, carry[0]));
                X(carry[0]);
            }
        }
        controlled adjoint auto;
    }
    operation ModularDblConstantModulus_Error (modulus : BigInt, xs : LittleEndian_Error) : Unit
    {
        body (...) {
            (Controlled ModularDblConstantModulus_Error) ([], (modulus, xs));
        }
        adjoint auto;
        controlled (controls, ...) {
            let nQubits = Length(xs!);

            Fact(
                modulus % 2L == 1L, 
                "ModularDbl requires modulus to be odd." );

            use  ancillas = Qubit[1]  {
                let carry = ancillas[0];
                let xxs = LittleEndian_Error( xs! + [carry] );

                (Controlled CyclicRotateRegister_Error) (controls, xxs);
                ApplyToEachWrapperCA(X, xxs!);
                AddConstant_Error(modulus, xxs);
                ApplyToEachWrapperCA(X, xxs!);
                (Controlled AddConstant_Error) ([carry], (modulus, xs));
                (Controlled CNOT) (controls, (xs![0], carry));
                X(carry);
            }
        }
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

}