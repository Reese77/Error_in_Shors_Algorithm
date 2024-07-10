namespace Microsoft.Quantum.Crypto.Error.ModularArithmetic {
    open Tools;
    open Microsoft.Quantum.Convert;
    open Microsoft.Quantum.Math;
    open Microsoft.Quantum.Diagnostics;
    open Microsoft.Quantum.Canon;
    //open Microsoft.Quantum.Crypto.Basics;
    open Microsoft.Quantum.Crypto.Error.Arithmetic;
    open Microsoft.Quantum.Crypto.Error.Basics;


    //ModularMul not copied over

    //ModularSqu not copied over

    //ModularAddConstantConstantModulus not copied over

    //ModularMulConstantModulus not copied over

    //ModularAddConstantConstantModulusSimple not copied over

    //ModularAdd not copied over

    //ModularNeg not copied over

    //ModularDbl not copied over

    //ModularMulDblAdd not copied over

    //ModularSquDblAdd not copied over


    /// # Summary
    /// Reversible, in-place modular addition of two integers modulo a constant 
    /// integer modulus. Given two $n$-bit integers x and y encoded in LittleEndian  
    /// registers `xs` and `ys`, and a constant integer `modulus`, the operation computes 
    /// the sum x + y \mod modulus. The result is held in the register `ys`. 
    ///
    /// # Input
    /// ## modulus
    /// Constant integer modulus.
    /// ## xs
    /// Qubit register encoding the first integer x.
    /// ## ys
    /// Qubit register encoding the second integer y.
    ///
    /// # References
    /// - Yasuhiro Takahashi and Noboru Kunihiro : "A quantum circuit for Shor's factoring
    ///     algorithm using 2n + 2 qubits", Quantum Information & Computation 6 (2006)
    /// - Thomas Haener, Martin Roetteler, Krysta M. Svore : "Factoring using 2n+2 qubits
    ///     with Toffoli based modular multiplication", 2016
    ///     https : //arxiv.org/abs/1611.07995
    ///
    /// # Remarks
    /// This uses `AddInteger` and `GreaterThanWrapper` and will thus make the same trade-offs
    /// (i.e., low-depth or low-T).
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

            use carry = Qubit() {
                mutable ancilla = wrapAncillaError(carry, get_Ancilla_Prob());
                (Controlled AddInteger_Error) (controls, (xs, ys, ancilla)); 
                (Adjoint AddConstant_Error)(modulus, LittleEndian_Error(ys! + [ancilla]));
                (Controlled AddConstant_Error) ([carry], (modulus, ys));
                (Controlled GreaterThanWrapper_Error) (controls, (xs, ys, ancilla));
                X_Gate_Error(ancilla);
            }
            
        }
        controlled adjoint auto;
    }


    /// # Summary
    /// # Input
    /// Reversible, in-place modular doubling of an integer modulo a constant 
    /// integer modulus. Given the n-bit integer x encoded in the LittleEndian  
    /// register `xs` and a constant integer `modulus`, the operation computes 
    /// the double 2x = x + x mod modulus. The result is held in the register `xs`. 
    ///
    /// # Input
    /// ## modulus
    /// Constant integer modulus.
    /// ## xs
    /// Qubit register encoding the first integer x.
    ///
    /// # References
    /// The algorithm for doubling modulo an odd number is sketched in Section 4.3.2 of
    /// - John Proos, Christof Zalka : "Shor's discrete logarithm quantum algorithm 
    ///   for elliptic curves", 2003.
    ///   https : //arxiv.org/abs/quant-ph/0301141/
    ///
    /// # Remarks
    /// Like ModularDbl, this operation only works correctly for odd moduli. For even
    /// modulus, the ancilla qubits will not necessarily be returned in the zero state.
    /// The specified control operation makes use of symmetry and mutual cancellation of operations 
    /// to improve on the default implementation that adds a control to every operation.
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

            //TODO last bit causes adjoint error everywhere
            use  carry = Qubit()  {
                mutable ancilla = wrapAncillaError(carry, get_Ancilla_Prob());

                let xxs = LittleEndian_Error( xs! + [ancilla] );

                (Controlled CyclicRotateRegister_Error) (controls, xxs);
                ApplyToEachWrapperCA(X_Gate_Error, xxs!);
                AddConstant_Error(modulus, xxs);
                ApplyToEachWrapperCA(X_Gate_Error, xxs!);
                (Controlled AddConstant_Error) ([carry], (modulus, xs));
                (Controlled CNOT_Gate_Error) (controls, (xs![0], ancilla));
                X_Gate_Error(ancilla);
            }
            
        }
        controlled adjoint auto;
    }

    //ModularAddConstantConstantModulusLowT not copied over

    //ModularMulDblAddConstantModulus not copied over

    //ModularSquDblAddConstantModulus not copied over

    //ModularNegConstantModulus not copied over


    /// # Summary
    /// Reversible multiplication of an integer x in a quantum register by a classical
    /// integer c, modulo a classical integer m :  y = x*c mod m.
    /// Requires a register of 0 qubits to store the result.
    ///
    /// # Input
    /// ## modulus
    /// Classical modulus m
    /// ## constant
    /// Classical constant c to be multiplied
    /// ## xs
    /// Qubit register encoding the input integer x
    /// ## ys
    /// Qubit register for the output integer y
    ///
    /// # References
    /// - The circuit is Fig. 5 of 
    ///   Martin Roetteler, Michael Naehrig, Krysta M. Svore, Kristin Lauter : 
    ///   Quantum Resource Estimates for Computing Elliptic Curve Discrete Logarithms
    ///   https : //eprint.iacr.org/2017/598
    ///   except "classically curried" over "x"
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

    /// # Summary
    /// Multiplies in-place a quantum integer x by a classical constant
    /// c, modulo a classical constant m.
    /// It borrows Length(x) qubits for the computation.
    ///
    /// # Input
    /// ## modulus
    /// Classical modulus m.
    /// ## constant
    /// Classical constant c to be multiplied. 
    /// Must be coprime to the modulus.
    /// ## xs
    /// Qubit register encoding the input integer x.
    ///
    /// # Remarks
    /// The function calls MultiplyByConstantWithConstantModulus
    /// twice, once in Adjoint, using c and c^-1.
    operation ModularMulByConstantConstantModulusInPlace_Error(modulus : BigInt, constant : BigInt, xs : LittleEndian_Error) : Unit {
        body (...) {
            (Controlled ModularMulByConstantConstantModulusInPlace_Error)([], (modulus, constant, xs));
        }
        controlled (controls, ...) {
            Fact(GreatestCommonDivisorL(constant, modulus)==1L, 
                $"Cannot multiply by {constant} in-place modulo {modulus} because they are not co-prime"
            );
            let constantinv = InverseModL(constant, modulus);
            use temp = Qubit[Length(xs!)] {
                mutable ys = wrapAncillaErrorArray(temp, get_Ancilla_Prob());
                let ysLE = LittleEndian_Error(ys);
                (Controlled SwapLE_Error)(controls, (xs, ysLE));
                (Controlled ModularMulByConstantConstantModulus_Error)(controls, (modulus, constant, ysLE, xs));
                (Adjoint Controlled ModularMulByConstantConstantModulus_Error)(controls, (modulus, constantinv, xs, ysLE));
            }
        }
        controlled adjoint auto;
    }



    //MONTGONMERY ARITHMETIC

    //Nothing has been copied over after this point
}