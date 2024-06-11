// Copyright (c) Microsoft Corporation.
// Licensed under the MIT license.

namespace Microsoft.Quantum.Crypto.NC.SpecialCounters {
    open Microsoft.Quantum.Intrinsic;
    open Microsoft.Quantum.Canon;
    open Microsoft.Quantum.Diagnostics;
    open Microsoft.Quantum.Crypto.Basics;
    open Microsoft.Quantum.Crypto.Arithmetic;


    ////////////////////////////////////////////////////////////////////////////////////////////
    ///////                                                                             ////////
    ///////                          SPECIAL COUNTERS                                   ////////
    ///////                                                                             ////////
    ////////////////////////////////////////////////////////////////////////////////////////////

    /// # Summary
    /// Represents a qubit register that functions as a counter.
    ///
    /// # Contents
    /// ## register
    /// Points to the qubits used for the counter
    /// ## period
    /// The highest integer it can count to. Assumed
    /// to return to its zero state if it is incremented
    /// `period` times.
    /// ## Prepare
    /// Operation which initializes the qubit registers
    /// to the zero state of the counter.
    /// ## Increment
    /// Operation which increments the counter by one
    /// ## Test
    /// Operation which flips the target qubit if the
    /// counter is in any non-zero state.
    newtype Counter = (register : Qubit[], 
        period : Int, 
        Prepare : (Unit => Unit is Ctl + Adj), 
        Increment : (Unit => Unit is Ctl + Adj), 
        Test : ((Qubit) => Unit is Ctl + Adj)
    );

    /// # Summary
    /// Returns a qubit array as a Counter type.
    ///
    /// # Inputs
    /// ## register
    /// The qubits that wil form the counter.
    function QubitsAsCounter(register : Qubit[]) : Counter {
        return QubitsAsBasicCounter(register);
    }

    /// # Summary
    /// Formats a qubit array into a Counter type,
    /// including all necessary functions to act as a counter.
    ///
    /// # Inputs
    /// ## register
    /// The qubits that will act as the counter.
    ///
    /// # Output
    /// ## Counter
    /// A Counter that points to the qubits.
    function QubitsAsBasicCounter (register: Qubit[]) : Counter {
        let nQubits = Length(register);
        let noOp = () => ();
        let incrementInternal = ConcatenateOperations(Increment, noOp, LittleEndian(register), _); // from arithmetic, will fix itself
        let test = OppositeCheck(CheckIfAllZero(register, _), _);
        return Counter(register, 2^nQubits, noOp, incrementInternal, test);
    }

    /// # Summary
    /// Returns a Counter type that references an input
    /// array of qubits, and includes operations
    /// that use shift registers for incrementing
    ///
    /// # Inputs
    /// ## counter
    /// Qubit register that will contain the counter.
    ///
    /// Output
    /// ## Counter
    /// Tuple referencing the qubits in `counter`, 
    /// as well as operations for counting based on 
    /// shift-registers
    function QubitsAsSpecialCounter (register : Qubit[]) : Counter {
        let nQubits = Length(register);
        let noOp = () => ();
        let prepare = ConcatenateOperations(PrepareSpecialCounter, noOp, register, _);
        let incrementInternal = ConcatenateOperations(IncrementSpecialCounter, noOp, register, _);
        let test = TestSpecialCounter(register, _);
        let primitivepoly=_PrimitiveGF2Polynomial(nQubits);
        return Counter(register, 2^nQubits, prepare, incrementInternal, test);
    }


    /// # Summary
    /// Sets a SpecialCounter to its "zero" state.
    ///
    /// # Inputs
    /// ## counter
    /// A qubit register assumed to be in an all-zero state,
    /// assumed to be referenced by a Counter type.
    operation PrepareSpecialCounter(counter : Qubit[]) : Unit {
        body(...){
            ApplyToEachWrapperCA(X, counter);
        }
        controlled adjoint auto;
    }



    

    /// # Summary
    /// Runs a "quantum while loop". This runs a series of 
    /// unitaries U_1, ..., U_n. Before each unitary, a quantum Test operation
    /// is run. If Test comes out true (i.e., it flips a control), then the 
    /// loop will stop running any more U_k and will instead increment a special counter.
    /// Since the classical control does not know many iterations it will take, it runs up
    /// to some predetermined bound.
    ///
    /// # Inputs
    /// ## Body
    /// This specifies the unitary U_k, where k is the integer input. 
    /// ## Test
    /// This runs some test, and flips the qubit given as input if the test passes. 
    /// ## counter
    /// A SpecialCounter type that must be passed initially in the all-ones state. 
    /// ## bound
    /// The maximum number of iterations that the while loop could possible take.
    ///
    /// # Reference
    /// A generalization of the circuit for modular inversion from : 
    ///   Martin Roetteler, Michael Naehrig, Krysta M. Svore, Kristin Lauter : 
    ///   Quantum Resource Estimates for Computing Elliptic Curve Discrete Logarithms
    ///   https : //eprint.iacr.org/2017/598
    ///
    /// # Remark
    /// This operation is well-defined for cases where the test never passes. 
    /// It assumes that calling Test will not change the result of calling
    /// Test again. 
    operation QuantumWhile(lowerBound : Int, upperBound : Int, Body : ((Int)=>Unit is Ctl + Adj), test : ((Qubit)=>Unit is Ctl + Adj), Alternate : ((Int)=>Unit is Ctl + Adj), counter : Counter) : Unit{
        body (...){
            (Controlled QuantumWhile)([], (lowerBound, upperBound, Body, test, Alternate, counter));
        }	
        controlled (controls, ...){
            Fact(upperBound>lowerBound, $"Upper bound ({upperBound}) must be higher than lower bound ({lowerBound})");
            Fact(upperBound-lowerBound<counter::period, $"Counter's period is {counter::period} but may need to count {upperBound-lowerBound} iterations");
            use mainControl = Qubit() {
	    	    // Use the main control if there are too many controls
	    	    if (Length(controls) > 1){
		    	    CheckIfAllOnes(controls, mainControl);
			        for roundNum in 0..lowerBound - 1 {
			            (Controlled Body)([mainControl], (roundNum));
			        }
			        (Adjoint CheckIfAllOnes)(controls, mainControl);
		        } else {
	    	        for roundNum in 0..lowerBound - 1 {
			   	        (Controlled Body)(controls, (roundNum));
			        }
	           }
	  	    for roundNum in lowerBound..upperBound-1 {
                    //Logic here : maincontrol is initially 0
                    //When the test does nothing and the counter is all 1s : 
                    //		It runs Body[idxRound], does not increment
                    //When the test is true but the counter is all 1s : 
                    //		It flips maincontrol from 0 to 1
                    //		The body is not run, the counter increments
                    //When the test is true and the counter is not all 1s : 
                    //		It flips maincontrol twice, keeping it at 1
                    //		The body is not run, the counter increments

                    //Runs the test
                    (Controlled test)(controls, (mainControl));
                    //Checks if the counter is non-start
                    counter::Test(mainControl);
                    //Fanout the main control to save depth
                    use extraControls = Qubit[2] {
                        CNOT(mainControl,extraControls[0]);
                        CNOT(extraControls[0],extraControls[1]);
                        //Runs the body if maincontrol is 0
                        (Controlled X)(controls, (mainControl));
                        (Controlled Body)([mainControl], (roundNum));
                        (Controlled X)(controls, (mainControl));
                        //Increments the counter if need be
                        (Controlled counter::Increment)([extraControls[0]], ());
                        //Otherwise, runs the alternate
                        (Controlled Alternate)([extraControls[1]], (roundNum));
                        CNOT(extraControls[0],extraControls[1]);
                        CNOT(mainControl,extraControls[0]);
                    }
                }
                //Clears the control
                //If the test was positive at any point, maincontrol
                //should be 1.
                //Otherwise, it will be 0. 
                //To test whether the test was ever positive, we check the
                // counter
                (Controlled counter::Test)(controls, (mainControl));
            }
        }
        controlled adjoint auto;
    }


    /// # Summary
    /// Tests if a special counter is in its non-zero state; if it is, 
    /// it flips the target qubit
    ///
    /// # Inputs
    /// ## counter
    /// Qubit register  to test
    /// ## target
    /// A qubit whose state will be flipped (an X gate) if
    /// `counter` is not in its zero state.
    operation TestSpecialCounter(counter : Qubit[], target : Qubit) : Unit {
        body (...) {
            (Controlled TestSpecialCounter)([], (counter, target));
        }
        controlled(controls, ...){
            (Controlled CheckIfAllOnes)(controls, (counter, target));
            (Controlled X)(controls, (target));
        }
        controlled adjoint auto;
    }


    /// # Summary
    /// Returns an irreducible polynomial over GF2 of the specified degree.
    /// Used for special counters.
    /// 
    /// # Inputs
    /// ## degree
    /// The degree of the polynomial to be returned
    ///
    /// # Outputs
    /// ## Int[]
    /// An array of coefficients in the polynomial which are non-zero, 
    /// where 0 is the constant term, 1 is x, 2 is x^2, etc.
    /// The constant term and largest term are assumed to be 1
    /// and thus omitted
    function _PrimitiveGF2Polynomial(degree : Int) : Int[]{
        let PRIMITIVE_TABLE_GF2 = [
              [ 1 ], [ 1 ], [ 1 ], [ 2 ], [ 1 ], [ 1 ], [ 2, 3, 4 ], [ 4 ], [ 3 ], [ 2 ], [ 1, 3, 5, 6, 7 ], [ 1, 3, 4 ], [ 3, 5, 7 ], [ 1 ], [ 2, 3, 5 ], [ 3 ], [ 1, 10, 12 ], 
              [ 1, 2, 5 ], [ 3 ], [ 2 ], [ 1 ], [ 5 ], [ 1, 3, 4 ], [ 3 ], [ 1, 4, 6, 7, 8, 10, 14 ], [ 1, 2, 5 ], [ 2, 5, 6, 7, 13 ], [ 2 ], [ 1, 2, 3, 5, 7, 11, 13, 16, 17 ], 
              [ 3 ], [ 3, 4, 7, 9, 15 ], [ 3, 6, 8, 10, 11, 12, 13 ], [ 1, 2, 4, 5, 6, 7, 8, 11, 12, 15, 16 ], [ 2 ], [ 1, 5, 6, 8, 13, 14, 17, 19, 20, 22, 23 ], [ 1, 4, 6 ], 
              [ 1, 5, 6 ], [ 4 ], [ 3, 4, 5 ], [ 3 ], [ 1, 2, 5, 6, 9, 11, 12, 18, 20, 24, 25, 26, 30 ], [ 3, 4, 6 ], [ 1, 3, 4, 16, 17, 19, 24 ], [ 1, 3, 4 ], [ 14, 17, 20, 21, 23 ], 
              [ 5 ], [ 3, 7, 8, 10, 11, 12, 17, 23, 25 ], [ 9 ], [ 2, 3, 4 ], [ 1, 3, 6 ], [ 3 ], [ 1, 2, 6 ], [ 1, 2, 4, 7, 13, 15, 16, 17, 18, 21, 25, 27, 29, 30, 31, 32, 34 ], 
              [ 4, 7, 9, 10, 11 ], [ 2, 4, 7 ], [ 1, 2, 3, 4, 5, 6, 8, 10, 11, 13, 16, 19, 21 ], [ 19 ], [ 2, 4, 7 ], [ 1 ], [ 1, 2, 5 ], 
              [ 1, 6, 12, 13, 14, 16, 17, 18, 19, 20, 21, 24, 25, 26, 27, 28, 29, 30, 32  ], [ 1 ], [ 1, 3, 4 ], [ 18 ], [ 2, 4, 5, 6, 7, 11, 13, 16, 19, 21, 22, 23, 24, 27, 29, 30, 31, 32, 33, 34, 38, 40, 42, 45, 46 ], 
              [ 1, 2, 5 ], [ 9 ], [ 2, 5, 6 ], [ 1, 3, 5 ], [ 6 ], [ 3, 9, 10 ], [ 25 ], [ 3, 8, 11, 12, 13, 16, 17, 21, 24, 26, 27, 28, 29, 30, 31, 32, 33, 34, 35,  36, 37 ], [ 1, 3, 6 ], 
              [ 1, 2, 5, 14, 15, 19, 20, 23, 24, 25, 27, 29, 31, 33, 34, 35, 36, 37, 38 ], [ 2, 5, 6 ], [ 1, 4, 6, 7, 8, 9, 11, 13, 14, 15, 17, 18, 19, 21, 22, 24, 25, 27, 28, 32,  33, 34, 35, 37, 39, 42, 43, 44, 46 ], 
              [ 9 ], [ 2, 4, 9 ], [ 4 ], [ 1, 2, 3, 4, 6, 7, 9, 11, 12, 13, 15, 16, 17, 21, 22, 24, 28, 32, 33, 34,  35, 36, 37 ], [ 2, 4, 7 ], [ 2, 4, 5, 7, 8, 9, 11, 12, 13, 16, 17, 20, 21, 24, 25, 26, 28, 31, 32, 37,  39, 41, 46, 47, 48, 52, 57 ], 
              [ 1, 2, 8 ], [ 1, 2, 5, 6, 7, 8, 9, 10, 12, 14, 16, 21, 22, 25, 27, 31, 38, 40, 43 ], [ 13 ], [ 1, 3, 4, 5, 7, 8, 9, 11, 12, 13, 14, 15, 18, 19, 21, 24, 27, 28, 30, 31,  33, 36, 38, 41, 44, 45, 47 ], [ 38 ], [ 2, 4, 7, 10, 11, 12, 14, 16, 18, 24, 25, 26, 28, 30, 32, 34, 36, 37, 38,  39, 40, 42, 44, 45, 46, 47, 48, 50, 51, 53, 55, 56, 57, 58, 60, 61, 62, 63,  64 ], [ 1, 5, 8 ], [ 2, 4, 5, 9, 12, 14, 15, 16, 17, 18, 21, 22, 23, 24, 30, 32, 33, 37, 38,  40, 41, 42, 43, 44, 48 ], [ 2 ], [ 21 ], [ 11 ], [ 6, 9, 10 ], [ 6 ], [ 11 ], [ 1, 2, 4, 6, 32, 33, 34, 35, 64, 65, 66, 67, 96, 97, 98 ], 
              [ 3, 5, 6, 8, 9, 11, 15, 16, 19, 20, 22, 24, 25, 27, 30, 31, 34, 35, 36, 37, 41, 43, 44, 45, 46, 47, 48, 52, 55, 56, 57 ]
        ];
        Fact(degree < Length(PRIMITIVE_TABLE_GF2) + 2, $"Degree {degree} is too large for table (max degree {Length(PRIMITIVE_TABLE_GF2) + 1}");
        return PRIMITIVE_TABLE_GF2[degree - 2];
    }

    /// # Summary
    /// Increments a special counter by 1.
    ///
    /// # Inputs
    /// ## counter
    /// Qubit register of the counter to increment.
    operation IncrementSpecialCounter(counter : Qubit[]) : Unit {
        body (...) {
            (Controlled IncrementSpecialCounter)([], (counter));
        }
        controlled (controls, ...){
            let nQubits=Length(counter);
            (Controlled CyclicRotateRegister)(controls, LittleEndian(counter));
            let polynomial = _PrimitiveGF2Polynomial(nQubits);
            for idp in 0..Length(polynomial) - 1 {
                (Controlled CNOT)(controls, (counter[0], counter[polynomial[idp]]));
            }
        }
        controlled adjoint auto;
    }

   


    
}