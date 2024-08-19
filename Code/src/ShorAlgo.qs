namespace Error_In_Shor_Algo {

    open Microsoft.Quantum.Diagnostics;
    open Microsoft.Quantum.Crypto.Basics;
    open Microsoft.Quantum.Crypto.Arithmetic;
    open Microsoft.Quantum.Crypto.ModularArithmetic;
    open Microsoft.Quantum.Math;
    open Microsoft.Quantum.Arrays;
    open Microsoft.Quantum.Convert;
    open Microsoft.Quantum.Crypto.Error.Basics;
    open Microsoft.Quantum.Crypto.Error.ModularArithmetic;
    open Tools;


    //// BEGINNING OF INT VERSIONS
    // There are no comments for the int versions since they just convert everything to BigInt, 
    // call the BigInt version, and convert back before returning
    // If you want to read the comments, Ctrl + F for the operation/function name but replace I with L
    
    operation findDivisorI(n : Int) : Int {

        let retval = findDivisorL(IntAsBigInt(n));

        return BoolArrayAsInt(BigIntAsBoolArray(retval, BitSizeL(retval)));

    }

    function findOrderofAModNaiveI(a : Int, mod : Int) : Int {
        let retval = findOrderofAModNaiveL(IntAsBigInt(a), IntAsBigInt(mod));

        return BoolArrayAsInt(BigIntAsBoolArray(retval, BitSizeL(retval)));
    }

    operation findOrderOfAMod_RecycledXRegisterI_Error(a: Int, mod : Int) : Int {
        let retval = findOrderOfAMod_RecycledXRegisterL_Error(IntAsBigInt(a), IntAsBigInt(mod));

        return BoolArrayAsInt(BigIntAsBoolArray(retval, BitSizeL(retval)));
        
    }

    operation findOrderOfAMod_RecycledXRegisterI(a: Int, mod : Int) : Int {
        let retval = findOrderOfAMod_RecycledXRegisterL(IntAsBigInt(a), IntAsBigInt(mod));

        return BoolArrayAsInt(BigIntAsBoolArray(retval, BitSizeL(retval)));
    }

    operation findOrderOfAModI_Error(a : Int, mod : Int) : Int{

        let retval = findOrderOfAModL_Error(IntAsBigInt(a), IntAsBigInt(mod));

        return BoolArrayAsInt(BigIntAsBoolArray(retval, BitSizeL(retval)));
        
    }

    operation findOrderOfAModI(a : Int, mod : Int) : Int{
        let retval = findOrderOfAModL(IntAsBigInt(a), IntAsBigInt(mod));

        return BoolArrayAsInt(BigIntAsBoolArray(retval, BitSizeL(retval)));
        
    }
    
    function FindOrderFromQFTI(guess : Int, mod : Int, qftresult : Int, n1 : Int, doubles : Int, epsilon : Int) : Int {
        let retval = FindOrderFromQFTL(IntAsBigInt(guess), IntAsBigInt(mod), IntAsBigInt(qftresult)
                                        , n1, doubles, IntAsBigInt(epsilon));

        if retval == -1L {
            return -1;
        }
        return BoolArrayAsInt(BigIntAsBoolArray(retval, BitSizeL(AbsL(retval))));
    }

    function RemoveEvenMultiplesI(guess : Int, mod : Int, answer : Int) : Int {
        if answer == -1 {
            return -1;
        }
        let retval = RemoveEvenMultiplesL(IntAsBigInt(guess), IntAsBigInt(mod), IntAsBigInt(answer));

        return BoolArrayAsInt(BigIntAsBoolArray(retval, BitSizeL(retval)));
    }

    function ContinuedFractionExpansionI(numerator : Int, denominator : Int) : Int[] {
        let retval = ContinuedFractionExpansionL(IntAsBigInt(numerator), IntAsBigInt(denominator));

        mutable ret = [];
        for i in retval {
            set ret += [BoolArrayAsInt(BigIntAsBoolArray(i, BitSizeL(i)))];
        }
        return ret;
    }

    function ConvergentsI(continuedFraction : Int[]) : (Int, Int)[] {
        mutable input :BigInt[]= [];
        for i in continuedFraction {
            set input += [IntAsBigInt(i)];
        }

        let retval = ConvergentsL( input );

        mutable ret = [];
        for (num, den) in retval {
            set ret += [( BoolArrayAsInt(BigIntAsBoolArray(num, BitSizeL(num))), BoolArrayAsInt(BigIntAsBoolArray(den, BitSizeL(den))) ) ];
        }
        return ret;
    }

    //// BEGINNING OF BIGINT VERSIONS

    /// # summary
    /// attempts 25 times to find a divisor of n using Shor's Algorithm
    ///
    /// # input
    /// ## n BigInt
    /// the number we want to factor
    ///
    /// # output
    /// ## BigInt
    /// a hopefully non-trivial factor of n
    ///
    /// #remarks
    /// if it can't successfully find a non-trivial factor after 25 attempts, returns 1
    ///
    operation findDivisorL(n : BigInt) : BigInt {

        for i in 1..25 {
            
            //generate random guess
            //because n is huge, chances of picking the same guess are astronomically tiny
            let guess = GenerateRandomNumberInRangeL(n);

            //if not coprime, return gcd
            let gcd = myGCDL(guess, n);
            if gcd != 1L {
                return gcd;
            }

            //else, find order mod N
            //maybe I should do the precomputation here
            let m = findOrderOfAMod_RecycledXRegisterL(guess, n);
            let orderCandidate = FindOrderFromQFTL(guess, n, m, 2 * BitSizeL(n), 4, 0L);
            let order = RemoveEvenMultiplesL(guess, n, orderCandidate);

            //if order is odd, continue to top of loop
            if order % 2L == 0L {
                //if guess^halforder is -1 mod n, continue to top of loop
                let squareRootOf1 = modularExponentiationL(guess, order / 2L, n);
                
                if squareRootOf1 != n-1L {
                    //if gcd(guess^halforder + 1, n) != 1, return it
                    let gcd1 = myGCDL(squareRootOf1 + 1L, n);
                    
                    if gcd1 != 1L {
                        return gcd1;
                    }
                    //if gcd(guess^halforder - 1, n) != 1, return it
                    let gcd2 = myGCDL(squareRootOf1 - 1L, n);

                    if gcd2 != 1L {
                        return gcd2;
                    }
                }
            }
        }

        return 1L;
    }


    /// # Description
    /// finds the order of (a) with modulus mod by repeated multiplication (SLOW)
    ///
    /// # Inputs
    /// ## a BigInt
    /// number we want to find order of
    ///
    /// ## mod BigInt
    /// the modulus we are working with
    ///
    /// # Output
    /// ## BigInt
    ///
    function findOrderofAModNaiveL(a : BigInt, mod : BigInt) : BigInt {
        mutable cur = a;
        mutable counter = 1L;
        while cur != 1L {
            set cur = (cur * a ) % mod;
            set counter = counter + 1L;
        }
        return counter;
    }

    /// # Description
    /// does the quantum part of Shor's Algorithm, returns the measured value after performing QFT
    ///
    /// # Inputs
    /// ## a BigInt
    /// the number you want to find the order of
    ///
    /// ## mod Big Int
    /// the modulus you're working in
    ///
    /// # Output
    /// ## BigInt
    ///
    /// #Remarks 
    /// recycles the same single qubit for the entire x register by shifting around the circuit diagram
    /// so all operation involving xi are completed before x(i-1), except for controlling rotations
    /// we use the measured value of xi in a classical if statement to "control" these rotations
    ///
    /// Uses Qubit_Error to simulate errors, you can control probability by editting get_X_Prob in Basics_Error.qs
    ///
    ///you would input this result into FindOrderFromQFT to find the order with high probability
    operation findOrderOfAMod_RecycledXRegisterL_Error(a: BigInt, mod : BigInt) : BigInt {

        //n2 is for the y register which is a^x mod N which means it needs enough bits to store up to N-1
        let n2 = BitSizeL(mod);
        //n1 is for the x register storing exponents
        //and since we need to find a period, we need at least N cycles of up to N-1 length
        //meaning we need to store up to N^2 which uses twice as many bits as N
        let n1 = n2 * 2;
        //this is an array for a^(2^i) so allow us to split the exponentiation into multiplication
        mutable precomputed = [0L, size = n1];

        //since we are BigIntermingling the multiplication and QFT inverse, we can reuse the x qubit for each bit
        use x = Qubit();

        mutable x_error = Qubit_Error(x, get_X_Prob());

        use y = Qubit[n2];
        mutable y_arr = [Qubit_Error(x, get_Y_Prob()), size = n2];
        for i in 0 .. n2-1 {
            set y_arr w/= i <- Qubit_Error(y[i], get_Y_Prob());

        }
        mutable y_error = LittleEndian_Error(y_arr);


        //doing the precomputation for a^(2^i)
        //I guess this could be passed as a parameter since a and mod are fixed 
        for i in 0 .. n1-1 {
            set precomputed w/= i <- modularExponentiationL(a, ExponentL(2L, IntAsBigInt(i)), mod);
        }

        //for storing the measured values of each "bit" in the x register
        mutable measuredXReg = [Zero, size = n1];

        //setting y register equal 1
        // the periodicity is what matters so we should theoretically be able to set y to anything
        // nonzero but I haven't extensively tested this hypothesis
        X_Gate_Error(y_error![0]);
        

        //interweaving multiplying the y register with qft
        for i in n1-1 ..-1.. 0 {
            // in the non-recycled version, H is applied to whole x register to create superposition of all numbers
            H_Gate_Error(x_error);


            Controlled ModularMulByConstantConstantModulusInPlace_Error([x],(mod, precomputed[i], y_error));


            //QFT part
            //do any necessary rotations
            for j in n1-1 ..-1.. i+1 {
                if measuredXReg[j] == One {
                    
                    R1Frac_Gate_Error(1, j-i, x_error);
                }

            }

            H_Gate_Error(x_error);

            //storing measured values for classical controlling and final result
            set measuredXReg w/= (i) <- M_Gate_Error(x_error);

            // xi qubit is being recycled for x(i-1)
            Reset_Error(x_error);
        }
        ResetAll_Error(y_error!);


        return ResultLittleEndiantoBigInt(measuredXReg);
    }


    /// # Description
    /// does the quantum part of Shor's Algorithm, returns the measured value after performing QFT
    ///
    /// # Inputs
    /// ## a BigInt
    /// the number you want to find the order of
    ///
    /// ## mod Big Int
    /// the modulus you're working in
    ///
    /// # Output
    /// ## BigInt
    ///
    /// #Remarks 
    /// recycles the same single qubit for the entire x register by shifting around the circuit diagram
    /// so all operation involving xi are completed before x(i-1), except for controlling rotations
    /// we use the measured value of xi in a classical if statement to "control" these rotations
    ///
    ///you would input this result into FindOrderFromQFT to find the order with high probability
    operation findOrderOfAMod_RecycledXRegisterL(a: BigInt, mod : BigInt) : BigInt {

        //n2 is for the y register which is a^x mod N which means it needs enough bits to store up to N-1
        let n2 = BitSizeL(mod);
        //n1 is for the x register storing exponents
        //and since we need to find a period, we need at least N cycles of up to N-1 length
        //meaning we need to store up to N^2 which uses twice as many bits as N
        let n1 = n2 * 2;
        //this is an array for a^(2^i) so allow us to split the exponentiation into multiplication
        mutable precomputed = [0L, size = n1];

        //since we are BigIntermingling the multiplication and QFT inverse, we can reuse the x qubit for each bit
        use x = Qubit();
        
        use y = Qubit[n2];
        
        mutable y_le = LittleEndian(y);


        //doing the precomputation for a^(2^i)
        //I guess this could be passed as a parameter since n is fixed 
        for i in 0 .. n1-1 {
            set precomputed w/= i <- modularExponentiationL(a, ExponentL(2L, IntAsBigInt(i)), mod);
        }

        //storing the measured values of each "bit" in the x register
        mutable measuredXReg = [Zero, size = n1];

        //setting y register equal to anything non-zero because it doesn't matter
        X(y[0]);

        //interweaving multiplying the y register with qft
        for i in n1-1 ..-1.. 0 {
            // Message($"H({i})");
            // in the non-recycled version, H is applied to whole x register to create superposition of all numbers
            H(x);

            // Message($"Multiplication ");
            // Message($"control: x{i}");
            // Message($"precomputed: {i}");
            // Message("");
            Controlled ModularMulByConstantConstantModulusInPlace([x],(mod, precomputed[i], y_le));

            //starting QFT part
            //do any necessary rotations
            for j in n1-1 ..-1.. i+1 {
                // Message($"Rotation by {j-i}");
                // Message($"Control: x{j}");
                // Message($"Target x{i}");
                // Message("");
                if measuredXReg[j] == One {
                    
                    R1Frac(1, j - i, x);
                }

            }
            // Message($"H({i})");
            H(x);

            set measuredXReg w/= (i) <- M(x);

            Reset(x);
        }
        ResetAll(y_le!);


        return ResultBigEndiantoBigInt(measuredXReg);

        
    }


    /// # summary
    /// does the quantum part of Shor's Algorithm, returns the measured value after performing QFT
    /// 
    ///
    /// # input
    /// ## a BigInt
    /// classical constant a 
    ///
    /// ## mod BigInt
    /// classical constant n 
    ///
    /// # output
    /// ## BigInt
    ///
    /// #remarks
    /// this is the bulk of Shor's Algo, the entire quantum part
    /// you would input this result into FindOrderFromQFT to find the order with high probability
    operation findOrderOfAModL(a : BigInt, mod : BigInt) : BigInt{

        //n2 is for the y register which is a^x mod N which means it needs enough bits to store up to N-1
        let n2 = BitSizeL(mod);
        //n1 is for the x register storing exponents
        //and since we need to find a period, we need at least N cycles of up to N-1 length
        //meaning we need to store up to N^2 which uses twice as many bits as N
        let n1 = n2 * 2;
        //this is an array for a^(2^i) so allow us to split the exponentiation BigInto multiplication
        mutable precomputed = [0L, size = n1];

        use z = Qubit();

        use x = Qubit[n1];


        use y = Qubit[n2];
        
        mutable y_le = LittleEndian(y);

        //doing the precomputation for a^(2^i)
        //I guess this could be passed as a parameter since n is fixed 
        for i in 0 .. n1-1 {
            set precomputed w/= i <- modularExponentiationL(a, ExponentL(2L, IntAsBigInt(i)), mod);
        }
        
        //setting x register to be a unformly random superposition of all numbers 0 to N^2
        for i in 0 .. n1-1 {
            H_Gate_Error(x_arr[i]);
        }

        //setting y register equal to 1
        X_Gate_Error(y_arr[0]);

        //incrementally multiplying y by a^(2^i) mod N, controlled by whether x[i] is 0 or 1
        for i in 0 .. n1-1 {


            Controlled ModularMulByConstantConstantModulusInPlace([x[i]],(mod, precomputed[i], y_le));

        }

        let yreg = QubitLittleEndianToBigInt(y);

        ResetAll(y);

        //now only the x values that caused the measured y value remain in superposition
        //we can find the frequency by appylying QFT and inverting that to find period

        ApplyQFT(x);

        let xreg = QubitLittleEndianToBigInt(x);

        ResetAll(x);

        return xreg;
    }


    /// # summary
    /// does the quantum part of Shor's Algorithm, returns the measured value after performing QFT
    /// 
    ///
    /// # input
    /// ## a BigInt
    /// classical constant a 
    ///
    /// ## mod BigInt
    /// classical constant n 
    ///
    /// # output
    /// ## BigInt
    ///
    /// #remarks
    /// this is the bulk of Shor's Algo, the entire quantum part
    /// you would input this result into FindOrderFromQFT to find the order with high probability
    ///
    /// Uses Qubit_Error to simulate errors, you can control probability by editting get_X_Prob in Basics_Error.qs

    operation findOrderOfAModL_Error(a : BigInt, mod : BigInt) : BigInt{

        //n2 is for the y register which is a^x mod N which means it needs enough bits to store up to N-1
        let n2 = BitSizeL(mod);
        //n1 is for the x register storing exponents
        //and since we need to find a period, we need at least N cycles of up to N-1 length
        //meaning we need to store up to N^2 which uses twice as many bits as N
        let n1 = n2 * 2;
        //this is an array for a^(2^i) so allow us to split the exponentiation into multiplication
        mutable precomputed = [0L, size = n1];

        mutable xreg = 0L;

        //doing the precomputation for a^(2^i)
        //precomputed is little endian so index 0 corresponds to a^2^0
        for i in 0 .. n1-1 {
            set precomputed w/= i <- modularExponentiationL(a, ExponentL(2L, IntAsBigInt(i)), mod);
        }

        //write print statements everywhere to recreate the circuit diagram
        use x = Qubit[n1]{
            mutable x_arr = [Qubit_Error(x[0], get_X_Prob()), size = n1];
            for i in 1 .. n1-1 {
                set x_arr w/= i <- Qubit_Error(x[i], get_X_Prob());
            }
            mutable x_error = LittleEndian_Error(x_arr);


            use y = Qubit[n2]{
                mutable y_arr = [Qubit_Error(y[0], get_Y_Prob()), size = n2];
                for i in 1 .. n2-1 {
                    set y_arr w/= i <- Qubit_Error(y[i], get_Y_Prob());
                }
                mutable y_error = LittleEndian_Error(y_arr);
                
                //setting x register to be a unformly random superposition of all numbers 0 to N^2
                for i in 0 .. n1-1 {
                    H_Gate_Error(x_arr[i]);
                    // Message($"H({i})");
                }
                
                //setting y register equal to 1
                X_Gate_Error(y_arr[0]);

                // Message("y=1\n");

                //incrementally multiplying y by a^(2^i) mod N, controlled by whether x[i] is 0 or 1
                for i in n1-1 ..-1.. 0 {
                    // Message($"Multiplication ");
                    // Message($"control: x{i}");
                    // Message($"precomputed: {i}");
                    // Message("");
                    Controlled ModularMulByConstantConstantModulusInPlace_Error([x[i]],(mod, precomputed[i], y_error));
                }

                let yreg = QubitLittleEndianErrorToInt(y_arr);

                //DumpMachine();
                ResetAll(y);

            }

            //DumpMachine();

            //now only the x values that caused the measured y value remain in superposition
            //we can find the frequency by appylying QFT and inverting that to find period

            ApplyQFT_Error(x_arr);

            set xreg = QubitLittleEndianErrorToBigInt(x_arr);

            ResetAll(x);
        }
        return xreg;
    }

    /// # Description
    /// given the measured value after QFT, apply post-processing to extract a multiple of the order
    ///
    /// # Inputs
    /// ## guess BigInt
    /// the number we want to find order of
    ///
    /// ## mod BigInt
    /// the modulus we are working in
    ///
    /// ## qftresult BigInt
    /// the measured value from findOrderofAMod(add-ons)
    ///
    /// ## n1 Int
    /// the number of qubits in x register
    ///
    /// ## doubles Int
    /// the largest multiple of the denominator you want to check
    /// if we're looking for 4 and qftres = 2, 2/4 is going to show up as 1/2 and we will miss 4
    /// to prevent this, you can set doubles equal to 2
    /// I always set doubles equal to 4 so it checks den, 2den, and 4den
    ///
    /// ## epsilon BigInt
    /// how much plus or minus from each denominator we want to check
    /// if order is 30 and the fraction expansion contains 4/29, we were so close
    /// we might potentially want to search in the immediate vicinity of every denominator
    ///
    /// # Output
    /// ## BigInt
    /// returns -1L if it couldn't find a valid order
    ///
    /// #Remarks
    /// will only return a positive value if guess^value = 1 mod 
    /// but value could actually be a integer multiple of the true order
    function FindOrderFromQFTL(guess : BigInt, mod : BigInt, qftresult : BigInt, n1 : Int, doubles : Int, epsilon : BigInt) : BigInt {
        let Q = 2L^n1;

        let continuedFraction = ContinuedFractionExpansionL(qftresult, Q);
        let convergents = ConvergentsL(continuedFraction);

        for (num, den) in convergents {
            mutable copy = doubles;
            mutable multiple = 1L;

            if den > 0L and den < mod {
                while copy > 0 and den*multiple < mod{

                    mutable power = MaxL(den*multiple - epsilon, 1L);
                    
                    while power <= den*multiple + epsilon and power < mod{
                        if (modularExponentiationL(guess, power, mod) == 1L) {
                            return power;
                        }
                        set power += 1L;
                    }

                    
                    set multiple *= 2L;
                    set copy /= 2;
                    
                }
            }
        }
        return -1L;

    }

    /// # Description
    /// given an integer multiple of the candidate, attempts to reduce it
    /// if answer is even, it checks if answer/2 is also an order candidate
    /// continues until newAnswer/2 no longer satisfies guess^newAnswer = 1 mod
    ///
    /// # Inputs
    /// ## guess BigInt
    /// the number we want to find order of
    ///
    /// ## mod BigInt
    /// the modulus we are working in
    ///
    /// ## answer BigInt
    /// a number that satisfies guess^answer = 1 mod, 
    /// basically an integer multiple of the order
    ///
    /// # Output
    /// ## BigInt
    ///
    /// #Remarks
    /// 
    function RemoveEvenMultiplesL(guess : BigInt, mod : BigInt, answer : BigInt) : BigInt {
        mutable candidate = answer;

        while candidate%2L == 0L and modularExponentiationL(guess, candidate / 2L, mod) == 1L {
                set candidate /= 2L;
        }
        return candidate;
    }

    /// # Description
    /// computes the list of coefficients in continued fraction expansion of num/den
    ///
    /// # Inputs
    /// ## numerator BigInt
    ///
    /// ## denominator BigInt
    ///
    /// # Output
    /// ## BigInt[]
    ///
    function ContinuedFractionExpansionL(numerator : BigInt, denominator : BigInt) : BigInt[] {
        mutable result = [];
        mutable a = numerator;
        mutable b = denominator;
        mutable i = 0;
        while (b != 0L) {
            let q = a / b;
            set result += [q];
            let temp = b;
            set b = a % b;
            set a = temp; 
            set i += 1;
        }
        
        return result;
    }

    /// # Description
    /// given an array of continued fraction coefficients, 
    /// returns a sequence of fractions representing the convergents of the continued frac expansion
    ///
    /// # Inputs
    /// ## continuedFraction BigInt[]
    /// the coefficients of the continued fraction expansion
    ///
    /// # Output
    /// ## (BigInt, BigInt)[]
    /// each tuple in the array represents a fraction
    /// the tuple (num, den) represents the fraction num/den
    ///
    function ConvergentsL(continuedFraction : BigInt[]) : (BigInt, BigInt)[] {
        mutable convergentsList = [];
        mutable prevNumerator = 1L;
        mutable prevPrevNumerator = 0L;
        mutable prevDenominator = 0L;
        mutable prevPrevDenominator = 1L;

        for term in continuedFraction {
            let currentNumerator = term * prevNumerator + prevPrevNumerator;
            let currentDenominator = term * prevDenominator + prevPrevDenominator;
            set convergentsList += [(currentNumerator, currentDenominator)];

            // Update previous values for the next iteration
            set prevPrevNumerator = prevNumerator;
            set prevNumerator = currentNumerator;
            set prevPrevDenominator = prevDenominator;
            set prevDenominator = currentDenominator;
        }

        return convergentsList;
    }
}