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


    /// # summary
    /// attempts 25 times to find a divisor of n using Shor's Algorithm
    ///
    /// # input
    /// ## n
    /// the Int we want to factor
    ///
    /// # output
    /// ## Int
    /// a hopefully non-trivial factor of n
    ///
    /// #remarks
    /// if it can't successfully find a non-trivial factor after 25 attempts, returns 1
    ///
    operation findDivisorI(n : Int) : Int {

        mutable attempts = 0;
        while attempts < 25 {
            set attempts += 1;
            //generate random guess
            //because n is huge, chances of picking the same guess are astronomically tiny
            let guess = GenerateRandomNumberInRangeI(n);

            //if not coprime, return gcd
            let gcd = myGCDI(guess, n);
            if gcd != 1 {
                return gcd;
            }

            //else, find order mod N
            //maybe I should do the precomputation here
            let m = findOrderOfAMod_RecycledXRegisterI_Error(guess, n);
            let almostOrder = FindOrderFromQFTI(guess, n, m, 2 * BitSizeI(n), 4, 0);
            let order = RemoveEvenMultiplesI(guess, n, almostOrder);

            //if order is odd, continue to top of loop
            if order % 2 == 0 {
                //if guess^halforder is -1 mod n, continue to top of loop
                let squareRootOf1 = modularExponentiationI(guess, order / 2, n);
                
                if squareRootOf1 != n-1 {
                    //if gcd(guess^halforder + 1, n) != 1, return it
                    let gcd1 = myGCDI(squareRootOf1 + 1, n);
                    
                    if gcd1 != 1 {
                        return gcd1;
                    }
                    //if gcd(guess^halforder - 1, n) != 1, return it
                    let gcd2 = myGCDI(squareRootOf1 - 1, n);

                    if gcd2 != 1 {
                        return gcd2;
                    }

                    
                }
            }
        }

        return 1;
    }



    function findOrderofAModNaiveI(a : Int, mod : Int) : Int {
        mutable cur = a;
        mutable counter = 1;
        while cur != 1 {
            set cur = (cur * a ) % mod;
            set counter = counter + 1;
        }
        return counter;
    }


    operation findOrderOfAMod_RecycledXRegisterI_Error(a: Int, mod : Int) : Int {

        //n2 is for the y register which is a^x mod N which means it needs enough bits to store up to N-1
        let n2 = BitSizeI(mod);
        //n1 is for the x register storing exponents
        //and since we need to find a period, we need at least N cycles of up to N-1 length
        //meaning we need to store up to N^2 which uses twice as many bits as N
        let n1 = n2 * 2;
        //this is an array for a^(2^i) so allow us to split the exponentiation into multiplication
        mutable precomputed = [0, size = n1];

        //since we are intermingling the multiplication and QFT inverse, we can reuse the x qubit for each bit
        use x = Qubit();
        mutable x_error = Qubit_Error(x, get_X_Prob());
        use y = Qubit[n2];
        mutable y_arr = [Qubit_Error(x, get_Y_Prob()), size = n2];
        for i in 0 .. n2-1 {
            set y_arr w/= i <- Qubit_Error(y[i], get_Y_Prob());
        }
        mutable y_error = LittleEndian_Error(y_arr);


        //doing the precomputation for a^(2^i)
        //I guess this could be passed as a parameter since n is fixed 
        for i in 0 .. n1-1 {
            set precomputed w/= i <- modularExponentiationI(a, ExponentI(2, i), mod);
        }

        //storing the measured values of each "bit" in the x register
        mutable measuredXReg = [Zero, size = n1];

        //setting y register equal to anything non-zero because it doesn't matter
        X_Gate_Error(y_error![0]);
        //X_Gate_Error(y_error![2]);
        //X_Gate_Error(y_error![5]);

        //interweaving multiplying the y register with qft
        for i in 0 .. n1 - 1 {
            H_Gate_Error(x_error);

            let (x_qubit, x_prob) = x_error!;

            Controlled ModularMulByConstantConstantModulusInPlace_Error([x_qubit],(IntAsBigInt(mod), IntAsBigInt(precomputed[i]), y_error));

            //do any necessary rotations
            mutable iterator = 0;
            while iterator < i {
                if measuredXReg[iterator] == One {
                    
                    R1Frac_Gate_Error(1, i - iterator, x_error);
                }

                set iterator += 1;
            }

            H_Gate_Error(x_error);

            set measuredXReg w/= i <- M_Gate_Error(x_error);

            Reset_Error(x_error);
        }
        ResetAll_Error(y_error!);

        return ResultBigEndiantoInt(measuredXReg);

        
    }

    operation findOrderOfAMod_RecycledXRegisterI(a: Int, mod : Int) : Int {

        //n2 is for the y register which is a^x mod N which means it needs enough bits to store up to N-1
        let n2 = BitSizeI(mod);
        //n1 is for the x register storing exponents
        //and since we need to find a period, we need at least N cycles of up to N-1 length
        //meaning we need to store up to N^2 which uses twice as many bits as N
        let n1 = n2 * 2;
        //this is an array for a^(2^i) so allow us to split the exponentiation into multiplication
        mutable precomputed = [0, size = n1];

        //since we are intermingling the multiplication and QFT inverse, we can reuse the x qubit for each bit
        use x = Qubit();
        //// mutable x_error = Qubit_Error(x, get_X_Prob());
        use y = Qubit[n2];
        // // mutable y_arr = [Qubit_Error(x, get_Y_Prob()), size = n2];
        // // for i in 0 .. n2-1 {
        // //     set y_arr w/= i <- Qubit_Error(y[i], get_Y_Prob());
        // // }
        mutable y_le = LittleEndian(y);


        //doing the precomputation for a^(2^i)
        //I guess this could be passed as a parameter since n is fixed 
        for i in 0 .. n1-1 {
            set precomputed w/= i <- modularExponentiationI(a, ExponentI(2, i), mod);
        }

        //storing the measured values of each "bit" in the x register
        mutable measuredXReg = [Zero, size = n1];

        //setting y register equal to anything non-zero because it doesn't matter
        X(y_le![0]);
        //X_Gate_Error(y_error![2]);
        //X_Gate_Error(y_error![5]);

        //interweaving multiplying the y register with qft
        for i in 0 .. n1 - 1 {
            H(x);

            // // let (x_qubit, x_prob) = x_error!;

            Controlled ModularMulByConstantConstantModulusInPlace([x],(IntAsBigInt(mod), IntAsBigInt(precomputed[i]), y_le));

            //do any necessary rotations
            mutable iterator = 0;
            while iterator < i {
                if measuredXReg[iterator] == One {
                    
                    R1Frac(1, i - iterator , x);
                }

                set iterator += 1;
            }

            H(x);

            set measuredXReg w/= i <- M(x);

            Reset(x);
        }
        ResetAll(y_le!);

        return ResultBigEndiantoInt(measuredXReg);

        
    }


    /// # summary
    /// finds the order of a in the multiplicative group Z/nZ
    ///
    /// # input
    /// ## a
    /// classical constant a Int
    ///
    /// ## mod
    /// classical constant n Int
    ///
    /// # output
    /// ## Int
    /// ord(a) in Z/modZ
    ///
    /// #remarks
    /// this is the bulk of Shor's Algo
    ///
    operation findOrderOfAModI_Error(a : Int, mod : Int) : Int{

        //n2 is for the y register which is a^x mod N which means it needs enough bits to store up to N-1
        let n2 = BitSizeI(mod);
        //n1 is for the x register storing exponents
        //and since we need to find a period, we need at least N cycles of up to N-1 length
        //meaning we need to store up to N^2 which uses twice as many bits as N
        let n1 = n2 * 2;
        //this is an array for a^(2^i) so allow us to split the exponentiation into multiplication
        mutable precomputed = [0, size = n1];

        mutable xreg = 0;


        use x = Qubit[n1]{
            mutable x_arr = [Qubit_Error(x[0], get_X_Prob()), size = n1];
            for i in 0 .. n1-1 {
                set x_arr w/= i <- Qubit_Error(x[i], get_X_Prob());
            }
            mutable x_error = LittleEndian_Error(x_arr);


            use y = Qubit[n2]{
                mutable y_arr = [Qubit_Error(y[0], get_Y_Prob()), size = n2];
                for i in 0 .. n2-1 {
                    set y_arr w/= i <- Qubit_Error(y[i], get_Y_Prob());
                }
                mutable y_error = LittleEndian_Error(y_arr);



                //doing the precomputation for a^(2^i)
                //I guess this could be passed as a parameter since n is fixed 
                for i in 0 .. n1-1 {
                    set precomputed w/= i <- modularExponentiationI(a, ExponentI(2, i), mod);
                }
                
                //setting x register to be a unformly random superposition of all numbers 0 to N^2
                for i in 0 .. n1-1 {
                    H_Gate_Error(x_arr[i]);
                }

                
                //setting y register equal to 1
                X_Gate_Error(y_arr[0]);

                
                
                //incrementally multiplying y by a^(2^i) mod N, controlled by whether x[i] is 0 or 1
                for i in 0 .. n1-1 {
                    let (x_qubit, x_prob) = x_error![i]!;

                    Controlled ModularMulByConstantConstantModulusInPlace_Error([x_qubit],(IntAsBigInt(mod), IntAsBigInt(precomputed[i]), y_error));
                }

                

                let yreg = QubitLittleEndianToInt(y);

                //DumpMachine();
                ResetAll(y);

            }

            

            //now only the x values that caused the measured y value remain in superposition
            //we can find the frequency by appylying QFT and inverting that to find period

            ApplyQFT_Error(x_arr);

            DumpMachine();

            set xreg = QubitLittleEndianToInt(x);

            ResetAll(x);

        }

        //extracting period length
        return xreg;
        
    }

    operation findOrderOfAModI(a : Int, mod : Int) : Int{

        //n2 is for the y register which is a^x mod N which means it needs enough bits to store up to N-1
        let n2 = BitSizeI(mod);
        //n1 is for the x register storing exponents
        //and since we need to find a period, we need at least N cycles of up to N-1 length
        //meaning we need to store up to N^2 which uses twice as many bits as N
        let n1 = n2 * 2;
        //this is an array for a^(2^i) so allow us to split the exponentiation into multiplication
        mutable precomputed = [0, size = n1];

        use x = Qubit[n1];
        
        use y = Qubit[n2];
        
        mutable y_le = LittleEndian(y);

        //doing the precomputation for a^(2^i)
        //I guess this could be passed as a parameter since n is fixed 
        for i in 0 .. n1-1 {
            set precomputed w/= i <- modularExponentiationI(a, ExponentI(2, i), mod);
        }
        
        //setting x register to be a unformly random superposition of all numbers 0 to N^2
        for i in 0 .. n1-1 {
            H(x[i]);
        }

        //setting y register equal to 1
        X(y[0]);

        //DumpMachine();

        //incrementally multiplying y by a^(2^i) mod N, controlled by whether x[i] is 0 or 1
        for i in 0 .. n1-1 {
            Message($"{i}");
            Controlled ModularMulByConstantConstantModulusInPlace([x[i]],(IntAsBigInt(mod), IntAsBigInt(precomputed[i]), y_le));
        }

        //DumpMachine();

        let yreg = QubitLittleEndianToInt(y);

        //DumpMachine();
        ResetAll(y);

        //now only the x values that caused the measured y value remain in superposition
        //we can find the frequency by appylying QFT and inverting that to find period

        ApplyQFT(x);

        DumpMachine();

        let xreg = QubitLittleEndianToInt(x);

        ResetAll(x);
        

        //extracting period length
        return xreg;
        
    }

    
    function FindOrderFromQFTI(guess : Int, mod : Int, qftresult : Int, n1 : Int, doubles : Int, epsilon : Int) : Int {
        let Q = 2^n1;

        let continuedFraction = ContinuedFractionExpansionI(qftresult, Q);
        let convergents = ConvergentsI(continuedFraction);

        //Message("Finished calculating convergents");

        for (num, den) in convergents {
            mutable copy = doubles;
            mutable multiple = 1;
            //Message($"den: {den}");
            if den > 0 and den < mod {
                while copy > 0 and den*multiple < mod{
                    //Message($"copy: {copy}");
                    //Message($"multiple: {multiple}");
                    mutable power = MaxI(den*multiple - epsilon, 1);
                    
                    while power <= den*multiple + epsilon and power < mod{
                        if (modularExponentiationI(guess, power, mod) == 1) {
                            return power;
                        }
                        set power += 1;
                    }

                    
                    set multiple *= 2;
                    set copy /= 2;
                    
                }
            }
        }
        return -1;

    }

    function RemoveEvenMultiplesI(guess : Int, mod : Int, answer : Int) : Int {
        mutable candidate = answer;

        while candidate%2 == 0 and modularExponentiationI(guess, candidate / 2, mod) == 1 {
                set candidate /= 2;
        }
        return candidate;
    }

    function ContinuedFractionExpansionI(numerator : Int, denominator : Int) : Int[] {
        mutable result = [];
        mutable a = numerator;
        mutable b = denominator;
        mutable i = 0;
        while (b != 0) {
            let q = a / b;
            set result += [q];
            let temp = b;
            set b = a % b;
            set a = temp; 
            //Message($"q{i}: {q}");
            set i += 1;
        }
        
        return result;
    }


    function ConvergentsI(continuedFraction : Int[]) : (Int, Int)[] {
        mutable convergentsList = [];
        mutable prevNumerator = 1;
        mutable prevPrevNumerator = 0;
        mutable prevDenominator = 0;
        mutable prevPrevDenominator = 1;

        for term in continuedFraction {
            let currentNumerator = term * prevNumerator + prevPrevNumerator;
            let currentDenominator = term * prevDenominator + prevPrevDenominator;
            set convergentsList += [(currentNumerator, currentDenominator)];
            //Message($"{currentNumerator}/{currentDenominator}");

            // Update previous values for the next iteration
            set prevPrevNumerator = prevNumerator;
            set prevNumerator = currentNumerator;
            set prevPrevDenominator = prevDenominator;
            set prevDenominator = currentDenominator;
        }

        return convergentsList;
    }

    /// # summary
    /// attempts 25 times to find a divisor of n using Shor's Algorithm
    ///
    /// # input
    /// ## n
    /// the BigInt we want to factor
    ///
    /// # output
    /// ## BigInt
    /// a hopefully non-trivial factor of n
    ///
    /// #remarks
    /// if it can't successfully find a non-trivial factor after 25 attempts, returns 1
    ///
    operation findDivisorL(n : BigInt) : BigInt {

        mutable attempts = 0;
        while attempts < 25 {
            set attempts += 1;
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
            let m = findOrderOfAMod_RecycledXRegisterL_Error(guess, n);
            let almostOrder = FindOrderFromQFTL(guess, n, m, 2 * BitSizeL(n), 4, 0L);
            let order = RemoveEvenMultiplesL(guess, n, almostOrder);

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



    function findOrderofAModNaiveL(a : BigInt, mod : BigInt) : BigInt {
        mutable cur = a;
        mutable counter = 1L;
        while cur != 1L {
            set cur = (cur * a ) % mod;
            set counter = counter + 1L;
        }
        return counter;
    }


    operation findOrderOfAMod_RecycledXRegisterL_Error(a: BigInt, mod : BigInt) : BigInt {

        //n2 is for the y register which is a^x mod N which means it needs enough bits to store up to N-1
        let n2 = BitSizeL(mod);
        //n1 is for the x register storing exponents
        //and since we need to find a period, we need at least N cycles of up to N-1 length
        //meaning we need to store up to N^2 which uses twice as many bits as N
        let n1 = n2 * 2;
        //this is an array for a^(2^i) so allow us to split the exponentiation BigInto multiplication
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
        //I guess this could be passed as a parameter since n is fixed 
        for i in 0 .. n1-1 {
            set precomputed w/= i <- modularExponentiationL(a, ExponentL(2L, IntAsBigInt(i)), mod);
        }

        //storing the measured values of each "bit" in the x register
        mutable measuredXReg = [Zero, size = n1];

        //setting y register equal to anything non-zero because it doesn't matter
        X_Gate_Error(y_error![0]);
        //X_Gate_Error(y_error![2]);
        //X_Gate_Error(y_error![5]);

        //BigInterweaving multiplying the y register with qft
        for i in 0 .. n1 - 1 {
            H_Gate_Error(x_error);

            let (x_qubit, x_prob) = x_error!;

            Controlled ModularMulByConstantConstantModulusInPlace_Error([x_qubit],(mod, precomputed[i], y_error));

            //do any necessary rotations
            mutable iterator = 0;
            while iterator < i {
                if measuredXReg[iterator] == One {
                    
                    R1Frac_Gate_Error(1, i - iterator, x_error);
                }

                set iterator += 1;
            }

            H_Gate_Error(x_error);

            set measuredXReg w/= i <- M_Gate_Error(x_error);

            Reset_Error(x_error);
        }
        ResetAll_Error(y_error!);

        return ResultBigEndiantoBigInt(measuredXReg);

        
    }

    operation findOrderOfAMod_RecycledXRegisterL(a: BigInt, mod : BigInt) : BigInt {

        //n2 is for the y register which is a^x mod N which means it needs enough bits to store up to N-1
        let n2 = BitSizeL(mod);
        //n1 is for the x register storing exponents
        //and since we need to find a period, we need at least N cycles of up to N-1 length
        //meaning we need to store up to N^2 which uses twice as many bits as N
        let n1 = n2 * 2;
        //this is an array for a^(2^i) so allow us to split the exponentiation BigInto multiplication
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
        //X_Gate_Error(y_error![2]);
        //X_Gate_Error(y_error![5]);

        //BigInterweaving multiplying the y register with qft
        for i in 0 .. n1 - 1 {
            H(x);


            Controlled ModularMulByConstantConstantModulusInPlace([x],(mod, precomputed[i], y_le));

            //do any necessary rotations
            mutable iterator = 0;
            while iterator < i {
                if measuredXReg[iterator] == One {
                    
                    R1Frac(1, i - iterator, x);
                }

                set iterator += 1;
            }

            H(x);

            set measuredXReg w/= i <- M(x);

            Reset(x);
        }
        ResetAll(y_le!);

        return ResultBigEndiantoBigInt(measuredXReg);

        
    }


    /// # summary
    /// finds the order of a in the multiplicative group Z/nZ
    ///
    /// # input
    /// ## a
    /// classical constant a BigInt
    ///
    /// ## mod
    /// classical constant n BigInt
    ///
    /// # output
    /// ## BigInt
    /// ord(a) in Z/modZ
    ///
    /// #remarks
    /// this is the bulk of Shor's Algo
    ///
    operation findOrderOfAModL(a : BigInt, mod : BigInt) : BigInt{

        //n2 is for the y register which is a^x mod N which means it needs enough bits to store up to N-1
        let n2 = BitSizeL(mod);
        //n1 is for the x register storing exponents
        //and since we need to find a period, we need at least N cycles of up to N-1 length
        //meaning we need to store up to N^2 which uses twice as many bits as N
        let n1 = n2 * 2;
        //this is an array for a^(2^i) so allow us to split the exponentiation BigInto multiplication
        mutable precomputed = [0L, size = n1];

    

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
            H(x[i]);
        }

        //setting y register equal to 1
        X(y[0]);

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

        //extracting period length
        return xreg;
        
    }

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


        use x = Qubit[n1]{
            mutable x_arr = [Qubit_Error(x[0], get_X_Prob()), size = n1];
            for i in 0 .. n1-1 {
                set x_arr w/= i <- Qubit_Error(x[i], get_X_Prob());
            }
            mutable x_error = LittleEndian_Error(x_arr);


            use y = Qubit[n2]{
                mutable y_arr = [Qubit_Error(y[0], get_Y_Prob()), size = n2];
                for i in 0 .. n2-1 {
                    set y_arr w/= i <- Qubit_Error(y[i], get_Y_Prob());
                }
                mutable y_error = LittleEndian_Error(y_arr);



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
                    let (x_qubit, x_prob) = x_error![i]!;

                    Controlled ModularMulByConstantConstantModulusInPlace_Error([x_qubit],(mod, precomputed[i], y_error));
                }

                

                let yreg = QubitLittleEndianToInt(y);

                DumpMachine();
                ResetAll(y);

            }

            //DumpMachine();

            //now only the x values that caused the measured y value remain in superposition
            //we can find the frequency by appylying QFT and inverting that to find period

            ApplyQFT_Error(x_arr);

            set xreg = QubitLittleEndianToBigInt(x);

            ResetAll(x);

        }

        //extracting period length
        return xreg;
        
    }

    
    function FindOrderFromQFTL(guess : BigInt, mod : BigInt, qftresult : BigInt, n1 : Int, doubles : Int, epsilon : BigInt) : BigInt {
        let Q = 2L^n1;

        let continuedFraction = ContinuedFractionExpansionL(qftresult, Q);
        let convergents = ConvergentsL(continuedFraction);

        //Message("Finished calculating convergents");

        for (num, den) in convergents {
            mutable copy = doubles;
            mutable multiple = 1L;
            //Message($"den: {den}");
            if den > 0L and den < mod {
                while copy > 0 and den*multiple < mod{
                    //Message($"copy: {copy}");
                    //Message($"multiple: {multiple}");
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

    function RemoveEvenMultiplesL(guess : BigInt, mod : BigInt, answer : BigInt) : BigInt {
        mutable candidate = answer;

        while candidate%2L == 0L and modularExponentiationL(guess, candidate / 2L, mod) == 1L {
                set candidate /= 2L;
        }
        return candidate;
    }

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
            //Message($"q{i}: {q}");
            set i += 1;
        }
        
        return result;
    }


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
            //Message($"{currentNumerator}/{currentDenominator}");

            // Update previous values for the next iteration
            set prevPrevNumerator = prevNumerator;
            set prevNumerator = currentNumerator;
            set prevPrevDenominator = prevDenominator;
            set prevDenominator = currentDenominator;
        }

        return convergentsList;
    }
}