namespace Error_In_Shor_Algo {

    open Microsoft.Quantum.Math;
    open Microsoft.Quantum.Convert;
    open Microsoft.Quantum.Crypto.Basics;
    open Microsoft.Quantum.Crypto.ModularArithmetic;
    open Tools;


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
    operation findDivisor(n : BigInt) : BigInt {

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
            let m = findOrderOfAMod_RecycledXRegister(guess, n);
            let order = FindOrderFromQFT(guess, n, 0L, 2 * BitSizeL(n));

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



    operation findOrderOfAMod_RecycledXRegister(a: BigInt, mod : BigInt) : BigInt {

        //n2 is for the y register which is a^x mod N which means it needs enough bits to store up to N-1
        let n2 = BitSizeL(mod);
        //n1 is for the x register storing exponents
        //and since we need to find a period, we need at least N cycles of up to N-1 length
        //meaning we need to store up to N^2 which uses twice as many bits as N
        let n1 = n2 * 2;
        //this is an array for a^(2^i) so allow us to split the exponentiation into multiplication
        mutable precomputed = [0L, size = n1];

        //since we are intermingling the multiplication and QFT inverse, we can reuse the x qubit for each bit
        use x = Qubit();
        use y = Qubit[n2];

        //doing the precomputation for a^(2^i)
        //I guess this could be passed as a parameter since n is fixed 
        for i in 0 .. n1-1 {
            set precomputed w/= i <- modularExponentiationL(a, ExponentL(2L, IntAsBigInt(i)), mod);
        }

        //storing the measured values of each "bit" in the x register
        mutable measuredXReg = [Zero, size = n1];

        //setting y register equal to 1
        X(y[0]);

        //interweaving multiplying the y register with qft
        for i in 0 .. n1 - 1 {
            H(x);

            Controlled ModularMulByConstantConstantModulusInPlace([x],(mod, precomputed[i], LittleEndian(y)));

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
        ResetAll(y);

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
    operation findOrderOfAMod(a : BigInt, mod : BigInt) : BigInt{

        //n2 is for the y register which is a^x mod N which means it needs enough bits to store up to N-1
        let n2 = BitSizeL(mod);
        //n1 is for the x register storing exponents
        //and since we need to find a period, we need at least N cycles of up to N-1 length
        //meaning we need to store up to N^2 which uses twice as many bits as N
        let n1 = n2 * 2;
        //this is an array for a^(2^i) so allow us to split the exponentiation into multiplication
        mutable precomputed = [0L, size = n1];

        use x = Qubit[n1];
        use y = Qubit[n2];


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
            Controlled ModularMulByConstantConstantModulusInPlace([x[i]],(mod, precomputed[i], LittleEndian(y)));
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

    
    function FindOrderFromQFT(a : BigInt, n : BigInt, qftresult : BigInt, n1 : Int) : BigInt {
        let Q = 2L^n1;

        let continuedFraction = ContinuedFractionExpansion(qftresult, Q);
        let convergents = Convergents(continuedFraction);

        for (h, k) in convergents {
            if k > 0L and k < n {
                if (modularExponentiationL(a, k, n) == 1L) {
                    return k;
                }
            }
        }

        //in findDivisor, we repeat the process if order is odd. If somehow this function doesn't return before this point, returning 1 will prevent it from getting through
        return 1L;
    }

    function ContinuedFractionExpansion(numerator : BigInt, denominator : BigInt) : BigInt[] {
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


    function Convergents(continuedFraction : BigInt[]) : (BigInt, BigInt)[] {
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