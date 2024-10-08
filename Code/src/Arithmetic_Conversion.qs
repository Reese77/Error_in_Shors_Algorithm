namespace Tools {
    open Microsoft.Quantum.Math;
    open Microsoft.Quantum.Convert;
    open Microsoft.Quantum.Crypto.Error.Basics;


    /// # Description
    /// returns list of integer multiples of 1/den until den/den
    /// 
    ///
    /// # Inputs
    /// ## den Int
    /// the denominator
    ///
    /// # output
    /// ## Double[]
    /// ex. [1/den, 2/den, ... , den/den]
    function listOfIntegerOverOrder(den : Int) : Double[] {
        mutable retval = [0.0];
        mutable index = 1.0;
        while index <= IntAsDouble(den) {
            set retval = retval + [index/IntAsDouble(den)];
            set index += 1.0;
        }
        return retval;

    }

    /// # Description
    /// returns tuple (d, i) where d is the minimum distance between num and every element in lst
    ///     and i is the index at which this minimum distance occurred
    ///
    /// # Inputs
    /// ## lst Double[]
    /// the list of numbers we want to minimize distance from
    /// ## num Double
    /// the number we want to minimize distance to 
    ///
    /// # output
    /// ## (Double, Int)
    /// tuple (d, i)
    
    function closestDistance(lst : Double[], num : Double) : (Double, Int) {
        mutable dist = AbsD(lst[0] - num);
        mutable integer = 1;
        for i in 1 .. Length(lst)-1 {
            let newDist = AbsD(lst[i] - num);
            if newDist < dist {
                set dist = newDist;
                set integer = i;
            }
            
        }
        return (dist, integer);
    }

    /// # description
    /// calculates base^exponent
    ///
    /// # input
    /// ## base Int
    /// classical constant base 
    ///
    /// ## exponent Int
    /// classical constant exponent 
    ///
    /// # output
    /// ## Int
    /// the base^exponent
    ///
    /// # remarks
    /// does not at all handle integer overflow
    function ExponentI(bas: Int, exponent : Int) : Int {
        mutable n = 1;
        for i in 1 .. exponent {
            set n *= bas;
        }
        return n;
    }

    /// # summary
    /// calculates base^exponent
    ///
    /// # input
    /// ## base BigInt
    /// classical constant base 
    ///
    /// ## exponent BigInt
    /// classical constant exponent 
    ///
    /// # output
    /// ## BigInt
    /// the base^exponent
    ///
    function ExponentL(bas: BigInt, exponent : BigInt) : BigInt {
        mutable n = 1L;
        mutable i = 0L;
        while i < exponent {
            set n *= bas;
            set i += 1L;
        }
        return n;
    }

    /// # summary
    /// calculates log_base(value) rounding UP to the nearest int
    ///
    /// # input
    /// ## base Int
    /// classical constant base 
    ///
    /// ## exponent Int
    /// classical constant exponent 
    ///
    /// # output
    /// ## Int
    /// rounded up Int of log_base(value)
    ///
    /// # remarks
    ///  log(0) = 0 for the purposes of this function
    function LogarithmI(bas: Int, value : Int) : Int {
        if value == 0 {
            return 0;
        }

        return 1 + LogarithmI(bas, value / bas);
    }

    /// # summary
    /// calculates log_base(value) rounding UP to the nearest int
    ///
    /// # input
    /// ## base BigInt
    /// classical constant base 
    ///
    /// ## exponent BigInt
    /// classical constant exponent 
    ///
    /// # output
    /// ## BigInt
    /// rounded up BigInt of log_base(value)
    ///
    /// # remarks
    ///  log(0) = 0 for the purposes of this function
    function LogarithmL(bas: BigInt, value : BigInt) : BigInt {
        if value == 0L {
            return 0L;
        }

        return 1L + LogarithmL(bas, value / bas);
    }


    /// # summary
    /// measures qs and returns the Int it represents
    ///
    /// # input
    /// ## qs Qubit[]
    /// qubit register holding an integer
    ///
    /// # output
    /// ## Int
    /// the Int generated by measuring qs
    ///
    /// # remarks
    /// qs is treated as LittleEndian
    /// all of qs is measured, collapsing superposition
    operation QubitLittleEndianToInt(qs : Qubit[]) : Int {
        mutable num = 0;
        let max = Length(qs) - 1;
        for i in 0 .. max {
            if M(qs[i]) == One {
                set num += ExponentI(2, max - i);
            }
        }
        return num;
        
    }

     /// # summary
    /// measures qs and returns the Int it represents
    ///
    /// # input
    /// ## qs Qubit_Error[]
    /// register holding an integer
    ///
    /// # output
    /// ## Int
    /// the Int generated by measuring qs
    ///
    /// # remarks
    /// qs is treated as LittleEndian
    /// all of qs is measured, collapsing superposition
    operation QubitLittleEndianErrorToInt(qs : Qubit_Error[]) : Int {
        mutable num = 0;
        let max = Length(qs) - 1;
        for i in 0 .. max {
            if M_Gate_Error(qs[i]) == One {
                set num += ExponentI(2, max - i);
            }
        }
        return num;
        
    }

    /// # summary
    /// measures qs and returns the BigInt it represents
    ///
    /// # input
    /// ## qs Qubit[]
    /// register holding an integer
    ///
    /// # output
    /// ## BigInt
    /// the BigInt generated by measuring qs
    ///
    /// # remarks
    /// qs is treated as BigEndian
    /// all of qs is measured, collapsing superposition
    operation QubitLittleEndianToBigInt(qs : Qubit[]) : BigInt {
        mutable num = 0L;
        let max = Length(qs) - 1;
        for i in 0 .. max {

            let res = M(qs[i]);
            if res == One {
                set num += ExponentL(2L, IntAsBigInt(i));
            }
        }
        return num;
        
    }

    /// # summary
    /// measures qs and returns the BigInt it represents
    ///
    /// # input
    /// ## qs Qubit_Error[]
    /// register holding an integer
    ///
    /// # output
    /// ## BigInt
    /// the BigInt generated by measuring qs
    ///
    /// # remarks
    /// qs is treated as BigEndian
    /// all of qs is measured, collapsing superposition
    operation QubitLittleEndianErrorToBigInt(qs : Qubit_Error[]) : BigInt {
        mutable num = 0L;
        let max = Length(qs) - 1;
        for i in 0 .. max {

            let res = M_Gate_Error(qs[i]);
            if res == One {
                set num += ExponentL(2L, IntAsBigInt(i));
            }
        }
        return num;
        
    }

    /// # summary
    /// converts array of results to BigInt and returns it
    ///
    /// # input
    /// ## arr Result[]
    /// array holding an integer
    ///
    /// # output
    /// ## BigInt
    /// the BigInt generated by Results in arr
    ///
    /// # remarks
    /// arr is treated as BigEndian

    function ResultBigEndiantoBigInt(arr : Result[]) : BigInt {
        mutable num = 0L;
        let max = Length(arr) - 1;
        for i in 0 .. max {
            if arr[i] == One {
                set num += ExponentL(2L, IntAsBigInt(max - i));
            }
        }
        return num;
    }

    /// # summary
    /// converts array of results to Int and returns it
    ///
    /// # input
    /// ## arr Result[]
    /// array holding an integer
    ///
    /// # output
    /// ## Int
    /// the Int generated by Results in arr
    ///
    /// # remarks
    /// arr is treated as BigEndian
    function ResultBigEndiantoInt(arr : Result[]) : Int {
        mutable num = 0;
        let max = Length(arr) - 1;
        for i in 0 .. max {
            if arr[i] == One {
                set num += ExponentI(2, max - i);
            }
        }
        return num;
    }

    /// # summary
    /// converts array of results to BigInt and returns it
    ///
    /// # input
    /// ## arr Result[]
    /// array holding an integer
    ///
    /// # output
    /// ## BigInt
    /// the BigInt generated by Results in arr
    ///
    /// # remarks
    /// arr is treated as LittleEndian
    function ResultLittleEndiantoBigInt(arr : Result[]) : BigInt {
        mutable num = 0L;
        let max = Length(arr) - 1;
        for i in 0 .. max {
            if arr[i] == One {
                set num += ExponentL(2L, IntAsBigInt(i));
            }
        }
        return num;
    }

    /// # summary
    /// converts array of results to Int and returns it
    ///
    /// # input
    /// ## arr Result[]
    /// array holding an integer
    ///
    /// # output
    /// ## Int
    /// the Int generated by Results in arr
    ///
    /// # remarks
    /// arr is treated as LittleEndian
    function ResultLittleEndiantoInt(arr : Result[]) : Int {
        mutable num = 0;
        let max = Length(arr) - 1;
        for i in 0 .. max {
            if arr[i] == One {
                set num += ExponentI(2, i);
            }
        }
        return num;
    }

    /// # summary
    /// calculates gcd(a, b)
    ///
    /// # input
    /// ## a Int
    /// classical constant a 
    ///
    /// ## b Int
    /// classical constant b 
    ///
    /// # output
    /// ## Int
    /// the gcd(a, b)
    ///
    /// # remarks
    /// can handle a or b = 0
    /// can handle negative numbers
    /// assumes gcd(0, 0) = 0
    function myGCDI(a : Int, b : Int) : Int {
        
        if a == 0 {
            return AbsI(b);
        }
        if b == 0 {
            return AbsI(a);
        }
        mutable aNew = AbsI(a);
        mutable bNew = AbsI(b);

        if aNew == bNew {
            return aNew;
        }

        if aNew > bNew {
            return myGCDI(bNew, aNew % bNew);
        }
        return myGCDI(aNew, bNew % aNew);
    }


    /// # summary
    /// calculates gcd(a, b)
    ///
    /// # input
    /// ## a BigInt
    /// classical constant a 
    ///
    /// ## b BigInt
    /// classical constant b 
    ///
    /// # output
    /// ## BigInt
    /// the gcd(a, b)
    ///
    /// # remarks
    /// can handle a or b = 0
    /// can handle negative numbers
    /// assumes gcd(0, 0) = 0
    function myGCDL(a : BigInt, b : BigInt) : BigInt {
        
        if a == 0L {
            return AbsL(b);
        }
        if b == 0L {
            return AbsL(a);
        }
        mutable aNew = AbsL(a);
        mutable bNew = AbsL(b);

        if aNew == bNew {
            return aNew;
        }

        if aNew > bNew {
            return myGCDL(bNew, aNew % bNew);
        }
        return myGCDL(aNew, bNew % aNew);
    }

  


    //not sure which of these is better, let me do a little thinking

    /// # summary
    /// computes base^exponent (mod mod)
    ///
    /// # input
    /// ## base BigInt
    /// classical constant base 
    ///
    /// ## exponent BigInt
    /// classical constant exponent 
    ///
    /// # output
    /// ## BigInt
    /// a ^ b (mod mod)
    ///
    /// #remarks
    /// kinda uses square and multiply technique
    /// makes the recursive call, and squares the result, then returns
    ///
    function modularExponentiationL(bas : BigInt, exponent : BigInt, mod : BigInt) : BigInt {
        //Message($"{bas}^{exponent} mod {mod}");
        if exponent == 0L {
            return 1L;
        }
        if exponent == 1L {
            return bas % mod;
        }
        if exponent % 2L == 1L {
            return multiplyModularL(bas, modularExponentiationL(bas, exponent-1L, mod), mod);
        }
        let half = modularExponentiationL(bas, exponent/2L, mod);
        return multiplyModularL(half, half, mod);

    }

    /// # summary
    /// computes base^exponent (mod mod)
    ///
    /// # input
    /// ## base Int
    /// classical constant base 
    ///
    /// ## exponent Int
    /// classical constant exponent 
    ///
    /// # output
    /// ## Int
    /// a ^ b (mod mod)
    ///
    /// #remarks
    /// kinda uses square and multiply technique
    /// makes the recursive call, and squares the result, then returns
    ///
    function modularExponentiationI(bas : Int, exponent : Int, mod : Int) : Int {
        //Message($"{bas}^{exponent} mod {mod}");
        if exponent == 0 {
            return 1;
        }
        if exponent == 1 {
            return bas % mod;
        }
        if exponent % 2 == 1 {
            return multiplyModularI(bas, modularExponentiationI(bas, exponent-1, mod), mod);
        }
        let half = modularExponentiationI(bas, exponent/2, mod);
        return multiplyModularI(half, half, mod);

    }


    /// # summary
    /// computes base^exponent (mod mod)
    ///
    /// # input
    /// ## base BigInt
    /// classical constant base 
    ///
    /// ## exponent BigInt
    /// classical constant exponent 
    ///
    /// # output
    /// ## BigInt
    /// a ^ b (mod mod)
    ///
    /// #remarks
    /// uses square and multiply technique
    /// it squares the base, and recurses on half the exponent
    ///
    function otherModularExponentiationL(bas : BigInt, exponent : BigInt, mod : BigInt) : BigInt {
        if exponent == 1L {
            return bas % mod;
        }
        if exponent % 2L == 0L {
            return otherModularExponentiationL(multiplyModularL(bas, bas, mod), exponent/2L, mod);
        }
        
        return multiplyModularL(bas, otherModularExponentiationL(bas, exponent-1L, mod), mod);
    }

    //I didn't write an int version of this

    /// # summary
    /// multiplies inputs, reduced mod, returns
    ///
    /// # input
    /// ## a Int
    /// classical constant multiplicand a 
    ///
    /// ## b Int
    /// classical constant multiplier b 
    ///
    /// # output
    /// ## Int
    /// a * b (mod mod)
    ///
    function multiplyModularI(a : Int, b : Int, mod : Int) : Int {
        return ((a%mod) * (b%mod)) % mod;
    }

    /// # summary
    /// multiplies inputs, reduced mod, returns
    ///
    /// # input
    /// ## a BigInt
    /// classical constant multiplicand a 
    ///
    /// ## b BigInt
    /// classical constant multiplier b 
    ///
    /// # output
    /// ## BigInt
    /// a * b (mod mod)
    ///
    function multiplyModularL(a : BigInt, b : BigInt, mod : BigInt) : BigInt {
        return ((a%mod) * (b%mod)) % mod;
    }
}