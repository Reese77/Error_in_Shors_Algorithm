namespace Tools {
    open Microsoft.Quantum.Math;
    open Microsoft.Quantum.Convert;


    /// # summary
    /// calculates base^exponent
    ///
    /// # input
    /// ## base
    /// classical constant base Int
    ///
    /// ## exponent
    /// classical constant exponent Int
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
    /// ## base
    /// classical constant base BigInt
    ///
    /// ## exponent
    /// classical constant exponent BigInt
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
    /// ## base
    /// classical constant base Int
    ///
    /// ## exponent
    /// classical constant exponent Int
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
    /// ## base
    /// classical constant base BigInt
    ///
    /// ## exponent
    /// classical constant exponent BigInt
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
    /// ## qs
    /// qubit array
    ///
    /// # output
    /// ## Int
    /// the Int generated by measuring qs
    ///
    /// # remarks
    /// qs is a LittleEndian
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
    /// measures qs and returns the BigInt it represents
    ///
    /// # input
    /// ## qs
    /// qubit array
    ///
    /// # output
    /// ## BigInt
    /// the BigInt generated by measuring qs
    ///
    /// # remarks
    /// qs is a LittleEndian
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
    /// calculates gcd(a, b)
    ///
    /// # input
    /// ## a
    /// classical constant a Int
    ///
    /// ## b
    /// classical constant b Int
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
    /// ## a
    /// classical constant a BigInt
    ///
    /// ## b
    /// classical constant b BigInt
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
    /// ## base
    /// classical constant base BigInt
    ///
    /// ## exponent
    /// classical constant exponent BigInt
    ///
    /// # output
    /// ## Int
    /// a ^ b (mod mod)
    ///
    /// #remarks
    /// kinda uses square and multiply technique
    /// it does the recursive call, and squares the result
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
            return multiplyModular(bas, modularExponentiationL(bas, exponent-1L, mod), mod);
        }
        let half = modularExponentiationL(bas, exponent/2L, mod);
        return multiplyModular(half, half, mod);

    }


    /// # summary
    /// computes base^exponent (mod mod)
    ///
    /// # input
    /// ## base
    /// classical constant base BigInt
    ///
    /// ## exponent
    /// classical constant exponent BigInt
    ///
    /// # output
    /// ## Int
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
            return otherModularExponentiationL(multiplyModular(bas, bas, mod), exponent/2L, mod);
        }
        
        return multiplyModular(bas, otherModularExponentiationL(bas, exponent-1L, mod), mod);
    }

    /// # summary
    /// multiplies inputs, reduced mod, returns
    ///
    /// # input
    /// ## a
    /// classical constant multiplicand a Int
    ///
    /// ## b
    /// classical constant multiplier b Int
    ///
    /// # output
    /// ## Int
    /// a * b (mod mod)
    ///
    function multiplyModular(a : BigInt, b : BigInt, mod : BigInt) : BigInt {
        return (a * b) % mod;
    }
}