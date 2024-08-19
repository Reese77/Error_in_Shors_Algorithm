namespace Tools {

    /// # summary
    /// generates a uniformly random number between 0 and max
    ///
    /// # input
    /// ## max Int
    /// classical constant representing the largest acceptable 
    ///
    /// # output
    /// ## Int
    /// the random Int generated
    operation GenerateRandomNumberInRangeI(max : Int) : Int {
        let n = LogarithmI(2, max);

        mutable number = 0;
        for i in 0 .. n - 1{
            if GenerateRandomBit() == One {
                set number += ExponentI(2, i);
                
            }
        }
        if number > max {
            return GenerateRandomNumberInRangeI(max);
        }

        return number;
    }


    /// # summary
    /// generates a uniformly random number between 0 and max
    ///
    /// # input
    /// ## max BigInt
    /// classical constant representing the largest acceptable 
    ///
    /// # output
    /// ## BigInt
    /// the random BigInt generated
    ///
    operation GenerateRandomNumberInRangeL(max : BigInt) : BigInt {
        let n = LogarithmL(2L, max);

        mutable number = 0L;
        mutable counter = 0L;

        while counter < n {
            if GenerateRandomBit() == One {
                set number += ExponentL(2L, counter);
                
            }
            set counter += 1L;
        }
     
        if number > max {
            return GenerateRandomNumberInRangeL(max);
        }

        return number;
    }

    

    /// # summary
    /// generates a One or Zero with 50/50 probability
    ///
    /// # output
    /// ## Result
    /// a Zero or One with 50/50 chance
    ///
    /// # remarks
    ///  uses and resets qubit
    operation GenerateRandomBit() : Result {
        // Allocate a qubit, by default it is in zero state    
        use q = Qubit();  
        // We apply a Hadamard operation H to the state
        // It now has a 50% chance of being measured 0 or 1  
        H(q);      
        // Now we measure the qubit in Z-basis.
        let result = M(q);

        Reset(q);
        // We reset the qubit before releasing it.
        return result;
    }

             
}