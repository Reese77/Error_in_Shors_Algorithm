namespace Tools {
    open Microsoft.Quantum.Math;
    open Microsoft.Quantum.Arrays;
    open Microsoft.Quantum.Diagnostics;


    /// # summary
    /// performs quantum fourier transform on n qubits
    ///
    /// # input
    /// ## qs
    /// array of qubits
    ///
    /// # remarks
    /// Not exactly sure if this is little or big endian
    /// Modifies qs
    ///
    /// I used Figure 4 in this paper
    /// https://www.math.mcgill.ca/darmon/courses/12-13/nt/projects/Fangxi-Lin.pdf
    /// and I also used the first diagram on this website
    /// https://learn.microsoft.com/en-us/azure/quantum/tutorial-qdk-qubit-level-program?tabs=tabid-qsharp%2Ctabid-qsharp2
    /// to preform the operation
    ///
    operation PerformNqubitQFT(qs : Qubit[]) : Unit {
        let lastIndex = Length(qs) - 1;
        mutable divisor = 2.0;

        //applying H and R gates
        for i in 0 .. lastIndex {
            Message($"i: {i}");
            H(qs[i]);
            set divisor = 2.0;
            for j in i+1 .. lastIndex {
                Message($"j: {j}");
                Controlled R1([qs[j]], (PI()/divisor, qs[i]));
                set divisor *= 2.0;
            }

        }
        //applying swaps
        for i in 0 .. Length(qs)/2 - 1 {
            Message($"{i}");
            SWAP(qs[i], qs[lastIndex - i]);
        }

    }

    /// # summary
    /// performs quantum fourier transform on 3 qubits
    ///
    /// # outputs
    /// Result[]
    /// apply QFT to 3 qubits, measure them, return the results
    ///
    /// # remarks
    ///
    /// Copied from this tutorial
    /// https://learn.microsoft.com/en-us/azure/quantum/tutorial-qdk-qubit-level-program?tabs=tabid-qsharp%2Ctabid-qsharp2
    /// 
    operation Perform3qubitQFT() : Result[] {
       mutable resArr = [Zero, size = 3];
       use qs = Qubit[3];
       

       H(qs[0]);
       Controlled R1([qs[1]], (PI()/2.0, qs[0]));
       Controlled R1([qs[2]], (PI()/4.0, qs[0]));

       H(qs[1]);
       Controlled R1([qs[2]], (PI()/2.0, qs[1]));

       H(qs[2]);

       SWAP(qs[0], qs[2]);

       Message("Before measuring");
       DumpMachine();

       for i in IndexRange(qs) {
            set resArr w/= i <- M(qs[i]);
       }

       Message("After");
       DumpMachine();
       ResetAll(qs);

       return resArr;
    }
}