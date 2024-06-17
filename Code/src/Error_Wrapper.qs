namespace Error_In_Shor_Algo {
    open Microsoft.Quantum.Intrinsic;
    open Microsoft.Quantum.Canon;
    // open Microsoft.Quantum.Arithmetic;
    open Microsoft.Quantum.Random;
    open Microsoft.Quantum.Convert;
    open Microsoft.Quantum.Diagnostics;
    open Microsoft.Quantum.Math;

    //probability is an Int between 0-1 000 000 denoting the probability that an error occurs
    //TODO maybe make multiple probabilities for accidentally applying X or Z gate separately
    newtype LittleEndianError = (Data : Qubit[], Probability : Int);

}