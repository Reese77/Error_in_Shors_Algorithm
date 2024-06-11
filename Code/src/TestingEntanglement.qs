namespace MyQuantumProgram {


    operation testing() : (Result, Result, Result, Result) {
        use a = Qubit();
        use b = Qubit();
        use c = Qubit();
        use d = Qubit();

        H(a);
        H(b);

        Controlled X([a], c);
        Controlled X([b], c);

        let bres = M(b);
        let ares = M(a);

        Controlled X([c], d);

        let cres = M(c);
        let dres = M(d);
        

        Reset(a);
        Reset(b);
        Reset(c);
        Reset(d);
        return (ares, bres, cres, dres);
    }
}