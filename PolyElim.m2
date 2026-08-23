newPackage(
    "PolyElim",
    Version => "2.3",
    Date => "August 23, 2026",
    Authors => {
        {Name => "Aditya Tyagi"}
    },
    Headline => "Polynomial system solving via elimination with adaptive splitting",
    Keywords => {
        "Elimination",
        "Polynomial Systems",
        "Groebner Bases"
    }
)


------------------------------------------------------------
-- Required packages
------------------------------------------------------------

needsPackage "Elimination";
needsPackage "Saturation";


------------------------------------------------------------
-- Exported symbols
------------------------------------------------------------

export {
    "eliminationSolve",
    "isZeroDimensionalSystem",
    "MaxSplitDepth",
    "Tolerance"
}


------------------------------------------------------------
-- Numerical scratch ring
------------------------------------------------------------

scratchRing = CC[t];
scratchVar = scratchRing_0;


------------------------------------------------------------
-- Convert a constant element of scratchRing to CC
------------------------------------------------------------

convertToCC = r -> (
    lift(r,CC)
);


------------------------------------------------------------
-- Clean numerical values
--
-- Numerical root computations can occasionally return tiny
-- floating-point values such as 6.1e-310 when the exact
-- answer is zero.
------------------------------------------------------------

cleanNumericalValue = (z,tol) -> (
    if abs(z) < tol then
        0_CC
    else
        z
);


------------------------------------------------------------
-- Clean every coordinate of a numerical solution
------------------------------------------------------------

cleanNumericalSolution = (sol,tol) -> (
    apply(
        sol,
        z -> cleanNumericalValue(z,tol)
    )
);


------------------------------------------------------------
-- Zero-dimensionality
------------------------------------------------------------

isZeroDimensionalSystem = method()

isZeroDimensionalSystem Ideal := I -> (
    dim I == 0
)


------------------------------------------------------------
-- Test whether a polynomial is constant
------------------------------------------------------------

isConstantPolynomial = f -> (
    #support f == 0
)


------------------------------------------------------------
-- Check that vrs contains exactly the variables of R
------------------------------------------------------------

validVariableList = (I,vrs) -> (
    R := ring I;
    n := numgens R;

    if #vrs != n then
        return false;

    all(
        0..(n-1),
        i -> vrs#i === R_i
    )
)


------------------------------------------------------------
-- Does f involve only variables
-- v_i,...,v_(n-1)?
------------------------------------------------------------

isAtEliminationLevel = (f,vrs,i) -> (
    supp := support f;

    if #supp == 0 then
        return false;

    allowed := set apply(
        i..(#vrs-1),
        j -> vrs#j
    );

    all(
        supp,
        v -> member(v,allowed)
    )
)


------------------------------------------------------------
-- Does f involve variable v?
------------------------------------------------------------

involvesVariable = (f,v) -> (
    member(v,support f)
)


------------------------------------------------------------
-- Find polynomials suitable for solving v_i
------------------------------------------------------------

findEliminationPolynomials = (polys,vrs,i) -> (
    select(
        polys,
        f ->
            isAtEliminationLevel(f,vrs,i)
            and
            involvesVariable(f,vrs#i)
    )
)


------------------------------------------------------------
-- Specialize a polynomial.
--
-- Earlier variables:
--     mapped to zero
--
-- Current variable:
--     mapped to t
--
-- Later variables:
--     replaced by previously computed roots
------------------------------------------------------------

specializePolynomial = (f,vrs,i,solValues) -> (
    R := ring f;

    images := apply(
        numgens R,
        j -> (
            rvar := R_j;

            p := position(
                0..(#vrs-1),
                j2 -> vrs#j2 === rvar
            );

            if p === null then
                error (
                    "specializePolynomial: variable not found"
                );

            if p < i then
                0_scratchRing

            else if p == i then
                scratchVar

            else
                convertToCC(
                    solValues#((#vrs - 1) - p)
                )
        )
    );

    phi := map(
        scratchRing,
        R,
        images
    );

    phi f
)


------------------------------------------------------------
-- Verify a complete numerical solution against I
------------------------------------------------------------

verifyCompleteSolution = (I,vrs,sol,tol) -> (
    R := ring I;

    images := apply(
        numgens R,
        j -> (
            rvar := R_j;

            p := position(
                0..(#vrs-1),
                k -> vrs#k === rvar
            );

            if p === null then
                error (
                    "verifyCompleteSolution: inconsistent variable list"
                );

            promote(
                sol#p,
                scratchRing
            )
        )
    );

    phi := map(
        scratchRing,
        R,
        images
    );

    all(
        flatten entries gens I,
        f -> (
            val := phi f;

            if isConstantPolynomial val then
                abs(lift(val,CC)) < tol
            else
                false
        )
    )
)


------------------------------------------------------------
-- Numerical equality of two solutions
------------------------------------------------------------

sameNumericalSolution = (a,b,tol) -> (
    if #a != #b then
        return false;

    all(
        0..(#a-1),
        i -> abs(a#i - b#i) < tol
    )
)


------------------------------------------------------------
-- Remove duplicate numerical solutions
------------------------------------------------------------

uniqueNumericalSolutions = (solutions,tol) -> (
    result := {};

    for sol in solutions do (
        alreadyThere := any(
            result,
            oldSol ->
                sameNumericalSolution(
                    sol,
                    oldSol,
                    tol
                )
        );

        if not alreadyThere then
            result = append(
                result,
                sol
            );
    );

    result
)


------------------------------------------------------------
-- Choose the lowest-degree candidate
------------------------------------------------------------

bestCandidate = useful -> (
    degs := apply(
        useful,
        h -> degree(scratchVar,h)
    );

    useful#(minPosition degs)
)


------------------------------------------------------------
-- Triangular back-substitution
------------------------------------------------------------

triangularSolve = (I,vrs,tol) -> (
    G := gb I;
    polys := flatten entries gens G;
    n := #vrs;

    partialSolutions := {{}};

    for i in reverse toList(0..n-1) do (

        candidates := findEliminationPolynomials(
            polys,
            vrs,
            i
        );

        if #candidates == 0 then
            return null;

        newSolutions := {};

        for sol in partialSolutions do (

            specialized := apply(
                candidates,
                f ->
                    specializePolynomial(
                        f,
                        vrs,
                        i,
                        sol
                    )
            );

            useful := select(
                specialized,
                h -> h != 0
            );

            if #useful == 0 then
                continue;

            h := bestCandidate useful;

            if isConstantPolynomial h then
                continue;

            rts := roots(
                h,
                Unique => true
            );

            for r in rts do (
                newSolutions = append(
                    newSolutions,
                    append(
                        sol,
                        convertToCC(r)
                    )
                );
            );
        );

        partialSolutions = newSolutions;

        if #partialSolutions == 0 then
            return {};
    );

    --------------------------------------------------------
    -- Reverse the order of the recursively found values
    -- and clean numerical zeros.
    --------------------------------------------------------

    finalSolutions := apply(
        partialSolutions,
        sol ->
            cleanNumericalSolution(
                reverse sol,
                tol
            )
    );

    verified := select(
        finalSolutions,
        sol ->
            verifyCompleteSolution(
                I,
                vrs,
                sol,
                tol
            )
    );

    uniqueNumericalSolutions(
        verified,
        tol
    )
)


------------------------------------------------------------
-- Find a coefficient-splitting candidate
--
-- We look for
--
--     f = g*x^d + lower terms
--
-- where g depends only on variables later in the
-- elimination order.
------------------------------------------------------------

findSplitCandidate = (polys,vrs) -> (
    n := #vrs;

    for i from 0 to n-1 do (

        x := vrs#i;

        for f in polys do (

            if member(x,support f) then (

                d := degree(x,f);

                if d > 0 then (

                    c := coefficient(
                        x^d,
                        f
                    );

                    if not isConstantPolynomial c then (

                        laterVars := set {};

                        if i+1 <= n-1 then
                            laterVars = set apply(
                                i+1..(n-1),
                                j -> vrs#j
                            );

                        suppc := support c;

                        if all(
                            suppc,
                            z -> member(z,laterVars)
                        ) then
                            return (x,c);
                    );
                );
            );
        );
    );

    null
)


------------------------------------------------------------
-- Recursive elimination and splitting
------------------------------------------------------------

eliminationSolveHelper = (
    I,
    vrs,
    depth,
    maxDepth,
    tol,
    verbose
) -> (

    if verbose then (
        print "";
        print "----------------------------------------------";
        print (
            "Elimination depth = "
            | toString depth
        );
        print "----------------------------------------------";
    );


    G := gb I;
    polys := flatten entries gens G;


    --------------------------------------------------------
    -- Unit ideal
    --------------------------------------------------------

    if any(
        polys,
        f -> f == 1
    ) then (

        if verbose then
            print "Unit ideal: no solutions.";

        return {};
    );


    --------------------------------------------------------
    -- Zero-dimensionality
    --------------------------------------------------------

    if not isZeroDimensionalSystem I then (

        if verbose then
            print "System is not zero-dimensional.";

        return {};
    );


    --------------------------------------------------------
    -- First attempt triangular solving
    --------------------------------------------------------

    result := triangularSolve(
        I,
        vrs,
        tol
    );

    if result =!= null then (

        if verbose then
            print "Triangular system solved.";

        return result;
    );


    --------------------------------------------------------
    -- Stop if maximum splitting depth is reached
    --------------------------------------------------------

    if depth >= maxDepth then (

        if verbose then
            print "Maximum splitting depth reached.";

        return {};
    );


    --------------------------------------------------------
    -- Find splitting coefficient
    --------------------------------------------------------

    cand := findSplitCandidate(
        polys,
        vrs
    );

    if cand === null then (

        if verbose then
            print "No suitable splitting coefficient found.";

        return {};
    );


    (x,g) := cand;


    if verbose then (
        print "";
        print "Splitting candidate:";
        print g;

        print "";
        print (
            "Variable: "
            | toString x
        );
    );


    --------------------------------------------------------
    -- Branch A: g = 0
    --------------------------------------------------------

    if verbose then (
        print "";
        print "Branch A: g = 0";
    );

    IA := trim(
        I + ideal(g)
    );

    solA := eliminationSolveHelper(
        IA,
        vrs,
        depth + 1,
        maxDepth,
        tol,
        verbose
    );


    --------------------------------------------------------
    -- Branch B: g != 0
    --
    -- This is I : g^infinity.
    --------------------------------------------------------

    if verbose then (
        print "";
        print "Branch B: g != 0";
    );

    IB := saturate(
        I,
        g,
        Strategy => Eliminate
    );

    solB := eliminationSolveHelper(
        IB,
        vrs,
        depth + 1,
        maxDepth,
        tol,
        verbose
    );


    --------------------------------------------------------
    -- Combine branches and remove duplicates
    --------------------------------------------------------

    uniqueNumericalSolutions(
        solA | solB,
        tol
    )
)


------------------------------------------------------------
-- Public solver
------------------------------------------------------------

eliminationSolve = method(
    Options => {
        MaxSplitDepth => 6,
        Tolerance => 1e-6,
        Verbose => true
    }
)


eliminationSolve(
    Ideal,
    List
) := opts -> (I,vrs) -> (

    R := ring I;


    --------------------------------------------------------
    -- Polynomial ring check
    --------------------------------------------------------

    if not isPolynomialRing R then
        error (
            "eliminationSolve: expected an ideal in a "
            | "polynomial ring"
        );


    --------------------------------------------------------
    -- Variable list check
    --------------------------------------------------------

    if not validVariableList(
        I,
        vrs
    ) then
        error (
            "eliminationSolve: vrs must contain exactly the "
            | "generators of ring I, in the chosen order"
        );


    --------------------------------------------------------
    -- Option checks
    --------------------------------------------------------

    if opts.MaxSplitDepth < 0 then
        error (
            "eliminationSolve: MaxSplitDepth must be nonnegative"
        );

    if opts.Tolerance <= 0 then
        error (
            "eliminationSolve: Tolerance must be positive"
        );


    --------------------------------------------------------
    -- Zero-dimensionality
    --------------------------------------------------------

    if not isZeroDimensionalSystem I then (

        if opts.Verbose then
            print (
                "PolyElim: system is not zero-dimensional."
            );

        return {};
    );


    --------------------------------------------------------
    -- Header
    --------------------------------------------------------

    if opts.Verbose then (
        print "";
        print "==============================================";
        print "                 PolyElim";
        print "==============================================";

        print (
            "Variables: "
            | toString vrs
        );

        print (
            "MaxSplitDepth = "
            | toString opts.MaxSplitDepth
        );

        print (
            "Tolerance = "
            | toString opts.Tolerance
        );

        print "";
    );


    --------------------------------------------------------
    -- Solve
    --------------------------------------------------------

    result := eliminationSolveHelper(
        I,
        vrs,
        0,
        opts.MaxSplitDepth,
        opts.Tolerance,
        opts.Verbose
    );


    result = apply(
        result,
        sol ->
            cleanNumericalSolution(
                sol,
                opts.Tolerance
            )
    );


    result = uniqueNumericalSolutions(
        result,
        opts.Tolerance
    );


    --------------------------------------------------------
    -- Final output
    --------------------------------------------------------

    if opts.Verbose then (
        print "";
        print "==============================================";
        print "              FINAL SOLUTIONS";
        print "==============================================";
        print result;
    );


    result
)


------------------------------------------------------------
-- Documentation
------------------------------------------------------------

beginDocumentation()


doc ///
    Key
        PolyElim
    Headline
        Polynomial system solving via elimination
    Description
        Text
            PolyElim solves zero-dimensional systems of
            polynomial equations using Groebner bases,
            triangular solving, and adaptive coefficient
            splitting.

            The algorithm is based on elimination methods for
            polynomial systems.

            If a polynomial has the form

                $f = g x^d + \text{lower terms}$,

            where $g$ involves only variables later in the
            elimination order, the algorithm splits into the
            cases $g=0$ and $g\neq0$.

            The $g=0$ branch is obtained by adjoining $g$ to
            the ideal.

            The $g\neq0$ branch is obtained by saturation:

                $I : g^\infty$.

            The resulting systems are solved recursively.

            Numerical solutions obtained by back-substitution
            are verified against the original ideal.

            The current version requires the supplied variable
            list to contain exactly the generators of the
            polynomial ring.
///


doc ///
    Key
        eliminationSolve
        (eliminationSolve, Ideal, List)
    Headline
        solve a polynomial system via elimination
    Usage
        eliminationSolve(I,vrs)
        eliminationSolve(I,vrs,MaxSplitDepth => d)
        eliminationSolve(I,vrs,Tolerance => eps)
        eliminationSolve(I,vrs,Verbose => b)
    Inputs
        I:Ideal
            a zero-dimensional ideal in a polynomial ring
        vrs:List
            the generators of the polynomial ring in the
            chosen elimination order
        MaxSplitDepth => ZZ
            maximum recursive splitting depth
        Tolerance => RR
            numerical tolerance used for verification
        Verbose => Boolean
            whether to print diagnostic information
    Outputs
        :List
            a list of numerical solutions
    Description
        Text
            The solver first computes a Groebner basis and
            attempts triangular back-substitution.

            If triangular solving fails, the algorithm searches
            for a suitable leading coefficient.

            For

                $f = g x^d + \text{lower terms}$,

            the system is split into $g=0$ and $g\neq0$.

            The first branch adds $g$ to the ideal.

            The second branch computes the saturation

                $I : g^\infty$.

            The two branches are solved recursively.

            Candidate numerical solutions are verified against
            the original ideal.
///


doc ///
    Key
        isZeroDimensionalSystem
        (isZeroDimensionalSystem, Ideal)
    Headline
        test whether an ideal is zero-dimensional
    Usage
        isZeroDimensionalSystem I
    Inputs
        I:Ideal
    Outputs
        :Boolean
            true if the ideal is zero-dimensional
    Description
        Text
            Tests whether the dimension of the ideal is zero.
///


doc ///
    Key
        MaxSplitDepth
    Headline
        maximum recursive splitting depth
    Description
        Text
            MaxSplitDepth controls how many recursive
            coefficient splits are allowed.

            The default value is 6.
///


doc ///
    Key
        Tolerance
    Headline
        numerical verification tolerance
    Description
        Text
            Tolerance controls the numerical tolerance used
            when checking candidate solutions against the
            original ideal.

            The default value is 1e-6.
///


doc ///
    Key
        Verbose
    Headline
        control diagnostic output
    Description
        Text
            If Verbose is true, eliminationSolve prints
            information about recursive elimination and
            splitting.

            The default value is true.
///


------------------------------------------------------------
-- Tests
------------------------------------------------------------

TEST ///
    -- Simple univariate quadratic.

    R = QQ[x];

    I = ideal(
        x^2 - 1
    );

    sols = eliminationSolve(
        I,
        {x},
        Verbose => false
    );

    assert(
        #sols == 2
    );

    assert(
        all(
            sols,
            sol -> abs(
                sol#0^2 - 1
            ) < 1e-6
        )
    );
///


TEST ///
    -- Two-variable example.

    R = QQ[x,y,MonomialOrder => Lex];

    I = ideal(
        x^2 - y^2 + 11 + y,
        x^3 - x*y^2 + 12
    );

    sols = eliminationSolve(
        I,
        {x,y},
        Verbose => false
    );

    assert(
        #sols == 4
    );

    assert(
        all(
            sols,
            sol -> (
                xv := sol#0;
                yv := sol#1;

                abs(
                    xv^2 - yv^2 + 11 + yv
                ) < 1e-6

                and

                abs(
                    xv^3 - xv*yv^2 + 12
                ) < 1e-6
            )
        )
    );
///


TEST ///
    -- Inconsistent system.

    R = QQ[x];

    I = ideal(
        x,
        x - 1
    );

    sols = eliminationSolve(
        I,
        {x},
        Verbose => false
    );

    assert(
        sols == {}
    );
///


TEST ///
    -- Zero-dimensionality.

    R = QQ[x,y];

    assert(
        isZeroDimensionalSystem(
            ideal(
                x^2 - 1,
                y^2 - 1
            )
        )
    );

    assert(
        not isZeroDimensionalSystem(
            ideal(
                x - y
            )
        )
    );
///


TEST ///
    -- Invalid variable list must produce an error.

    R = QQ[x,y];

    I = ideal(
        x^2 - 1,
        y^2 - 1
    );

    caught := false;

    try (
        eliminationSolve(
            I,
            {x},
            Verbose => false
        );
    ) else (
        caught = true;
    );

    assert(
        caught
    );
///


TEST ///
    -- Triangular system with four solutions.

    R = QQ[x,y,MonomialOrder => Lex];

    I = ideal(
        y^2 - 1,
        x^2 - y
    );

    sols = eliminationSolve(
        I,
        {x,y},
        Verbose => false
    );

    assert(
        #sols == 4
    );

    assert(
        all(
            sols,
            sol -> (
                xv := sol#0;
                yv := sol#1;

                abs(
                    yv^2 - 1
                ) < 1e-6

                and

                abs(
                    xv^2 - yv
                ) < 1e-6
            )
        )
    );
///


TEST ///
    -- Coefficient-splitting example.

    R = QQ[x,y,MonomialOrder => Lex];

    I = ideal(
        y*x + 1,
        y^2 - 1
    );

    sols = eliminationSolve(
        I,
        {x,y},
        Verbose => false
    );

    assert(
        #sols == 2
    );

    assert(
        all(
            sols,
            sol -> (
                xv := sol#0;
                yv := sol#1;

                abs(
                    yv*xv + 1
                ) < 1e-6

                and

                abs(
                    yv^2 - 1
                ) < 1e-6
            )
        )
    );
///


end
