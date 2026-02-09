
clearAll
needsPackage "NumericalCertification"
uninstallPackage("Bertini")
needsPackage("Bertini",  Configuration=>{"BERTINIexecutable"=>"bertini"})

--Section 5 Code


--Builds matrix for the 1D periodic Laplacian
--assumes at least 3 vertices.
BlockPeriodicMatrix1DLap = method(TypicalValue => List)
BlockPeriodicMatrix1DLap(ZZ) := (Sequence) => (a)-> (
     local outMatrix;
     local R;
     R = QQ[x_1,z,y_1,q_1 .. q_(a)];
     local currow;
     local toprow;
     local botrow;
     toprow = flatten {{2 + q_1-z,-1},(new List from (a-3):0_R), {-y_1}};
     botrow = flatten {{-x_1},(new List from (a-3):0_R), {-1,2 + q_a-z}};
     outMatrix = {toprow};
    for i from 2 to a-1 do( 
     currow = flatten{(new List from (i-2):0_R), {-1,2+q_i-z,-1}, (new List from (a-i-1):0_R)};
     outMatrix = append(outMatrix,currow);
     );       
        outMatrix = append(outMatrix,botrow);
        outMatrix = matrix(outMatrix);
     return (outMatrix,R)
     )
 

--Solving symbolically is very slow, and for our purposes it will suffice to compute numerical solutions as we are only interested in finding explicit solutions.

needsPackage "NumericalAlgebraicGeometry";


---------------------------------------------------------------
-- 1. Helpers: coordinates & complex-norm distance
---------------------------------------------------------------

-- Extract coordinates of a Point or return the list itself
-- If p is a Point: use p#Coordinates
-- If p is already a list of numbers: just return p
coords = p -> (
    if class p === Point then p#Coordinates else p
);

-- squared modulus of a (possibly complex) number
squareModulus = z -> (
    (realPart z)^2 + (imaginaryPart z)^2
);

-- squared Euclidean distance between two coordinate lists u, v,
-- with early cutoff if partial sum already exceeds eps2
distance2CoordsBounded = (u, v, eps2) -> (
    u = coords u;
    v = coords v;
    n := #u;
    s := 0.;
    i := 0;
    while i < n and s <= eps2 do (
        d := u#i - v#i;
        s = s + squareModulus d;
        i = i + 1;
    );
    s
);

---------------------------------------------------------------
-- 2. Dihedral orbit on coordinate lists
---------------------------------------------------------------

-- all dihedral (rotation + reflection) permutations of a coord list v
dihedralOrbitCoords = v -> (
    v = coords v;
    n := #v;
    L := {};
    -- rotations
    for k from 0 to n-1 do (
        L = append(L, for i from 0 to n-1 list v#((i + k) % n));
    );
    -- reflections (reverse then rotate)
    vr := reverse v;
    for k from 0 to n-1 do (
        L = append(L, for i from 0 to n-1 list vr#((i + k) % n));
    );
    L
);

---------------------------------------------------------------
-- 3. Prune up to dihedral symmetry (optimized)
---------------------------------------------------------------

-- pts : list of Points or lists
-- eps : tolerance (real)
pruneDihedral = (pts, eps) -> (
    nPts := #pts;
    if nPts == 0 then return {};

    eps2 := eps^2;

    -- precompute coordinates and orbits
    coordList := new MutableList from apply(pts, p -> coords p);
    orbitList := new MutableList from apply(nPts, i -> dihedralOrbitCoords(coordList#i));

    isClose = (i, j) -> (
        u := coordList#i;
        O := orbitList#j;
        m := #O;
        k := 0;
        while k < m do (
            d2 := distance2CoordsBounded(u, O#k, eps2);
            if d2 < eps2 then return true;
            k = k + 1;
        );
        false
    );

    repsIdx := {};
    for i from 0 to nPts-1 do (
        isNew := true;
        scan(repsIdx, r -> (
            if isClose(i, r) then isNew = false;
        ));
        if isNew then repsIdx = append(repsIdx, i);
    );

    apply(repsIdx, i -> pts#i)
);

---------------------------------------------------------------
-- 4. Cluster near-duplicates WITHOUT symmetry
---------------------------------------------------------------

-- Cluster points that are within eps of each other WITHOUT symmetry
-- Returns: list of lists of indices, e.g. {{0,7,9}, {1}, {2,5}, ...}
nearDuplicateClustersNoDihedral = (pts, eps) -> (
    n := #pts;
    if n == 0 then return {};

    eps2 := eps^2;
    coordList := new MutableList from apply(pts, p -> coords p);

    isClosePlain = (i, j) -> (
        u := coordList#i;
        v := coordList#j;
        distance2CoordsBounded(u, v, eps2) < eps2
    );

    clustersIdx := {};
    visited := new MutableList from apply(n, i -> false);

    for i from 0 to n-1 do (
        if not visited#i then (
            current := {i};
            visited#i = true;
            for j from i+1 to n-1 do (
                if not visited#j and isClosePlain(i, j) then (
                    current = append(current, j);
                    visited#j = true;
                );
            );
            clustersIdx = append(clustersIdx, current);
        );
    );
    clustersIdx
);

---------------------------------------------------------------
-- 5. List all close pairs (NO dihedral)
---------------------------------------------------------------

-- Returns: list of {i, j, distance} for pairs within eps
findClosePairsNoDihedral = (pts, eps) -> (
    n := #pts;
    if n == 0 then return {};

    eps2 := eps^2;
    coordList := new MutableList from apply(pts, p -> coords p);

    pairs := {};
    for i from 0 to n-1 do (
        for j from i+1 to n-1 do (
            d2 := distance2CoordsBounded(coordList#i, coordList#j, eps2);
            if d2 < eps2 then (
                pairs = append(pairs, {i, j, sqrt d2});
            );
        );
    );
    pairs
);

---------------------------------------------------------------
-- 6. Full symmetry orbit: ± and conjugation + dihedral
---------------------------------------------------------------

symmetryOrbitCoords = v -> (
    v = coords v;
    v1 := v;
    v2 := apply(v, z -> -z);
    v3 := apply(v, z -> conjugate z);
    v4 := apply(v, z -> - conjugate z);

    L := {};
    for w in {v1, v2, v3, v4} do (
        L = L | dihedralOrbitCoords w;
    );
    L
);

---------------------------------------------------------------
-- 7. Prune up to all symmetries (dihedral + ± + conjugate)
---------------------------------------------------------------

-- pts : list of Points or lists
pruneSymmetric = (pts, eps) -> (
    nPts := #pts;
    if nPts == 0 then return {};

    eps2 := eps^2;

    coordList    := new MutableList from apply(pts, p -> coords p);
    symOrbitList := new MutableList from apply(nPts, i -> symmetryOrbitCoords(coordList#i));

    isCloseSym = (i, j) -> (
        u := coordList#i;
        O := symOrbitList#j;
        m := #O;
        k := 0;
        while k < m do (
            d2 := distance2CoordsBounded(u, O#k, eps2);
            if d2 < eps2 then return true;
            k = k + 1;
        );
        false
    );

    repsIdx := {};
    for i from 0 to nPts-1 do (
        isNew := true;
        scan(repsIdx, r -> (
            if isCloseSym(i, r) then isNew = false;
        ));
        if isNew then repsIdx = append(repsIdx, i);
    );

    apply(repsIdx, i -> pts#i)
);

---------------------------------------------------------------
-- 8. Filter points outside a radius (works for Points or lists)
---------------------------------------------------------------

outsideRadius = (L, R) -> (
    select(L, pt -> (
        v := coords pt;
        norm2 := sum apply(v, z -> z * conjugate z);
        sqrt(norm2) > R
    ))
);

---------------------------------------------------------------
-- 9. Count symmetry-equivalent points of p inside pts
---------------------------------------------------------------

countSymmetricMatches = (p, pts, eps) -> (
    eps2 := eps^2;
    u := coords p;

    -- precompute orbit of p
    O := symmetryOrbitCoords u;

    count := 0;

    scan(pts, q -> (
        v := coords q;
        matched := false;
        i := 0;
        while i < #O and not matched do (
            d2 := distance2CoordsBounded(v, O#i, eps2);
            if d2 < eps2 then matched = true;
            i = i + 1;
        );
        if matched then count = count + 1;
    ));

    count
);


---------------------------------------------------------------
-- Helpers: coordinates & complex checks
---------------------------------------------------------------

-- Accept either Points or raw coordinate lists
coords = p -> (
    if class p === Point then p#Coordinates else p
);

-- squared modulus of a (possibly complex) number
squareModulus = z -> (
    (realPart z)^2 + (imaginaryPart z)^2
);

-- check |z - conjugate(w)| < epsPair
isConjPairClose = (z, w, epsPair) -> (
    diff := z - conjugate w;
    squareModulus diff < epsPair^2
);

-- check imag(z) is small: "z is approximately real"
isApproximatelyReal = (z, epsReal) -> (
    abs imaginaryPart z < epsReal
);

---------------------------------------------------------------
-- Internal predicate: does ONE solution have conjugate symmetry?
-- v = (v1,...,v_n, conj(v_n),...,conj(v1))
-- If length is odd, middle entry must be ≈ real.
---------------------------------------------------------------

isConjugateSymmetricLocal = (p, epsPair, epsReal) -> (
    v := coords p;
    m := #v;
    if m == 0 then return false;

    if m % 2 == 0 then (
        -- even length: m = 2n
        n := m // 2;
        for i from 0 to n-1 do (
            if not isConjPairClose(v#i, v#(m - 1 - i), epsPair) then (
                return false;
            );
        );
        true
    )
    else (
        -- odd length: m = 2n+1
        n := (m - 1) // 2;
        mid := n;
        -- middle must be approximately real
        if not isApproximatelyReal(v#mid, epsReal) then return false;
        -- outer pairs must be conjugates
        for i from 0 to n-1 do (
            if not isConjPairClose(v#i, v#(m - 1 - i), epsPair) then (
                return false;
            );
        );
        true
    )
);

---------------------------------------------------------------
-- PUBLIC FUNCTION:
-- Count how many solutions in pts have that conjugate symmetry
---------------------------------------------------------------

countConjugateSymmetric = (pts, epsPair, epsReal) -> (
    count := 0;
    scan(pts, p -> (
        if isConjugateSymmetricLocal(p, epsPair, epsReal) then (
            count = count + 1;
        );
    ));
    count
);

---------------------------------------------------------------
-- Example usage (sketch)
---------------------------------------------------------------
-- sols = {...}        -- list of solutions, each either a Point or a list
-- epsPair = 1e-6;     -- tolerance for v_i ≈ conjugate(v_j)
-- epsReal = 1e-6;     -- tolerance for "middle entry is ≈ real"
--
-- nSym = countConjugateSymmetric(sols, epsPair, epsReal)
-- nSym

--Code for checking various aspects of V(I)
a=7

denseData = BlockPeriodicMatrix1DLap(a);
use denseData_1;
specm = map (denseData_1, denseData_1, {1,z + 2,1,q_1..q_a})
smat = specm denseData_0;
spol = det(smat);
use denseData_1;
varsss = new List from a:0;
specma = map (denseData_1, denseData_1, join({1,z,1},varsss))

DF2 = spol - specma spol
K = coefficients(DF2,Variables=>{z});
KL = entries K_1_0;
KLu = unique KL;
#KLu
KLu --these are our spectral invariants

--I = ideal(KLu)
--J = tangentCone(I)
--degree(J, Verbose => true) --gives mutliplicity at 0
--takes a while
--one can also use local rings to compute this. tangentCone method became very slow after n=6
--For n = 7 we relied on looking at the length of the quotient over the local ring at 0, i.e. the text book definition of local multiplicity 
-- as can be found in Using Algebraic Geometry by Cox, Little, O'Shea

NAGtrace 2;
CCR = CC[q_1..q_a] 
specCCR = map(CCR, denseData_1, {0,0,0,q_1..q_a})
F = apply(KLu, n-> specCCR n) -- we reuse the old system
use CCR
solns1 = solveSystem(F);


solns = time solveSystem(F, Software => BERTINI);
--BertiniDoes not handle multiplicity by default, but the number of solutions appears good

#solns


nonz = outsideRadius(solns, 0.00001)


#solns
#nonz

countConjugateSymmetric(nonz, 0.00001, 0.00001)

nonzsymsgone = pruneDihedral(nonz, 0.00001)
#nonzsymsgone

nearDs = nearDuplicateClustersNoDihedral(nonz, 0.000001)

sizeNearD = for i in nearDs list #i
#sizeNearD
biggerthan1 = flatten select(nearDs, x -> #x > 2)
singCheck = for i in biggerthan1 list nonz_i
tally sizeNearD


#nonzsymsgone --number of solutions up to dihedral symmetry


--next also account for conjugate and negation symmetries
nonzsymsgone2 = pruneSymmetric(nonz, 0.00001)
#nonzsymsgone2

nearDs = nearDuplicateClustersNoDihedral(nonz, 0.000001)

sizeNearD = for i in nearDs list #i
#sizeNearD
biggerthan1 = flatten select(nearDs, x -> #x > 2)
singCheck = for i in biggerthan1 list nonz_i
tally sizeNearD


#nonzsymsgone


--make a list of all distinct sols
distinctSols = for i in nearDs list nonz_i_0
#distinctSols
--now reduce via all symmetries
distinctSolsSym = pruneSymmetric(distinctSols, 0.00001)
#distinctSolsSym

pairings = for i in distinctSolsSym list countSymmetricMatches(i, distinctSols, 0.00001)
tally pairings
 
F1 = polySystem F
C = certifySolutions(F1,distinctSolsSym)
#C#"certifiedRegular"
peek C
#C#"certifiedSingular"
#C#"certifiedDistinct"

--if any nonCertified solutions exist, try to certify them by performing additional Newton's method steps
a = apply(C#"nonCertified", n-> newton(F1, n))


Csing = certifySolutions(F1,a)
peek Csing

--using newtons method to check solution near 0 is actually 0.
a1 = newton(F1, singCheck_4)
a2 = newton(F1, a1)
peek a2



#solns1
nonz1 = outsideRadius(solns1, 0.00001)
#solns1
#nonz1



--Code for checking various aspects of V(I')
--newPruneSymmetry since Dihedreal symmetry no longer makes sense here
---------------------------------------------------------------
-- 6. Full symmetry orbit: ± and conjugation + dihedral
---------------------------------------------------------------

-- Given coord list v, return {v, -v, conj(v), -conj(v)}
symmetryOrbitCoords2 = v -> (
    v = coords v;
    v1 := v;
    v2 := apply(v, z -> -z);
    v3 := apply(v, z -> conjugate z);
    v4 := apply(v, z -> - conjugate z);

    -- Flat list of the four variants:
    {v1, v2, v3, v4}
);


---------------------------------------------------------------
-- 7. Prune up to all symmetries (dihedral + ± + conjugate)
---------------------------------------------------------------
distance2CoordsBounded = (u, v, eps2) -> (
    u = coords u;
    v = coords v;
    n := #u;
    s := 0.;
    i := 0;
    while i < n and s <= eps2 do (
        d := u#i - v#i;
        s = s + squareModulus d;
        i = i + 1;
    );
    s
);
-- pts : list of Points or lists
pruneSymmetric2 = (pts, eps) -> (
    nPts := #pts;
    if nPts == 0 then return {};

    eps2 := eps^2;

    -- Precompute coords and these small orbits
    coordList    := new MutableList from apply(pts, p -> coords p);
    symOrbitList := new MutableList from apply(nPts, i -> symmetryOrbitCoords2(coordList#i));

    -- Are point i and j within eps up to ± / conjugation?
    isCloseSym = (i, j) -> (
        u := coordList#i;
        O := symOrbitList#j;
        m := #O;
        k := 0;
        while k < m do (
            d2 := distance2CoordsBounded(u, O#k, eps2);
            if d2 < eps2 then return true;
            k = k + 1;
        );
        false
    );

    -- Greedy reps by index
    repsIdx := {};
    for i from 0 to nPts-1 do (
        isNew := true;
        scan(repsIdx, r -> (
            if isCloseSym(i, r) then isNew = false;
        ));
        if isNew then repsIdx = append(repsIdx, i);
    );

    apply(repsIdx, i -> pts#i)
);



a=12

denseData = BlockPeriodicMatrix1DLap(a);
use denseData_1;
b = a//2
NAGtrace 2;
veee = new List from ((a % 2):0)
varss1 = new List from q_1 .. q_b
varss2 = reverse apply((new List from q_1 .. q_b), n -> -1*n)
varss = varss1 | veee | varss2
specm = map (denseData_1, denseData_1, {1,z + 2,1} | varss)
smat = specm denseData_0;
spol = det(smat);
use denseData_1;
varsss = new List from a:0;
specma = map (denseData_1, denseData_1, join({1,z,1},varsss))

DF2 = spol - specma spol
K = coefficients(DF2,Variables=>{z});
KL = entries K_1_0;
KLu = unique KL;
#KLu
KLu --these are our spectral invariants

--I = ideal(KLu)
--J = tangentCone(I)
--degree(J, Verbose => true) --gives mutliplicity at 0
--takes a while
b = a//2
NAGtrace 2;
QQR = QQ[q_1..q_b] 
veee = new List from ((a % 2):0)
varss1 = new List from q_1 .. q_b
varss2 = reverse apply((new List from q_1 .. q_b), n -> -1*n)
varss = varss1 | veee | varss2
specQQR = map(QQR, denseData_1, ({0,0,0} |varss))
Fpre = apply(KLu, n-> specQQR n) -- we reuse the old system

I = ideal(Fpre)
degree I
--J = tangentCone(I)
--degree J


CCR = CC[q_1..q_b] 


specCCR = map(CCR, QQR, (new List from q_1..q_b))
F = apply(Fpre, n-> specCCR n) -- we reuse the old system
use CCR

F = unique F
F = select(F, n -> n != 0)
time solns1 = solveSystem(F);


solns = time solveSystem(F, Software => BERTINI);
--BertiniDoes not handle multiplicity by default, but the number of solutions appears good

#solns


nonz = outsideRadius(solns, 0.00001)


#solns
#nonz

--next also account for conjugate and negation symmetries
nonzsymsgone2 = pruneSymmetric2(nonz, 0.00001)
#nonzsymsgone2


F1 = polySystem F
C = certifySolutions(F1,nonzsymsgone2);
peek C
#C#"certifiedRegular"
#C#"certifiedSingular"
#C#"certifiedDistinct"
#C#"nonCertified"

--if any nonCertified solutions exist, try to certify them by performing additional Newton's method steps
a = apply(C#"nonCertified", n-> newton(F1, n))
C = certifySolutions(F1,a)
#C#"certifiedRegular"
peek C
#C#"certifiedSingular"
#C#"certifiedDistinct"

a = apply(a, n-> newton(F1, n))
C = certifySolutions(F1,a)
#C#"certifiedRegular"
peek C
#C#"certifiedSingular"
#C#"certifiedDistinct"

b = apply(a, n-> newton(F1, n))
C = certifySolutions(F1,a)
#C#"certifiedRegular"
peek C
#C#"certifiedSingular"
#C#"certifiedDistinct"


pons = point (C#"certifiedSingular"_0)
#select(solns1, n -> n == pons) --check the degree of the solution, assuming homotopy continuation is counting with multiplicity; the multiplicity is technically uncertified.


#solns1



--Code for the tests done in Section 6


-- Floquet adjacency matrix for Z^2 / <(a,0),(b,c)>
-- Fundamental domain: (i,j) with i=1..a, j=1..c
-- Vertex order: id(i,j) = (i-1)*c + j
-- Phases:
--   crossing +(a,0)  -> x
--   crossing -(a,0)  -> xi
--   crossing +(b,c)  -> y
--   crossing -(b,c)  -> yi
-- Diagonal: v_i - z

floquetMatrix = (a,b,c) -> (
    n := a*c;

    -- base symbol for indexed variables v_1..v_n

    -- ring with quasimomenta and diagonal potentials
    R := QQ[x, xi, y, yi, z, v_1..v_n];

    -- helper for v_k (1-based)
    vvar = k -> v_k;

    -- index map (1-based (i,j) -> 0-based linear index)
    ide = (i,j) -> (i-1)*c + j - 1;

    -- make an n×n zero mutable matrix over R
    M := mutableMatrix(R, n, n);

    -- add a directed edge with phase
    addEdge = (i1,j1,i2,j2,phase) -> (
        u  := ide(i1,j1);
        vtx := ide(i2,j2);
        M_(u,vtx) = M_(u,vtx) + phase;
    );

    -- fill matrix
    for i from 1 to a do (
      for j from 1 to c do (
        u := ide(i,j);
        M_(u,u) = M_(u,u) + vvar(u+1) - z;

        -- RIGHT neighbor: (i+1, j)
        ii := i+1; ph := 1_R;
        if ii == a+1 then ( ii = 1;  ph = ph * xi );   -- crossed -(a,0)
        addEdge(i,j,ii,j,ph);

        -- LEFT neighbor: (i-1, j)
        ii = i-1; ph = 1_R;
        if ii == 0 then ( ii = a;  ph = ph * x );      -- crossed +(a,0)
        addEdge(i,j,ii,j,ph);

        -- UP neighbor: (i, j+1)
        ii = i; jj := j+1; ph = 1_R;
        if jj == c+1 then (
            -- crossed top: subtract (b,c)
            jj = 1; ii = i - b; ph = ph * yi;
            -- possible extra wrap in i
            if ii < 1 then ( ii = ii + a; ph = ph * x  );
            if ii > a then ( ii = ii - a; ph = ph * xi );
        );
        addEdge(i,j,ii,jj,ph);

        -- DOWN neighbor: (i, j-1)
        ii = i; jj = j-1; ph = 1_R;
        if jj == 0 then (
            -- crossed bottom: add (b,c)
            jj = c; ii = i + b; ph = ph * y;
            -- possible extra wrap in i
            if ii < 1 then ( ii = ii + a; ph = ph * x  );
            if ii > a then ( ii = ii - a; ph = ph * xi );
        );
        addEdge(i,j,ii,jj,ph);
      )
    );

    matrix M
);


a = 7
b = 2
c=  1 
M = floquetMatrix(a,b,c)
R = ring(M_{1,1})
use R
spol = det(M);
spol = spol % ideal(x*xi-1,y*yi-1)
n = a*c
varsss = new List from n:0;
specma = map (R, R, join({x,xi,y,yi,z},varsss))

DF2 = spol - specma spol
DF2 = DF2  % ideal(x*xi-1,y*yi-1)
K = coefficients(DF2,Variables=>{z,x,y,xi,yi});
KL = entries K_1_0;
KLu = unique KL;
#KLu
KLu  

I = ideal(KLu)
degree I


J = tangentCone I
degree J