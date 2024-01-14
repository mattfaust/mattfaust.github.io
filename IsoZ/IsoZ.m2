 clearAll

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

a=4

denseData = BlockPeriodicMatrix1DLap(a);
use denseData_1;
specm = map (denseData_1, denseData_1, {1,z + 2,1,q_1 .. q_(a)}) --Here we are adding 2 to make the spectral problem fit our original problem as 
-- in the code we are using the graph laplacian, but in the problem we add 2 to the eigenvalues to get the spectral problem.
--we also fix the quaismomentum to 1
smat = specm denseData_0; --densedata_0 in this case is the spectral problem matrix
spol = det(smat); --Here we take the determinant to get P_v
use denseData_1; 
varsss = new List from a:0;
specma = map (denseData_1, denseData_1, join({1,z,1},varsss)) --Here we are fixing the quasimomentum to 1 and the potential variable to 0

DF2 = spol - specma spol --Here we take the difference of P_v and P_0
K = coefficients(DF2,Variables=>{z}); 
KL = entries K_1_0;
KLu = unique KL; -- allows us to extract the coefficients of the polynomial in z, these are the F_i in the paper
#KLu
KLu

--now we have the system that we wish to solve, KLU =0 is F from the paper
CCR = CC[q_1..q_a] --our cofficients are just polynomial in the q_i i.e the potential v_i in the paper
specCCR = map(CCR, denseData_1, {0,0,0,q_1 .. q_a})
F = apply(KLu, n-> specCCR n) --this just places our polynomials in the correct ring with no superfluous variables
use CCR
time solns = solveSystem(F); --actually calculates the solutions
#solns
solns
--Notice that the general solutions we claim are in fact solutions for n=4
-- a=5:

a=5

denseData = BlockPeriodicMatrix1DLap(a);
use denseData_1;
specm = map (denseData_1, denseData_1, {1,z + 2,1,q_1 .. q_(a)})
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
KLu


CCR = CC[q_1..q_a] 
specCCR = map(CCR, denseData_1, {0,0,0,q_1 .. q_a})
F = apply(KLu, n-> specCCR n)
use CCR
time solns = solveSystem(F); 

-- a = 6:

a=6

denseData = BlockPeriodicMatrix1DLap(a);
use denseData_1;
specm = map (denseData_1, denseData_1, {1,z + 2,1,q_1 .. q_(a)})
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
KLu


CCR = CC[q_1..q_a] 
specCCR = map(CCR, denseData_1, {0,0,0,q_1 .. q_a})
F = apply(KLu, n-> specCCR n) -- we reuse the old system
use CCR
time solns = solveSystem(F);
#solns


-- a=7:

a=7

denseData = BlockPeriodicMatrix1DLap(a);
use denseData_1;
specm = map (denseData_1, denseData_1, {1,z + 2,1,q_1 .. q_(a)})
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
KLu


CCR = CC[q_1..q_a]
specCCR = map(CCR, denseData_1, {0,0,0,q_1 .. q_a})
F = apply(KLu, n-> specCCR n) 
use CCR
solns = time solveSystem(F);
#solns


-- a=8:
--Here we will start only checking for solutions of the form v_1, v_2, 0,...,0,v_3,v_4,0,...,0 
--this is because otherwise there are simply too many solutions to parse through
--it will also significantly reduce computation time
--one can also use this to study the KLu equations after specializing
a=8

denseData = BlockPeriodicMatrix1DLap(a);
use denseData_1;
specm = map (denseData_1, denseData_1, {1,z + 2,1,q_1 .. q_(a)})
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
KLu

CCR = CC[v_1..v_4]
--build the variable specialization list described before Theorem 4.1.
zlist = new List from ((a-4)//2):0;
varlist = flatten {{0,0,0,v_1,v_2},zlist,{v_3,v_4},zlist};

specCCR = map(CCR, denseData_1, varlist)
F = apply(KLu, n-> specCCR n) 
use CCR
solns = time solveSystem(F);
#solns



-- a=10:
a=10

denseData = BlockPeriodicMatrix1DLap(a);
use denseData_1;
specm = map (denseData_1, denseData_1, {1,z + 2,1,q_1 .. q_(a)})
smat = specm denseData_0;
spol = det(smat);
--time sparseDetList(smat ,ZZ);
use denseData_1;
varsss = new List from a:0;
specma = map (denseData_1, denseData_1, join({1,z,1},varsss))

DF2 = spol - specma spol
K = coefficients(DF2,Variables=>{z});
KL = entries K_1_0;
KLu = unique KL;
#KLu
KLu

CCR = CC[v_1..v_4]
--build the variable specialization list described before Theorem 4.1.
zlist = new List from ((a-4)//2):0;
varlist = flatten {{0,0,0,v_1,v_2},zlist,{v_3,v_4},zlist};

specCCR = map(CCR, denseData_1, varlist)
F = apply(KLu, n-> specCCR n) 
use CCR
solns = time solveSystem(F);
#solns

-- a=12:
a=12

denseData = BlockPeriodicMatrix1DLap(a);
use denseData_1;
specm = map (denseData_1, denseData_1, {1,z + 2,1,q_1 .. q_(a)})
smat = specm denseData_0;
spol = det(smat);
--time sparseDetList(smat ,ZZ);
use denseData_1;
varsss = new List from a:0;
specma = map (denseData_1, denseData_1, join({1,z,1},varsss))

DF2 = spol - specma spol
K = coefficients(DF2,Variables=>{z});
KL = entries K_1_0;
KLu = unique KL;
#KLu
KLu

CCR = CC[v_1..v_4]
--build the variable specialization list described before Theorem 4.1.
zlist = new List from ((a-4)//2):0;
varlist = flatten {{0,0,0,v_1,v_2},zlist,{v_3,v_4},zlist};

specCCR = map(CCR, denseData_1, varlist)
F = apply(KLu, n-> specCCR n) 
use CCR
solns = time solveSystem(F);
#solns
