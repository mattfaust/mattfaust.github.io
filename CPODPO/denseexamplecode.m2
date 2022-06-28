 
clearAll
load "necessaryfunctions.m2"


a =  {45, 439, 25, 13, 548, 35, 87, 257, 12, 637, 52, 543, 65,13,17} --densegraph let all edges be nonzero
R = QQ[x_1,x_2,z,y_1,y_2,zi, e_1 .. e_15]
Operator = matrix {{-x_1*e_1-y_1*e_1-x_2*e_5-y_2*e_5-x_1^2*e_9-y_1^2*e_9-z+2*e_1+e_2+e_3+2*e_5+e_6+e_7+2*e_9+e_10+e_11+e_13-e_14, -y_1*e_2-x_1*e_3-y_2*e_6-x_2*e_7-y_1^2*e_10-x_1^2*e_11-e_13}, {-x_1*e_2-y_1*e_3-x_2*e_6-y_2*e_7-x_1^2*e_10-y_1^2*e_11-e_13, -x_1*e_4-y_1*e_4-x_2*e_8-y_2*e_8-x_1^2*e_12-y_1^2*e_12-z+e_2+e_3+2*e_4+e_6+e_7+2*e_8+e_10+e_11+2*e_12+e_13-e_15}}; --operator with edge weights as variables
Ra = QQ[x_1,x_2,z,y_1,y_2,zi]
specmap = map(Ra,R, join({x_1,x_2,z,y_1,y_2,zi}, a)) --specialize the edges
DF = det(specmap Operator),Strategy => Cofactor; --get determinant i.e characteristic polynomial
use Ra;
I = ideal(x_1*y_1 -1, x_2*y_2 -1, z*zi -1);
DFr = x_1^4 * x_2^2 * DF % I; --make our characteristic polynomial a polynomial with no inverse variables
CP = {DFr}; --define the critical point equations
for i from 1 to 2 do (
    	 CP = append(CP,(diff(x_i, CP_0)));
    ); 


Ra2 = QQ[x_1,x_2,z] --ring so we can lower dimension and check the volume
volmap = map(Ra2,Ra,{x_1,x_2,z,0,0,0}) --specialize the edges

CPsP = apply( CP , n -> exponents(volmap n ));
CPsN = apply(CPsP, n -> convexHull (transpose matrix n)); --list of polytopes


vv = volume CPsN_0 -- volume is 32/3. Thus mixed volume is 64
-- one could check this by checking the system CPsN with mixedVolume
--I do not recommend this with macaulay2 unless you write your own mixed volume
--function as the built in function is slow (unsure if functional).

--Here is a mixed volume check wrote using the most  naive method of direct 
--computation
mv = myMixedVolume CPsN
--64 as expected


--next we get a fan so we can check all divisors at infinity for solutions
CFan = normalFan CPsN_0;
conelistCP = coneList(CFan);
sysCP = apply(CP, n -> apply(conelistCP, m-> getFaceFunc(m,n,0))); --the 1 is just to let the function know how many variables are not inverse variables, see function.m2 description for more info
--this gives us a collection of all facial systems


--we extract some information about these systems:
     theideals = {};--will store the ideal of the system of equations for the various faces   
     dims = {};--will store the dimensions of these ideals
     degs = {};--will store the degrees of these ideals
     for i from 0 to #conelistCP - 1 do (
	 thelist = {};
	 for j from 0 to 2 do (
	     thelist = append(thelist, (sysCP_j)_i);
	     );
	 theideals = append(theideals,(ideal thelist)+(I));
	 dims = append(dims, dim theideals_i);
	 degs = append(degs, degree theideals_i);
	 );
     dims
     degs --we get lists of -1 and 0 indicating that there are no solutions
     --for any divisor at infinity.
--this gives us the dimension and degs, notice the base is dimension 1, this is because lambda is not present, but lambda is fixed to 0, thus this is really a 0 dimensional ideal of solutions on the base,
--Everywhere except the base, we see the dimension is -1 and the degree is 0, i.e there are no solutions on any facet.

-- change to the space the blochvariety exists in (the torus union the base)

use Ra;
Raz = QQ[x_1,x_2,z,y_1,y_2]
use Raz
Iz = ideal(x_1*y_1-1, x_2*y_2 -1) 
specmap2 = map(Raz, Ra, {x_1,x_2,z,y_1,y_2,0});
CPT = apply(CP, n -> specmap2 n);
CPTT = apply(CPT, n -> n % Iz)
J = ideal(CPTT) + Iz
K = gb J;
gK = gens K;
M = coker gK;
codim M
dim M
degree M
--for this example, the dimension is 0 and the degree is 64, as expected.


--next we want to check and make sure all these solutions are isolated.
use Raz
J0 = eliminate(J,{x_1,y_1,x_2,y_2}) -- obtain possible eigen values of the critical points
facty = (factor J0_0)
--We get a degree 36 polynomial with potential eigenvalues
F = ZZ/10667[x_1,x_2,z,y_1,y_2]
specmap3 = map(F, Raz, {x_1,x_2,z,y_1,y_2});
numsols = 0;
nums = {};
for i from 0 to #facty-2 do (
 chek = specmap3 J +  specmap3 ideal(facty#i#0);
 numsols = numsols + degree chek;    
 nums = append(nums,degree chek);
    );
numsols
nums
--notice numsols counts 8 solutions for the first 4 factors, we are then left with a degree 28 irreducible term. 
-- We expect 56 more solutions, we will look for them in a finite field, this particular prime was chosen as it yields a convient factorization (found using commented out code below)
--We check this remaining polynomial of eigenvalues to find the remaining distinct solutions

--Here we factor the fifth irreducible term further in positive characteristic  
facts = (factor J0_0)#4#0
F = ZZ/10667[x_1,x_2,z,y_1,y_2] --prime chosen since reduces degree nicely
specmap3 = map(F, Raz, {x_1,x_2,z,y_1,y_2});
factss = factor (specmap3 facts);

--adds the irreducible factor to look at the ideal at the particular eigen values identified by each irreducible term, we then check the degree of these 0 dimensional ideals
degys = {}
for i from 0 to #factss-1 do (
    s = factss#i#0;
    chek = specmap3 J + ideal(s);
    degy = degree chek;
    degys = append(degys, degy);
	    );
degys --we see that we expect 56 solutions total, however we need to check to make sure that these 56 solutions correspond to distinct points

--to do this we will again look at the ideal at each set of eigenvalues specified by each irreducible factor found
-- we then will eliminate the remaining variables to see how many unique x_1 values exist, if there are 56 unique x_1 values we know
--that  we have 56 distinct solutions
for i from 0 to #factss-1 do (
 chek = specmap3 J + ideal(factss#i#0);
 echek = eliminate(chek,{z});
 echek = eliminate(echek,{x_1,y_1,y_2});
 numsols = numsols + degree echek;    
    );
numsols
--We see we have added 56 distinct solutions to our previous count of 8, thus we see that we have found our remaining 56 solutions, and they are distinct
--Since we have 64 isolated critical points, it cannot be the case that any degenerate solutions exist.

--Indeed we can compare this to checking for degenerate critical points directly by adding the hessian to our set of critical point equations
use Raz
L = Hessian2(CPT_0,2);
P = ideal(gK);
L = L % P;
J2 = ideal(L) + P;
K2 = gb J2;
gK2 = gens K2;
N = coker gK2;
codim N
dim N
degree N
--for the example, the dimension is -1 and the degree is 0, that is there are no degenerate critical points.
--Thus confirming what we already previous demonstated via finding all isolated critical points.
--We should remark however, that if critical points are not all isolated, this does not imply that there exist degenerate critical points
-- these could simply be singular points of the bloch variety (i.e where the partial derivative with respect to z (the eigenvalue) vanishes.
