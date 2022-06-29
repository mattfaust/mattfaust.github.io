
clearAll
load "necessaryfunctions.m2"


a =  {0, 439, 0, 0, 0, 365, 827, 0, 0, 0, 252, 0, 0, 0, 632, 423, 0, 0, 0, 0, 41, 0, 0, 0, 0, 179, 0, 928, 0, 108,13,24,12} --non pyramid triangular face example
R = QQ[x_1,x_2,x_3,z,y_1,y_2,y_3,zi, e_1 .. e_33]
Operator = matrix {{-x_1*e_1-y_1*e_1-x_2*e_10-y_2*e_10-x_3*e_19-y_3*e_19-z+2*e_1+e_2+e_3+e
       _4+e_7+2*e_10+e_11+e_12+e_13+e_16+2*e_19+e_20+e_21+e_22+e_25+e_28+e_29-e
       _31, -y_1*e_2-x_1*e_4-y_2*e_11-x_2*e_13-y_3*e_20-x_3*e_22-e_28,
       -y_1*e_3-x_1*e_7-y_2*e_12-x_2*e_16-y_3*e_21-x_3*e_25-e_29},
       {-x_1*e_2-y_1*e_4-x_2*e_11-y_2*e_13-x_3*e_20-y_3*e_22-e_28,
       -x_1*e_5-y_1*e_5-x_2*e_14-y_2*e_14-x_3*e_23-y_3*e_23-z+e_2+e_4+2*e_5+e_6
       +e_8+e_11+e_13+2*e_14+e_15+e_17+e_20+e_22+2*e_23+e_24+e_26+e_28+e_30-e_
       32, -y_1*e_6-x_1*e_8-y_2*e_15-x_2*e_17-y_3*e_24-x_3*e_26-e_30},
       {-x_1*e_3-y_1*e_7-x_2*e_12-y_2*e_16-x_3*e_21-y_3*e_25-e_29,
       -x_1*e_6-y_1*e_8-x_2*e_15-y_2*e_17-x_3*e_24-y_3*e_26-e_30,
       -x_1*e_9-y_1*e_9-x_2*e_18-y_2*e_18-x_3*e_27-y_3*e_27-z+e_3+e_6+e_7+e_8+2
       *e_9+e_12+e_15+e_16+e_17+2*e_18+e_21+e_24+e_25+e_26+2*e_27+e_29+e_30-e_
       33}}
Ra = QQ[x_1,x_2,z,y_1,y_2,zi]
specmap = map(Ra,R, join({x_1,x_2,x_1*x_2,z,y_1,y_2,y_1*y_2,zi}, a)) --specialize the edges
DF = det(specmap Operator),Strategy => Cofactor; --get determinant i.e characteristic polynomial
use Ra;
I = ideal(x_1*y_1 -1, x_2*y_2 -1, z*zi -1);
DFr = x_1^3 * x_2^3 * DF % I; --make our characteristic polynomial a polynomial with no inverse variables
CP = {DFr}; --define the critical point equations
for i from 1 to 2 do (
    	 CP = append(CP,(diff(x_i, CP_0)));
    ); 


Ra2 = QQ[x_1,x_2,z] --ring so we can lower dimension and check the volume
volmap = map(Ra2,Ra,{x_1,x_2,z,0,0,0}) --specialize the edges

CPsP = apply( CP , n -> exponents(volmap n ));
CPsN = apply(CPsP, n -> convexHull (transpose matrix n)); --list of polytopes

CP_0
vv = volume CPsN_0 -- volume is 70/3. Thus mixed volume is 140

--Here is a mixed volume check wrote using the most  naive method of direct 
--computation
mv = myMixedVolume CPsN
--140 as expected


--next we get a fan so we can check all divisors at infinity for solutions
CFan = normalFan CPsN_0;
conelistCP = coneList(CFan);
sysCP = apply(CP, n -> apply(conelistCP, m-> getFaceFunc(m,n,0))); --the 0 is just to let the function know how many variables are not inverse variables, see function.m2 description for more info
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
--for this example, the dimension is 0 and the degree is 140, as expected.


--next we want to check and make sure all these solutions are isolated.
use Raz
F = ZZ/10903[x_1,x_2,z,y_1,y_2]
specmap3 = map(F, Raz, {x_1,x_2,z,y_1,y_2});
J0 = eliminate(specmap3 J,{x_1,y_1,x_2,y_2}) -- obtain possible eigen values of the critical points
facty = (factor J0_0)
numsols = 0;
nums = {};
for i from 0 to #facty-1 do (
 chek = specmap3 J +  ideal(facty#i#0);
 numsols = numsols + degree chek;    
 nums = append(nums,degree chek);
    );
numsols
nums
--notice numsols counts 12 eigenvalues with a single critcal point, we are then left several factors that have twice as many critical points as eigen values. 
-- We expect 128 more solutions, we will look for them in a finite field, this particular prime was chosen as it yields a convient factorization (found using commented out code below)
--We check this remaining polynomial of eigenvalues to find the remaining distinct solutions

factss = facty;
degys = {}
for i from 0 to #factss-1 do ( --this gives us the degree of solutions with respect to each
    s = factss#i#0; -- irreducible term
    chek = specmap3 J + ideal(s);
    degy = degree chek;
    degys = append(degys, degy);
    print i;
	    );
--get the degrees of the polynomials
pdegs = {}
for i from 0 to #factss-1 do (
    s = factss#i#0;
    dee=  degree ideal(s);
    pdegs = append(pdegs, dee);
    print i;
	    );
pdegs
degys
sum degys --we see that we expect 140 solutions total, however we need to check to make sure that these 140 solutions correspond to distinct points
--to do this we will again look at the ideal at each set of eigenvalues specified by each irreducible factor found
-- we then will eliminate the remaining variables to see how many unique x_1 values exist

--the degree of these fermi varities (or finite union of fermi varties are given by the list
--{1, 1, 1, 1, 1, 1, 1, 2, 2, 3, 8, 14, 16, 28, 30, 30}
--degree of the polynomials are 
-- {1, 1, 1, 1, 1, 1, 1, 1, 2, 3, 4, 7, 8, 14, 15, 15}, we see either there are twice as many solutions as eigenvalues
-- or there are exactly as many eigen values as solutions
--We need only check when there are more solutions than the degree of the polynomial to make sure none are the same solution
--if we find as many x_1 values as the degree of the varity for that particular irreducible polynomial (i.e finite subset of eigenvalues)
-- then we know that they must all correspond to distinct solutions.

chek = specmap3 J + ideal(factss#1#0);
 echek = eliminate(chek,{z});
 echek = eliminate(echek,{x_1,y_1,y_2});
degree echek

numsols = 0;
sols = {}
for i from 0 to #factss-1 do (
 chek = specmap3 J + ideal(factss#i#0);
 echek = eliminate(chek,{z});
 echek = eliminate(echek,{x_1,y_1,y_2});
 degee = degree echek;
 numsols = numsols + degee;
 sols = append(sols, degee); 
 print i;   
    );
numsols
sols
--sols = {1, 1, 1, 1, 1, 1, 1, 2, 1, 1, 8, 14, 16, 28, 30, 30}
--We see that there are 2 solutions for each eigenvalue that we needed, thus we can conclude that we counted
--Although solutions doesn't sum to 140 this is fine, as we only needed for certain eigen values this is the case
-- notice at some indices the number of x_1 is 1, but the degree of the variety is 2 or 3
-- If you look this is because this value corresponds to multiple eigen values (inparticular 2 z share the same x_1 for two irreducibles).
--
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
