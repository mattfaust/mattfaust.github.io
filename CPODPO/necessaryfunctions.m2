
-- installPackage "Polyhedra";
needsPackage "Polyhedra"
needsPackage "NumericalAlgebraicGeometry"

-- In here are helper functions to accompany code for discrete periodic operators



--literally just map
Specialize = (P,Q,M) -> map(P,Q,M)

-- minkowskiSum that takes a list of polytopes and recurses 
--appearently can just use fold(minkowskiSum, List) aswell.
myMinkowskiSum = method(TypicalValue => Thing)
myMinkowskiSumHelper = method(TypicalValue => Sequence)
 
myMinkowskiSum (List) := (Thing) => (polyList) -> (
    return (myMinkowskiSumHelper(polyList_0, drop(polyList,1)))_0
)
myMinkowskiSumHelper (Thing, List) := (Thing, List) => (curPoly, polyList) -> (
    if (polyList === {}) then return (curPoly,{});
    if (polyList =!= {}) then return myMinkowskiSumHelper (minkowskiSum (curPoly, polyList_0), drop (polyList,1));
    ) 

--myMixedVolume will take a list of polytope
myMixedVolume  = method(TypicalValue => QQ) --function to call
myMixedVolumeRec = method(TypicalValue => Sequence) --recursive helper function
myMixedVolume (List) := QQ => (initList) -> (
    	tracklist = {};
	for i from 1 to #initList do(
	    tracklist = append(tracklist, i);
	    );
    	return (myMixedVolumeRec (initList, { }, tracklist))#0
    )
myMixedVolumeRec (List ,List, List) := (QQ, List)  => (polyList,accountedList, trackList) -> (--accountedList being used as a lazy redudancy reduction, storage is cheap
    local mvolume; local mixedpoly; local couple; local curpoly; local curtrack;
    	if (any(accountedList, n-> n == trackList)) then return (0, accountedList);
	accountedList = append(accountedList, trackList);
	if (#polyList === 1) then (
	    if (isFullDimensional polyList_0 == false) then return (0, accountedList);
	     return (volume polyList_0, accountedList);		 
		 );
	mvolume = 0;
--	mixedpoly = myMinkowskiSum(polyList);
        mixedpoly = fold(minkowskiSum, polyList);
	if (isFullDimensional mixedpoly == false) then return (0, accountedList);
	 mvolume = volume mixedpoly;
	for i from 0 to #polyList-1 do(
	    curpoly = drop(polyList, {i,i});
	    curtrack = drop(trackList, {i,i});
	    couple = myMixedVolumeRec(curpoly, accountedList, curtrack);
	    mvolume = mvolume - couple#0;
--	   <<couple#0;-- was just here for debugging
--	   <<curtrack;
	    accountedList = couple#1;
	    );
	return (mvolume, accountedList)	
    )

--coneList will take a fan and return the list of matrices defining our cones in each dimension 1 to ambDim(curFan)
coneList = method(TypicalValue => List)
coneList (Thing) := List => (curFan) -> (
    local cList; local adim; local curCone; local curConeList;local curIndex; local raytrix;
    raytrix = rays curFan;
    cList = { };
    adim = ambDim curFan;
    for i from 1 to adim do (	
	curConeList = cones(i, curFan);
      	for j from 0 to #curConeList-1 do ( --honestly a super lazy design that no for loop without a do is implemented....
	    	curIndex = (curConeList_j)_0;
	    	curCone =raytrix_{curIndex};
	    for k from 1 to #curConeList_j-1 do (
		if (#curConeList_j <= 1) then break;
--		<< curCone; lines for debugging
		curIndex = (curConeList_j)_k;
		curCone = curCone | raytrix_{curIndex};
--		<< curIndex;
--		<< curCone;
		);
	    	cList = append(cList, curCone);
	    );
	);
        return cList
     )
 
 --getFaceFunc will take a cone and a polynomial it will return the subpolynomial corresponding to the facet the cone is normal to
--will use exponents to decide which indices are chosed
--then will iterate through a list of terms to create the facial polynomial by successively added the indices chosen
--formate the polynomial so that variables with inverses do not appear with their inverses
--Assumes ring to be of the form R[x_1,...x_n,xi_1,...,xi_n,z_1,...z_m] where xi_j is inverse to i_j and z_i are non invertable vars.
--pass to getFaceFunc(thing, thing) if ring is a laurent polynomial (that is m = 0
--pass to getFaceFunc(thing, thing, ZZ) if ring has non invertable variables, this takes an extra variable m to account for cutting
getFaceFunc = method(TypicalValue => Thing)
getFaceFunc (Thing, Thing) := Thing => (inCone, initf) -> (
    	    return getFaceFunc(inCone, initf, 0)
    );

getFaceFunc (Thing, RingElement, ZZ) := RingElement => (inCone, initf, m) -> (
    local curmin; local minList; local curPoly; local expsf; local termsf; local vartocut; local numinvars;
    numinvars = numRows(inCone) - m;
    vartocut = { };
    for i from 1 to numinvars do (
	    vartocut= append(vartocut, 2*numinvars - i);
	);
  --  << numinvars;
    exps = pruneList(exponents initf, vartocut);
    termsf = terms initf;  
    minList = { };
    curPoly = initf-initf;
    for i from 0 to #exps-1 do (
	if (i == 0) then (
	    checkmin = getIProd(inCone, exps_i);--helper function
	    minList = append(minList, checkmin);
     	    curmin = checkmin;
	    continue;
	    );
	checkmin = getIProd(inCone, exps_i);
	curmin = min {curmin, checkmin};
	minList = append(minList, checkmin);
	);
    for i from 0 to #exps-1 do (
	    if minList_i == curmin then curPoly = curPoly + termsf_i;
	);
    return curPoly
     )
 --getIProd takes a cone/matrix and a vector and computes sum of inner product of the transpose of each column and the vector 
 --helper function to getFaceFunc
 getIProd = method(TypicalValue => QQ)
 getIProd (Matrix, Thing) := QQ => (inCone, expvec) -> (
     local cumsum; local colList;
     cumsum = 0;
     for i from 0 to numColumns(inCone)-1 do(
	 cumsum = cumsum + vecIProd((entries transpose inCone_{i})_0,expvec);
	 );
     return cumsum
     )
 --helper to getIProd, just yields the inner product. takes two lists and computes inner product
 vecIProd = method(TypicalValue => QQ)
 vecIProd (List, List) := QQ => (inCone, expvec) -> (
     local cumsum;
     cumsum = 0;
     if (#inCone =!= #expvec) then (
	 << "Vectors not of equal length, see vecIProd code";
	 return 0;
	 );
     for i from 0 to #inCone-1 do(
	 cumsum = cumsum + (inCone_i * expvec_i);
	 );
     return cumsum
     )

Hessian2 = method()
Hessian2 (Thing, ZZ) := (func, actions) -> (
	rows = new List;
	for i from 1 to actions do (
		row = new List;
		for j from 1 to actions do (
			row = append(row, diff(x_j, diff(x_i, func)));
		);
		rows = append(rows, row);
	);
	return determinant(matrix(rows));)
