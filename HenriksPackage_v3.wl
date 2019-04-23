(* ::Package:: *)

(* ::Section:: *)
(*Packages*)


$HarmonicSums2Path="C:\\Users\\zalat\\OneDrive\\Dokumenter\\Fysik & Matematik\\Master's Thesis\\Mathematica Packages\\HarmonicSums";
Get[ToFileName[{$HarmonicSums2Path},"HarmonicSums2.m"]];


(* ::Section:: *)
(*Basics*)


Clear[minMax]

minMax[index__List] := {index}[[All,2;;3]]


Clear[indexQ]

indexQ[x_,index__List] := FreeQ[{x},Alternatives@@({index}[[All, 1]])]


Clear[prodToList]

prodToList[func_] := If[Head[func] === Times, Replace[func, Times -> List, {1}, Heads -> True], List@func]


Clear[minGrMax]

(* min \[GreaterEqual] max + 2 *)

minGrMax[func_,indexList__] := Module[{newList,grQ,grPos},
newList[list_] := { list [[1]], list [[3]] + 1, list [[2]] - 1 };
grQ[min_,max_] := Refine[min >= max+2]; 
grPos = Position[grQ @@@ minMax[indexList], True];

Power[-1,Length@grPos] sum[func, ##] &@@ MapAt[newList,{indexList},grPos] ]


Clear[minEqMax]

(* min \[Equal] max *)

minEqMax[func_,indexList__] := Module[{inds,min,TrueFalse,eqPos,replaceInds,i},
{inds, min} = { {indexList}[[All,1]], {indexList}[[All,2]] };
TrueFalse = SameQ @@@ minMax[indexList];
eqPos = Position[TrueFalse, True];
replaceInds = Table[ Part[inds,Flatten@eqPos][[i]] -> Part[min,Flatten@eqPos][[i]], {i,1,Length@eqPos}];

	Which[
		Length@{indexList} == 1, func /. replaceInds,
		FreeQ[TrueFalse,False] == False, (sum[func, ##] &@@ Delete[{indexList}, eqPos]) /. replaceInds,
		FreeQ[TrueFalse,False] == True, func /. replaceInds
		]
]


Clear[sumToSum]

(* NumericQ[min,max] = True *)

sumToSum[func_,indexList__] := Module[{minMaxNumericQ,numericPos,indexQ,SumList,sumList,varList,SumIndexQ,SumVarPos,SumVar,sumVar},

minMaxNumericQ[min_,max_] := NumericQ[min] && NumericQ[max];
numericPos = Position[minMaxNumericQ @@@ minMax[indexList], True];

SumList = Part[{indexList},Flatten@numericPos];
sumList = Delete[{indexList},numericPos];

(* Is x a function of y? E.g indexQ[a^b, b] = True *)
indexQ[x_,y_] := ! FreeQ[x, y];

(* Is x a function of any of the indices in SumList? *)
SumIndexQ[x_] := Or @@ ( indexQ[x,##] &/@ SumList[[All,1]] );

varList = prodToList[func];
SumVarPos = Position[SumIndexQ /@ varList, True];

SumVar = Times @@ Part[varList, Flatten@SumVarPos];
sumVar = Times @@ Delete[varList, SumVarPos];

If[Length@{indexList} == 1,
	Sum[func,indexList],
	Sum[  (sum[SumVar sumVar, ##] &@@  sumList) , ##] &@@ SumList]
	
]


Clear[sum]

(* Do also e.g Sum[i,{i,k+1,k+2] = 2k+3 *)

sum[x_ + y_,index__List] := sum[x,index] + sum[y,index]
sum[(x_ + y_) * z_,index__List] := sum[x * z,index] + sum[y * z,index]
sum[x_ * y_,index__List] :=x * sum[y,index] /; indexQ[x,index]
sum[x_^(y_ + z_) * w_,index__List] := x^y * sum[x^z * w,index] /; indexQ[y,index]
sum[x_^(y_ - z_) * w_,index__List] := x^y * sum[x^-z * w,index] /; indexQ[y,index]
sum[0,index__List] := 0
sum[x_,index__List] := 0 /; Module[{eqPlus1}, eqPlus1[min_,max_] := TrueQ[min == max+1]; AnyTrue[eqPlus1 @@@ minMax[index], TrueQ]]
sum[x_,index__List] := minEqMax[x,index] /; AnyTrue[SameQ @@@ minMax[index], TrueQ]
sum[x_,index__List] := minGrMax[x,index] /; Module[{grQ}, grQ[min_,max_] := Refine[min >= max+2]; AnyTrue[grQ @@@ minMax[index], TrueQ]]
sum[x_,index__List] := sumToSum[x,index] /; Module[{minMaxNum}, minMaxNum[min_,max_] := NumericQ[min] && NumericQ[max]; AnyTrue[minMaxNum @@@ minMax[index], TrueQ]]


Clear[EZ]

EZ[Depth_,n_] := Module[{Ones}, Ones[i_] := If[i==0,{}, ConstantArray[1,i]]; Z[##,n]&@@Ones[Depth] /. Z[m_] :> 1]


Clear[mIndex]

mIndex[j_,k_] := Block[{m}, Join[ {{m[1], 1, k - (j - 1)}}, Table[{m[i], m[i-1] + 1, k - (j - i)}, {i,2,j}] ]];


Clear[f]
(* For \vec{x}=1, write xlist={} *)

f[j_,k_,n_,xlist__] :=
Which[Not[NumericQ[j]], HoldForm[f[j,k,n,xlist]], j==0, 1, NumericQ[j],
	If[(Length[xlist]!=j) && (Length[xlist]!=0), Print["variable list has wrong size"],
		Block[{m,indexlist,product}, 
			indexlist = mIndex[j,k]; 
			product = If[Length[xlist] == 0, Product[1/(m[i]+n),{i,1,j}], Product[xlist[[i]]^m[i]/(m[i]+n),{i,1,j}]];
			If[NumericQ[k], Sum[product,##] &@@ indexlist, sum[product,##] &@@ indexlist]
		]
	]
]


Clear[Sync]

Sync[i_,k_,n_] := EZ[i,n] + Sum[ EZ[i-j,n] f[j,k,n,{}],{j,1,i} ]


(* ::Section:: *)
(*Convert sums to Z, Li and HPL*)


Clear[Li, HPL]

Li[{},{}] := 1
Li[{m_?NumberQ},{x_}] := PolyLog[m,x] /; Refine[m>0];

HPL[{},x_] := 1
HPL[{m_?NumericQ},x_] := -Log[1-x]/m /; Refine[m>0];


Clear[sumReduce]

sumReduce = {
x_^-p_ :> (1/x)^p, 
sum[term_*Z[m__,{x__},i_],{i_,1,n_}] :> sum[term*Z[m,{x},i-1],{i,1,n}] + If[Length@{x} !=  1, sum[term*{x}[[1]]^i/\!\(\*SuperscriptBox[\(i\), \({m}[\([1]\)]\)]\)*(Z[##,Delete[{x},1],i-1] &@@ Delete[{m},1]),{i,1,n}], sum[term*{x}[[1]]^i/\!\(\*SuperscriptBox[\(i\), \({m}[\([1]\)]\)]\),{i,1,n}]],  
sum[term_*Z[m__,i_],{i_,1,n_}] :> sum[term*Z[m,i-1],{i,1,n}] + If[Length@{m} != 1, sum[term*1/\!\(\*SuperscriptBox[\(i\), \({m}[\([1]\)]\)]\)*(Z[##,i-1] &@@ Delete[{m},1]),{i,1,n}], sum[term*1/\!\(\*SuperscriptBox[\(i\), \({m}[\([1]\)]\)]\),{i,1,n}]],
sum[x_^n_/(n_ + k_),{n_,1,\[Infinity]}] :> -Log[1-x]/x^k - Z[1,{x},k]/x^k,
sum[term_*Z[i_-1],{i_,1,n_}] :> sum[term,{i,1,n}],
sum[x1_^i_ Power[i_,m1_],{i_,1,n_}] :> Z[-m1,{x1},n],
sum[x1_^i_ Power[i_,m1_] Z[m__,{x__},i_-1],{i_,1,n_}] :> (Z[##,Join[{x1},{x}],n] &@@ Join[{-m1},{m}]),
sum[x1_^i_ Power[i_,m1_] Z[m__,i_-1],{i_,1,n_}] :> (Z[##,Join[{x1},ConstantArray[1,Length@{m}]],n] &@@ Join[{-m1},{m}]),
sum[Power[i_,m1_] Z[m__,{x__},i_-1],{i_,1,n_}] :> (Z[##,Join[{1},{x}],n] &@@ Join[{-m1},{m}]),
sum[Power[i_,m1_],{i_,1,n_}] :> Z[-m1,{1},n],
sum[Power[i_,m1_] Z[m__,i_-1],{i_,1,n_}] :> (Z[##,n] &@@ Join[{-m1},{m}]),
Z[m__,{x__},\[Infinity]] :> If[DeleteDuplicates@{x}[[2;;All]] == {1}, HPL[{m},{x}[[1]]], Li[{m},{x}]],
PolyGamma[0,k_] :> -EulerGamma + Z[1,k-1],
sum[x_^m_/(-1-k_+m_),{m_,1,k_}] :> -x^(1+k) Z[1,{1/x},k],
sum[1/(-1-k_+m_),{m_,1,k_}] :> - Z[1,k],
sum[1/(m_-k_),{m_,1,k_+K_}] /; Negative@K :> -Z[1,k-1] + Z[1,Abs@K-1],
sum[x_^m_/(m_-k_),{m_,1,k_+K_}] /; Negative@K :> -x^k Z[1,{1/x},k-1] +x^k Z[1,{1/x},Abs@K-1]
};


Clear[fjk]

fjk[Loop_] := Module[{fjk1,fjk2},
fjk1 = Table[sum[Product[1/(1+k-m[i]),{i,1,j}],##] &@@ mIndex[j,k] :> Z[##,k] &@@ ConstantArray[1,j],{j,1,Loop}]; 
fjk2 = Module[{temp}, temp[l_,j_] := sum[ Power[x_, m[l]] Product[1/(1+k-m[i]),{i,1,j}],##] &@@ mIndex[j,k] :> x^(k+1) Z[##, Insert[ConstantArray[1,j-1], 1/x, l], k] &@@ ConstantArray[1,j];
Table[Table[temp[l,j],{l,1,j}],{j,1,Loop}]];

Flatten@{fjk1,fjk2}]


Clear[factorMinus]

factorMinus = sum[x_,y__] :> sum[Factor[x],y];


(* ::Section:: *)
(*Pentaladder Paper*)


Clear[xyz]

xyz[u_,v_,w_] := Module[{\[CapitalDelta],x,y,z},
\[CapitalDelta] = (1 - u - v - w)^2 - 4u*v*w;
{x = 1 + (1 - u - v - w + Sqrt[ \[CapitalDelta] ])/(2u*v), y = 1 + (1 - u - v - w - Sqrt[ \[CapitalDelta] ])/(2u*v), z = (u(1 - v))/(v(1 - u))}
];


Clear[F0]

F0[L_,x_] := Module[{coeff}, coeff[n_] := - (((2^n-2) \[Pi]^n BernoulliB[n])/n!); Sum[ coeff[2L-2n] HPL[{##},x]&@@ConstantArray[2,n],{n,0,L} ] ]


Clear[Fk]

(* G := (-1)*g^2 is the copupling *)
(* First term = Sum[\[Epsilon][k]^i ez[i,k], {i,0,L}] *)

Fk[L_,x_,k_] := Block[{\[Epsilon],G,FixingIndices,n,m}, 
\[Epsilon][k] := (k*Sqrt[1 + (4*G)/k^2] - k)/2; FixingIndices = {n+m[i_] :> n+m[i]-1, Z[m__,n] :> Z[m,n-1]};
(SeriesCoefficient[(\[Pi]*\[Epsilon][k])/Sin[\[Pi]*\[Epsilon][k]] (- G * sum[x^n/(n(n+k)) * Sum[(-1)^i \[Epsilon][k]^(i+j) (EZ[i,n] Sync[j,k,n] //LinearExpand) ,{i,0,L},{j,0,L}], {n,1,\[Infinity]}]), {G,0,L}] //Expand) /. FixingIndices ];


(* ::Section:: *)
(*Japanese Algorithm*)


Clear[regDiv]

(* 
- Does it handle m[i] - m[j] = 0 correctly? (1-m[1])(m[1]-m[2]) \[Rule] (1+\[Delta]+m[1])(\[Delta]+m[1]-m[2]), even though m[1] \[NotEqual] m[2].
- Problem with symbolic domains \[NotEqual] m[i],k though. Idea: func which transforms any summation variable to m[i].
- Dodgy parts: m[i_] \[RuleDelayed]  i and k \[RuleDelayed] len 
*)

regDiv = sum[func_,index__List] :> Block[{m,k,factors,len,indices,range,,sol,divPos,regDenom},
factors = Lr[func];
len = Length@factors;
indices = {index}[[All,1]];
range = {index}[[All,2;;3]] /. m[i_] :>  i /. k :> len;
sol = Flatten@Table[Solve[ factors[[i]] == 0, indices[[i]] ],{i,1,len}] /. k :> len /. Rule[a_,b_] :> b;
divPos = Table[IntervalMemberQ[Interval[ range[[i]] ], sol[[i]] ], {i,1,len}];
regDenom = Times @@ factors /. m[i_] :> m[i] + c[i]\[Delta] * If[divPos[[i]] == True, 1, 0];

sum[Numerator@func/regDenom,index]];


Clear[factorConstant]

factorConstant[sumexpr__] := Which[
Head[sumexpr] === Plus, List @@ sumexpr /. (const_:1)*sum[X__] :> {const, sum[X]} ,
Head[sumexpr] === sum, {1,sumexpr},
Head[sumexpr] === Times,  sumexpr /. const_*sum[X__] :> {const, sum[X]}]


Clear[nestn]

nestn = sum[func__,{n_,1,\[Infinity]},indexlists___] :>  Module[{var,member,notmember},
var = prodToList[func]; member = Select[var, !FreeQ[#,n]&]; notmember = Complement[var, member];
	If[Length@{indexlists} == 0, 
	sum[func,{n,1,\[Infinity]}],
	sum[Times@@notmember sum[Times@@member,{n,1,\[Infinity]}], indexlists]
	]
];


Clear[arcnest]

arcnest = X_[(Y1_:1)*X_[Y2_,L2__],L1__] :> X[Y1*Y2,L1,L2];


Clear[Sk]

Sk = Module[{sumRecurse}, 

sumRecurse[{},x_,k_] := -Z[1,{x},k]/x^k - Log[1-x]/x^k;

sumRecurse[m__,x_,i_[n_]] := Block[{m1,mNew}, m1 = m[[1]]; mNew = Delete[m,1];
(-1)^(m1+1) x^-i[n] sum[ x^i[n+1]/i[n+1]^m1 sumRecurse[mNew,x,i[n+1]], {i[n+1],1,i[n]}] + 
x^-i[n] ((-1)^m1 Z[m1,{x},i[n]] HPL[Join[{1},mNew],x] - 
KroneckerDelta[m1,2] Z[1,{x},i[n]] HPL[Join[{2},mNew],x] + HPL[Join[{1},m],x])];

sumRecurse[m__,x_,k_] := Block[{m1,mNew,i}, m1 = m[[1]]; mNew = Delete[m,1];
(-1)^(m1+1) x^-k sum[ x^i[1]/i[1]^m1 sumRecurse[mNew,x,i[1]], {i[1],1,k}] + 
x^-k ((-1)^m1 Z[m1,{x},k] HPL[Join[{1},mNew],x] - 
KroneckerDelta[m1,2] Z[1,{x},k] HPL[Join[{2},mNew],x] + HPL[Join[{1},m],x])];

sum[x_^n_/(n_+k_) Z[m__,n_-1],{n_,1,\[Infinity]}] :> sumRecurse[{m},x,k]];


Clear[factor]

factor[func_, {index_}] := factor[Expand[func], {index}] /; Expand[func] =!= func
factor[func_, {index_}] := Total[factor[#, {index}] & /@ (List @@ func)] /; Expand[func] === func \[And] Head[func] === Plus
factor[func_, {index_}] := Apart[func, index] /; Expand[func] === func \[And] Head[func] =!= Plus
factor[func_, {tt__, index_}] := Sum[Expand[ factor[Times @@ Power @@@ Select[FactorList[term], FreeQ[#, index] &], {tt}]*(Times @@ Power @@@ Select[FactorList[term], ! FreeQ[#, index] &])], {term, If[Head[#] === Plus, List @@ #, {#}] &@Apart[func, index]}]


Clear[PF]

PF = sum[func_,{n_,1,\[Infinity]},indexlists___] :> Block[{ordering,m},
	If[Length@{indexlists} == 0,
	sum[factor[func,{n}],{n,1,\[Infinity]}],
	ordering = Join[Table[m[i],{i,1,Length@{indexlists}}],{n}]; (* {m[1],...,m[j],n} *)
	sum[factor[func, ordering],{n,1,\[Infinity]},indexlists]]
];


Clear[indices]

indices[sumexpr__] := Table[sumexpr[[i]], {i,2,Length[sumexpr]}]


Clear[Lr]

Lr[func_] := With[{temp = func /. x_^-y_ :> (1/x)^y}, prodToList@Denominator@temp] /. x_^y_ :> x


Clear[delta]

(* \[CapitalDelta]temp*\[CapitalDelta]0 is in the same order as L1,L2,... and \[CapitalDelta]0 = shift in k *)

delta[func__,k_] := Module[{notk,factors,A,Cr,\[CapitalDelta]temp,\[CapitalDelta]0},
factors = Lr@func;
notk = Complement[Variables@factors,{k}];
A = D[factors,{notk}];
Cr = D[factors,k];
\[CapitalDelta]temp = -(Inverse@A).Cr; 
\[CapitalDelta]0 = Apply[Times,Denominator@\[CapitalDelta]temp];
{\[CapitalDelta]temp*\[CapitalDelta]0,\[CapitalDelta]0}]


Clear[deltaS]

deltaS[sumexpr__,k_] := Module[{shift,insertsummand,depth,indexlist,a,b,\[CapitalDelta],\[CapitalDelta]0,\[Alpha],\[Beta],temp,tempsum},

shift[x_] := (Table[x[[n]] /. indexlist[[n]] :> indexlist[[n]] + \[CapitalDelta][[n]], {n,1,depth}] /.  k :> k + \[CapitalDelta]0) - x;
insertsummand[x__] := Module[{sign,product,lists}, sign = Select[x,Negative]; product = Select[x, !NumericQ[#] &] /. Times :> List; lists = Delete[#, 0] & /@ product; sign*sum[sumexpr[[1]], ##] &@@ lists ];

depth = Length@indices[sumexpr];
indexlist = indices[sumexpr][[1;;depth,1]];

a = indices[sumexpr][[1;;depth,2]];
b = indices[sumexpr][[1;;depth,3]];

\[CapitalDelta] = delta[sumexpr[[1]],k][[1]];
\[CapitalDelta]0 = delta[sumexpr[[1]],k][[2]];


\[Alpha] = shift[a];
\[Beta] = shift[b];

tempsum = Product[temp[{indexlist[[n]],a[[n]],b[[n]]}] - temp[{indexlist[[n]],a[[n]],a[[n]]+\[Alpha][[n]]-1}] +  temp[{indexlist[[n]],b[[n]]+1,b[[n]]+\[Beta][[n]]}], {n,1,depth}] - Product[temp[{indexlist[[n]],a[[n]],b[[n]]}], {n,1,depth}] // Expand;
Map[insertsummand,tempsum]]


(* ::Section:: *)
(*Junk*)


(*

$SigmaPath="C:\\Users\\zalat\\OneDrive\\Dokumenter\\Fysik & Matematik\\Master's Thesis\\Mathematica Packages\\HarmonicSums"
Get[ToFileName[{$SigmaPath},"Sigma.m"]];
 
$WaPath="C:\\Users\\zalat\\OneDrive\\Dokumenter\\Fysik & Matematik\\Master's Thesis\\Mathematica Packages\\Wa"
SetDirectory[$WaPath];
<<multipleZeta`

$HPLPath="C:\\Users\\zalat\\OneDrive\\Dokumenter\\Fysik & Matematik\\Master's Thesis\\Mathematica Packages\\HPL-2.0"
Get[ToFileName[{$HPLPath},"HPL.m"]];

*)
