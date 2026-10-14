(* ::Package:: *)

(*Truncation of f up to degree k in the variables v*)
Truncate[f_,v_,k_]:=Module[{\[Epsilon],deg,pol,trun},
 pol = Normal[Series[f/.Table[v[[i]]->\[Epsilon] v[[i]],{i,1,Length[v]}],{\[Epsilon],0,k}]];
 deg = Exponent[pol,\[Epsilon]];
 trun = 0 f;
 If[Max[deg] <= k,
  trun = pol/.\[Epsilon]->1;
 ];
 Expand[trun]
]


(*Returns all the monomials in the variables x of degree lower than or equal to n*)
VecDeg[n_,x_] := Module[{kk,jj,vv,m,prod,MM,NN},
 m = Length[x];
 vv = ConstantArray[0,{m}];
 prod = 1;
 For[kk=1,kk<= m,kk++,
  For[jj=0,jj<= n, jj++,
   vv[[kk]]= vv[[kk]]+ (x[[kk]])^jj;
   ];
   prod = prod*vv[[kk]];
 ];
 prod = prod//Expand;
 MM = MonomialList[prod,x,"DegreeLexicographic"];
 NN = Max[Position[MM,(x[[1]])^n]];
 MM[[NN;;All]]
];


(*Returns all the monomials in the variables x of degree equal to n*)
DegVecDeg[n_,x_] := Module[{MM,m},
 MM = VecDeg[n,x];
 m = Max[Position[MM,(x[[-1]])^n]];
 MM[[1;;m]]
];


(*Compute the Lie derivative of f along g in the variables v*)
LieDerivative[f_,g_,v_]:= D[f,{v}] . g


(*Compute the Lie parenthesis of f and g in the variables v*)
Liep[f_,g_,v_]:= D[g,{v}] . f-D[f,{v}] . g


(*Push forward of f through \[Phi]*)
PushForw[\[Phi]_,f_,i\[Phi]_,v_]:= D[\[Phi],{v}] . f/.Table[v[[i]]->i\[Phi][[i]],{i,1,Length[v]}];


(*Apply g to f in the variables v*)
ComposeFun[f_,g_,v_]:=Factor[f/.Table[v[[i]]->g[[i]],{i,1,Length[v]}]];


FindResonances[A_,v_,NN_]:=Module[{n,vec,mons,k,params,sol,parres,freeparam,resonancebasis},
 n=Length[v];
 vec = ConstantArray[0,n];
 mons = DeleteCases[VecDeg[NN,v],1];
 For[k=1,k<=n,k++,
  mons=DeleteCases[mons,v[[k]]];
 ];
 For[k=1,k<=n,k++,
  vec[[k]]= Sum[Subscript[\[Gamma], k,i]mons[[i]],{i,1,Length[mons]}];
 ];
 params=Flatten[Table[Subscript[\[Gamma], k,i],{k,1,n},{i,1,Length[mons]}]];
 sol = Quiet[Solve[0==DeleteCases[Flatten[CoefficientList[Liep[vec,A . v,v],v]],0],params]];
 If[Length[sol]==1,
  parres = vec/.sol;
  freeparam = Intersection[Variables[parres],params];
  resonancebasis = Table[Coefficient[parres,freeparam[[i]]],{i,1,Length[freeparam]}]//Transpose;
  resonancebasis = resonancebasis[[1]]//Transpose;
 ,
  resonancebasis = {};
 ];
 resonancebasis
]


(*Approximate a near identity symmetry of a f up to degree N*)
ApproxSymmetry[f_,v_,NN_]:=Module[{n,k,g,hf,fk,mons,sg,eq,sol},
 n = Length[v];
 k = 1;
 g = v;
 hf=f;
 Do[
  fk=Truncate[f,v,k];
  mons = DegVecDeg[k,v];
  sg = g + Table[Sum[Subscript[\[Beta], k,i,j]mons[[i]],{i,1,Length[mons]}],{j,1,n}];
  eq = DeleteCases[Flatten[CoefficientList[Truncate[Liep[f,sg,v],v,k],v]],0];
  sol = FindInstance[eq==0, Flatten[Table[Subscript[\[Beta], k,i,j],{i,1,Length[mons]},{j,1,n}]],Reals];
  If[Length[sol]==1,
   g=sg/.sol[[1]];
   hf=hf/.sol[[1]];
  ,
   Print[StringJoin["Found ",ToString[Length[sol]], " solutions at step ",ToString[k]]];
   Print[sol];
   g=0;
   Break[];
  ];
 ,
  {k,2,NN}
 ];
 g
]


(*Given a symmetry approximate the corresponding diffeomorphism up to degree N*)
ApproxDiffeo[g_,v_,NN_]:=Module[{n,pol,VN,e1,\[Kappa],Lgt},
 n = Length[v];
 pol=ConstantArray[0,n];
 VN = Table[i^j,{j,0,NN-1},{i,1,NN}];
 e1 = Join[{1},ConstantArray[0,{NN-1}]];
 For[\[Kappa]=1,\[Kappa]<=n,\[Kappa]++,
  Lgt = ConstantArray[0,NN];
  Lgt[[1]]=v[[\[Kappa]]];
  Do[
   Lgt[[i+1]]=Truncate[D[Lgt[[i]],{v}] . g,v,NN];
  ,
   {i,1,NN-1}
  ];
  pol[[\[Kappa]]] = e1 . Inverse[VN] . Lgt//Expand;
 ];
 pol
]


(*Consistent Pade approximation of degree m/n*)
ConsistentPade[f_,v_,orderNum_,orderDen_]:= Module[{ftr,\[Epsilon],pade},
 ftr = Truncate[f,v,orderNum+2orderDen]/.Table[v[[i]]->\[Epsilon] v[[i]],{i,1,Length[v]}];
 pade = Quiet[Together[Factor[Check[PadeApproximant[ftr,{\[Epsilon],0,{orderNum,orderDen}}]/.\[Epsilon]->1,0]]]]
]


(*Find the Pade approximatn using the \[Epsilon]-method of Wynn*)
Wynn[fun_,v_,NN_]:=Module[{seq, M,wlist,i,j,k,wdel,lozenge},
 seq = Table[Truncate[fun,v,k],{k,0,NN}];
 M = Length[seq];
 wlist = ConstantArray[0,{M+1,M+1}];
 wlist[[1;;-2,2]]=seq;
 For[j=3,j<=M+1,j++,
  For[i=1,i<=M-j+2,i++,
   wlist[[i,j]]=Simplify[wlist[[i+1,j-2]]+(wlist[[i+1,j-1]]-wlist[[i,j-1]])^-1];
  ];
 ];
 wdel = wlist[[1;;-2,2;;All;;2]];
 lozenge = ConstantArray[Indeterminate,Dimensions[wdel]];
 For[k=1,k<=Dimensions[wdel][[2]],k++,
  lozenge[[k;;M-k+1,k]]=wdel[[1;;M-2k+2,k]];
 ];
 {lozenge,wlist[[1;;-2,2;;All]]}
]


(*Find the inverse of a given diffeomorphism up to degree N*)
FindInv[h_,v_,ev_,NN_]:= Module[{n,pol,Afun,i,polval,j,Bfun,k,Bfx,ih},
	n=Length[v];
	pol=Truncate[h,v,NN];
	Afun = ConstantArray[0,{n,n}];
	For[i=1,i<=n,i++,
		polval = pol[[i]]-v[[i]];
		For[j=1,j<=n,j++,
			Afun[[i,j]]=PolynomialQuotient[polval,v[[j]],v[[j]]];
			polval = polval - Afun[[i,j]] v[[j]]//Expand;
		];
	];
	Bfun = 0 Afun;
	For[k=1,k<=NN-1,k++,
		Bfx=ev+Bfun . ev;
		Bfun=-(Afun/.Table[v[[i]]->Bfx[[i]],{i,1,n}]) . (IdentityMatrix[n]+Bfun);
	];
	ih = ev+Truncate[Bfun,ev,NN-1] . ev//Expand
]


(*Find the Pade approximatn using the \[Epsilon]-method of Wynn*)
SequenceWynn[seq_]:=Module[{ M,wlist,i,j,k,wdel,lozenge},
 M = Length[seq];
 wlist = ConstantArray[Indeterminate,{M+1,M+1}];
 wlist[[1;;-2,2]]=seq;
 For[j=3,j<=M+1,j++,
  For[i=1,i<=M-j+2,i++,
   wlist[[i,j]]=Simplify[wlist[[i+1,j-2]]+(wlist[[i+1,j-1]]-wlist[[i,j-1]])^-1];
  ];
 ];
 wdel = wlist[[1;;-2,2;;All;;2]]
]
