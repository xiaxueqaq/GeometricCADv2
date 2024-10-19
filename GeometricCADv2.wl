(* ::Package:: *)

BeginPackage["GeometricCADv2`"];


GeometricCAD::usage="Main Procedure of GeometricCADv2";


Begin["`Private`"];


SquareFreePart[f_]:=Times@@FactorSquareFreeList[f][[1;;-1,1]]


RationalApproximant[x_,dx_]:=Rationalize[x,Min[dx,3]]


ExpressionToRoot[polys_,index_,var_]:=Root[Table[Evaluate[var[[1;;i]]]|->Evaluate[polys[[i]]],{i,1,Length[var]}],index]


BasicConstructibleSetNormalize[tuple_,x_]:=Module[{V,h,f,index},
V=tuple[[1]];h=tuple[[2]];f=tuple[[3]];index=tuple[[4]];
If[Length[x]>1,
V=SquareFreePart/@(GroebnerBasis[SquareFreePart/@V,x,MonomialOrder->DegreeReverseLexicographic]);
(*V=(GroebnerBasis[V,x,MonomialOrder->DegreeReverseLexicographic]);*)
h=PolynomialReduce[h,V,x,MonomialOrder->DegreeReverseLexicographic][[2]]
,
If[Length[V]==0,Return[{V,h,f,index}]];
V={SquareFreePart[PolynomialGCD@@V]};
h=PolynomialRemainder[h,V[[1]],x[[1]]];
];
Return[{V,h,f,index}];
]


ancestorsRule={};


FreeStratification[f_,y_,x_,index_]:=Module[{GB,IGB,JGB,MatOrder,MainPoly,ret,lc,tmpGB,i,v1},
	MatOrder=Table[KroneckerDelta[i,j,1]+KroneckerDelta[i,2]-KroneckerDelta[i+j,Length[y]+4],{i,Length[y]+1},{j,Length[y]+1}];
	If[Length[y]>=2,GB=GroebnerBasis[f,Join[{x},y],MonomialOrder->MatOrder,Method->"GroebnerWalk"],GB=TimeConstrained[GroebnerBasis[f,Join[{x},y],Method->"Buchberger"],1,GroebnerBasis[f,Join[{x},y],Method->"GroebnerWalk"]]];
	If[GB=={1},Return[{}]];
	JGB=Select[GB,Exponent[#,x]==0&];IGB=Select[GB,Exponent[#,x]>0&];
	If[Length[IGB]==0,Return[{BasicConstructibleSetNormalize[{JGB,1,0,index},y]}]];
	MainPoly=First[MinimalBy[IGB,Exponent[#,x]&]];
	lc=(FactorList[Times@@(Coefficient[#,x,Exponent[#,x]]&/@IGB)][[1;;-1,1]]);
	ret=BasicConstructibleSetNormalize[{JGB,Times@@lc,MainPoly,index},y];
	If[ret[[2]]=!=0,ret={ret},ret={}];
	For[i=1,i<=Length[lc],i++,
		tmpGB=GroebnerBasis[Append[GB,lc[[i]]],Join[{x},y],MonomialOrder->MatOrder];
		If[Select[tmpGB,Exponent[#,x]==0&]===GroebnerBasis[Append[JGB,lc[[i]]],y,MonomialOrder->DegreeReverseLexicographic],
			ret=Join[ret,FreeStratification[tmpGB,y,x,index]]
			,
			v1=BasicConstructibleSetNormalize[{Append[JGB,lc[[i]]],1,1,index},y];
			ret=Join[Append[ret,v1],FreeStratification[tmpGB,y,x,index]]
		]
	];
	Return[ret];
	(*If[ret[[2]]=!=0,
	Return[Join[{ret},Join@@(FreeStratification[Append[GB,#],y,x,index]&/@lc)]],
	Return[Join@@(FreeStratification[Append[GB,#],y,x,index]&/@lc)]
	];*)

]


EtaleStratification[f_,y_,x_,index_,ancestors_]:=Module[{GB,IGB,JGB,MatOrder,MainPoly,SubRes,SubResP,ret,lc,tmp,tmpGB,i,v1},
	MatOrder=Table[KroneckerDelta[i,j,1]+KroneckerDelta[i,2]-KroneckerDelta[i+j,Length[y]+4],{i,Length[y]+1},{j,Length[y]+1}];
	GB=GroebnerBasis[f,Join[{x},y],MonomialOrder->MatOrder,Method->"GroebnerWalk"];
	JGB=Select[GB,Exponent[#,x]==0&];IGB=Select[GB,Exponent[#,x]>0&];
	If[GB=={1},Return[{}]];
	If[Length[IGB]==0,tmp=BasicConstructibleSetNormalize[{JGB,1,0,index},y];AppendTo[ancestorsRule[[Length[y]]],({tmp[[1]]->#}&)/@ancestors];Return[{tmp}]];
	MainPoly=First[MinimalBy[IGB,Exponent[#,x]&]];
	lc=(FactorList[Times@@(Coefficient[#,x,Exponent[#,x]]&/@IGB)][[1;;-1,1]]);
	If[Not[ZeroDimensionalQ[GB,Join[{x},y],MatOrder]],
		SubRes=Cancel[Subresultants[MainPoly,D[MainPoly,x],x]/Coefficient[MainPoly,x,Exponent[MainPoly,x]]];
		ret=Join[{{JGB,SubRes[[1]]*Times@@lc,MainPoly,index}},Table[{Join[JGB,SubRes[[1;;i]]],If[i<Length[SubRes],SubRes[[i+1]],1]*Times@@lc,MainPoly,index},{i,1,Length[SubRes]-1}]]
		(*SubResP=SubresultantPolynomials[MainPoly,D[MainPoly,x],x];
		SubRes=Cancel[Coefficient[#,x,Exponent[#,x]]/Coefficient[MainPoly,x,Exponent[MainPoly,x]]]&/@SubResP;
		ret=Join[{{JGB,SubRes[[1]]*Times@@lc,MainPoly,index}},Table[{Join[JGB,SubRes[[1;;i]]],If[i<Length[SubRes],SubRes[[i+1]],1]*Times@@lc,If[SubRes[[i+1]]===0,MainPoly,Numerator[Together[PolynomialQuotient[MainPoly,SubResP[[i+1]],x]]]],index},{i,1,Length[SubRes]-1}]]*)
		,
		ret={{JGB,Times@@lc,MainPoly,index}}
	];
	ret=Select[(BasicConstructibleSetNormalize[#,y]&)/@ret,(#[[1]]=!={1})\[And](#[[2]]=!=0)& ];
	ancestorsRule[[Length[y]]]=Join[ancestorsRule[[Length[y]]],Join@@Table[({ret[[i,1]]->#}&)/@(Join[ancestors,ret[[1;;i-1,1;;2]]]),{i,1,Length[ret]}]];
	tmp={};
	For[i=1,i<=Length[lc],i++,
		tmpGB=GroebnerBasis[Append[GB,lc[[i]]],Join[{x},y],MonomialOrder->MatOrder];
		If[Select[tmpGB,Exponent[#,x]==0&]===GroebnerBasis[Append[JGB,lc[[i]]],y,MonomialOrder->DegreeReverseLexicographic],
			AppendTo[tmp,EtaleStratification[tmpGB,y,x,index,Join[ancestors,ret[[1;;-1,1;;2]]]]]
			,
			v1=BasicConstructibleSetNormalize[{Append[JGB,lc[[i]]],1,1,index},y];
			AppendTo[tmp,{v1}];
			AppendTo[ancestorsRule[[Length[y]]],(v1[[1]]->#)&/@Join[ancestors,ret[[1;;-1,1;;2]]]];
			AppendTo[tmp,EtaleStratification[tmpGB,y,x,index,Join[ancestors,ret[[1;;-1,1;;2]]]]]

		]
	];
	(*Return[Join[ret,Join@@(EtaleStratification[Append[GB,#],y,x,index,Join[ancestors,ret[[1;;-1,1;;2]]]]&/@lc)]];*)
	Return[Join[ret,Join@@tmp]];
]


EqualQ[a_,b_]:=TimeConstrained[PossibleZeroQ[a-b,Method->"ExactAlgebraics"],2,Print["EQ test slow. a = ",a,". b = ",b];TimeConstrained[PossibleZeroQ[Simplify[a]-Simplify[b],Method->"ExactAlgebraics"],2,PossibleZeroQ[RootReduce[a]-RootReduce[b],Method->"ExactAlgebraics"]]]


GenerateSection[base_,expr_,poly_,par_,var_,label_]:=Module[{sol,solnum,solexp,ret,i},
If[Length[par]>0,
	sol=TimeConstrained[Solve[(poly/.Table[par[[i]]->base[[i]],{i,1,Length[par]}])==0,var,Reals],5,solnum=Simplify[base];Solve[(poly/.Table[par[[i]]->solnum[[i]],{i,1,Length[par]}])==0,var,Reals]];
	solnum=Length[sol]
	,
	sol=Solve[poly==0,var,Reals];
	solnum=Length[sol]
	(*sol=TimeConstrained[CountRoots[(poly/.Table[par[[i]]->base[[i]],{i,1,Length[par]}]),var],0.25,Length[Solve[(poly/.Table[par[[i]]->base[[i]],{i,1,Length[par]}])==0,var,Reals]]]*)
	(*sol=Length[Solve[(poly/.Table[par[[i]]->base[[i]],{i,1,Length[par]}])==0,var,Reals]],
	sol=CountRoots[poly,var]*)
];
If[solnum==0,Return[{}]];
solexp=Table[{Append[expr[[1]],poly],Append[expr[[2]],i]},{i,1,solnum}];
sol=Table[ExpressionToRoot[solexp[[i,1]],solexp[[i,2]],Append[par,var]],{i,1,Length[solexp]}];
If[Length[par]==0,For[i=1,i<=Length[sol],i++,If[(sol[[i,0]]===Root)\[And](sol[[i,1]][var]=!=poly),solexp[[i]]={{sol[[i,1]][var]},{sol[[i,2]]}},If[QuadraticIrrationalQ[sol[[i]]],solnum=MinimalPolynomial[sol[[i]],var];If[sol[[i]]<-Coefficient[solnum,var,1]/(2Coefficient[solnum,var,2]),solexp[[i]]={{solnum},{1}},solexp[[i]]={{solnum},{2}}]]]],
For[i=1,i<=Length[sol],i++,
	If[(sol[[i,0]]===Root)\[And](Length[sol[[i,2]]]==Length[par]+1),solexp[[i,1,-1]]=(sol[[i,1,-1]]@@Append[par,var]);solexp[[i,2,-1]]=sol[[i,2,-1]]]; (*If a simpler triangular form is found*)
	(*If[Exponent[poly,var]<=2,sol[[i]]=Simplify[sol[[i]]]];*)
];
];
(*ret=DeleteDuplicates[Table[{sol[[i]],solexp[[i]]},{i,1,Length[sol]}],(PossibleZeroQ[#1[[1]]-#2[[1]],Method->"ExactAlgebraics"])&];*)
ret=DeleteDuplicates[Table[{sol[[i]],solexp[[i]]},{i,1,Length[sol]}],EqualQ[#1[[1]],#2[[1]]]&];
Return[Table[{Append[base,ret[[i,1]]],label,ret[[i,2]]},{i,1,Length[ret]}]]
]


ZeroDimensionalQ[J_,x_]:=(Return[Length[Select[Variables[First[MonomialList[#,x,DegreeReverseLexicographic]]]&/@J,Length[#]==1&]]==Length[x]])
ZeroDimensionalQ[J_,x_,order_]:=(Return[Length[Select[Variables[First[MonomialList[#,x,order]]]&/@J,Length[#]==1&]]==Length[x]]) (*The debugger of mma does not support default parameter, we have to adjust here*)


Lift[ListS_,ListJ_,x_]:=Module[{cells,labels,bands,sol,cyl,q,qs,flag,i,j,k,l,t,n,p,tmp,crIndex,verbose,JtoS,cellcache,lifttime,mergetime,relabeltime},
	verbose:=False;
	n=Length[x];
	cells={};
	bands={};
	cyl={};(*Partition the real axis*)
	For[j=1,j<=Length[ListJ[[1]]],j++,
		If[Length[ListJ[[1,j]]]==0,bands={{}};Continue[]];
		(*cyl=Join[cyl,SingleLift[{},ListJ[[1,j,1]],x[[1]],{ListJ[[1,j]]}]];*)
		cyl=Join[cyl,GenerateSection[{},{{},{}},ListJ[[1,j,1]],{},x[[1]],{ListJ[[1,j]]}]];
	];
	For[j=1,j<=Length[cyl],j++,
		flag=True;
		For[k=1,k<=Length[cells],k++,
			If[cells[[k,1]]==cyl[[j,1]],
				flag=False;
				cells[[k,2]]=Join[cells[[k,2]],cyl[[j,2]]];
				Break[];
			]
		];
		If[flag,AppendTo[cells,cyl[[j]]]];
	];
	cells=Sort[cells,#1[[1,1]]<#2[[1,1]]&];
	If[Length[bands]!=0,(*Bands between sections are needed*)
		(*If[Length[cells]==0,cells={{{0},{{}}}}, (*No section, 1 band*)
		bands=Table[{{RationalApproximant[(cells[[j,1,1]]+cells[[j+1,1,1]])/2,(cells[[j+1,1,1]]-cells[[j,1,1]])/4]},{{}}},{j,1,Length[cells]-1}];
		PrependTo[bands,{{RationalApproximant[cells[[1,1,1]]-1,1/2]},{{}}}];
		AppendTo[bands,{{RationalApproximant[cells[[Length[cells],1,1]]+1,1/2]},{{}}}];
		For[j=1,j<=Length[cells],j++,AppendTo[cells[[j,2]],{}]];
		cells=Riffle[bands,cells];
		]*)
		If[Length[cells]==0,cells={{{0},{{}},{{x[[1]]},{1}}}}, (*No section, 1 band*)
		bands=Table[{{RationalApproximant[(cells[[j,1,1]]+cells[[j+1,1,1]])/2,(cells[[j+1,1,1]]-cells[[j,1,1]])/4]},{{}},{{x[[1]]-RationalApproximant[(cells[[j,1,1]]+cells[[j+1,1,1]])/2,(cells[[j+1,1,1]]-cells[[j,1,1]])/4]},{1}}},{j,1,Length[cells]-1}];
		PrependTo[bands,{{RationalApproximant[cells[[1,1,1]]-1,1/2]},{{}},{{x[[1]]-RationalApproximant[cells[[1,1,1]]-1,1/2]},{1}}}];
		AppendTo[bands,{{RationalApproximant[cells[[Length[cells],1,1]]+1,1/2]},{{}},{{x[[1]]-RationalApproximant[cells[[Length[cells],1,1]]+1,1/2]},{1}}}];
		For[j=1,j<=Length[cells],j++,AppendTo[cells[[j,2]],{}]];
		cells=Riffle[bands,cells];
		]
	];
	If[verbose,Print["Before relabel: ",cells]];
	(*Relabel the cells by regions*)
	For[j=1,j<=Length[cells],j++,
		labels={};
		For[k=1,k<=Length[cells[[j,2]]],k++,
			For[i=1,i<=Length[ListS[[1]]],i++,
				If[(ListS[[1,i,1]]==cells[[j,2,k]])\[And](0!=ListS[[1,i,2]]/.{x[[1]]->cells[[j,1,1]]}),
					AppendTo[labels,ListS[[1,i]]];
				]
			]
		];
		cells[[j,2]]=SortBy[labels,#[[4]]&];
	];
	cells={cells};
	If[verbose,Print[cells]];
	For[i=2,i<=n,i++,
		Print["i=",i,"; Total= ",Length[cells[[i-1]]]];
		AppendTo[cells,{}];
		JtoS=Dispatch[Table[ListJ[[i,j]]->Select[ListS[[i]],#[[1]]===ListJ[[i,j]]&],{j,1,Length[ListJ[[i]]]}]];
		cellcache={};
		For[j=1,j<=Length[cells[[i-1]]],j++,
			If[(Mod[j,1000]==0),Print["j= ",j,Now]];
			sol=SessionTime[];
			p=cells[[i-1,j]];
			If[verbose,Print["Lifting over p=",p]];
			(*Lift to the sections*)
			(*For[k=1,k<= Length[p[[2]]],k++,
				If[Length[p[[2,k,4]]]>1,Continue[]];
				If[p[[2,k,3]]=!=0, 
					(*AppendTo[q,SingleLift[p[[1]],p[[2,k,3]]/.Table[x[[l]]->p[[1,l]],{l,1,i-1}],x[[i]],{ListJ[[i,p[[2,k,4,1]]]]}]];*)
					AppendTo[q,GenerateSection[p[[1]],p[[3]],p[[2,k,3]],x[[1;;i-1]],x[[i]],{ListJ[[i,p[[2,k,4,1]]]]}]];
					AppendTo[labels,p[[2,k]]];
					,
					AppendTo[bands,p[[2,k]]];
				]
			];*)
			tmp=Select[p[[2]],Length[#[[4]]]==1&];
			bands=Select[tmp,#[[3]]===0&];
			tmp=Select[tmp,#[[3]]=!=0&];
			q=Table[GenerateSection[p[[1]],p[[3]],tmp[[k,3]],x[[1;;i-1]],x[[i]],{ListJ[[i,tmp[[k,4,1]]]]}],{k,1,Length[tmp]}];
			lifttime=SessionTime[]-sol;
			If[verbose,Print["Sections are ",q]];
			If[verbose,Print["Bands are ",bands]];
			cyl={};(*Merge the sections*)
			For[k=1,k<=Length[q],k++,
				(*qs=q[[k]];
				For[l=1,l<k,l++,
					tmp=Select[p[[2]],#[[4]]=={labels[[k,4,1]],labels[[l,4,1]]}&];
					If[(Length[tmp]!=0)\[And](Length[qs]!=0),
						tmp=SingleLift[p[[1]],tmp[[1,3]]/.Table[x[[l]]->p[[1,l]],{l,1,i-1}],x[[i]],0];
						If[Length[tmp]==0,Continue[]];
						tmp=tmp[[1;;-1,1]];
						If[verbose,Print["Pair= ",{labels[[k,4,1]],labels[[l,4,1]]},"; tmp= ",tmp]];
						(*crIndex=Table[(Nearest[cyl[[1;;-1,1]]\[Rule]"Index",tmp[[t]]])[[1]],{t,1,Length[tmp]}];*)
						crIndex=Table[SelectIndex[cyl[[1;;-1,1,-1]],tmp[[t,-1]]],{t,1,Length[tmp]}];
						If[verbose,Print["crIndex in cyl= ",crIndex]];
						For[t=1,t<=Length[crIndex],t++,AppendTo[cyl[[crIndex[[t]],2]],ListJ[[i,labels[[k,4,1]]]]]];
						(*crIndex=Sort[Table[(Nearest[qs[[1;;-1,1]]->"Index",tmp[[t]]])[[1]],{t,1,Length[tmp]}]];*)
						crIndex=Sort[Table[SelectIndex[qs[[1;;-1,1,-1]],tmp[[t,-1]]],{t,1,Length[tmp]}]];
						If[verbose,Print["crIndex in qs= ",crIndex]];
						(*If[MemberQ[crIndex,0],Print["base=",p];Print[" cyl=",cyl];Print[" qs=",qs];Print["Sections are",q];Print["Labels=",labels]];*)
						(*For[t=Length[crIndex],t>=1,t--,If[crIndex[[t]]>0,qs=Delete[qs,crIndex[[t]]]]];*)
						qs=qs[[Select[Table[t,{t,1,Length[qs]}],Not[MemberQ[crIndex,#]]&]]]
						,
						Continue[];
					]
				];
				If[verbose,Print["cyl= ",cyl];Print["qs= ",qs]];
				cyl=Join[cyl,qs];*)
				l=1;
				t=1;
				qs={};
				While[(l<=Length[cyl])\[And](t<=Length[q[[k]]]),
					If[TimeConstrained[PossibleZeroQ[cyl[[l,1,i]]-q[[k,t,1,i]],Method->"ExactAlgebraics"],1,(*Print["EQ test slow. a = ",cyl[[l,1,i]],". b = ",q[[k,t,1,i]]];*)
						cyl[[l,1,i]]=TimeConstrained[RootReduce[cyl[[l,1,i]]],1,cyl[[l,1,i]]];q[[k,t,1,i]]=TimeConstrained[RootReduce[q[[k,t,1,i]]],1,q[[k,t,1,i]]];
						TimeConstrained[PossibleZeroQ[cyl[[l,1,i]]-q[[k,t,1,i]],Method->"ExactAlgebraics"],5,Print["Mathematica internal error. Cannot test for equality: a = ",cyl[[l,1,i]],". b = ",q[[k,t,1,i]],". Assuming yes"];True]],
						(*EqualQ[cyl[[l,1,i]],q[[k,t,1,i]]]*)
						(*(PossibleZeroQ[cyl[[l,1,i]]-q[[k,t,1,i]],Method->"ExactAlgebraics"]),*)
						tmp={cyl[[l,1]],Join[cyl[[l,2]],q[[k,t,2]]],cyl[[l,3]]};
						AppendTo[qs,tmp];
						t++;l++;
						Continue[];
					];
					If[cyl[[l,1,i]]<q[[k,t,1,i]],
						AppendTo[qs,cyl[[l]]];
						l++;
						Continue[]
					];
					If[cyl[[l,1,i]]>q[[k,t,1,i]],
						AppendTo[qs,q[[k,t]]];
						t++;
						Continue[]
					];
					Print["Sorry! Cannot compare ",cyl[[l,1,i]]," and ", q[[k,t,1,i]],". Aborted"];
					Print["base = ",p," ; polys = ",(Select[p[[2]],Length[#[[4]]]==1&])[[1;;-1,3]]];
					Abort[];
					$MaxExtraPrecision++
				];
				If[l<=Length[cyl],qs=Join[qs,cyl[[l;;-1]]]];
				If[t<=Length[q[[k]]],qs=Join[qs,q[[k,t;;-1]]]];
				cyl=qs;
				(*If[verbose,Print[cyl[[1;;-1,1]]]];*)
			];
			mergetime=SessionTime[]-sol-lifttime;
			(*
			For[k=1,k<=Length[cyl],k++,cyl[[k,2]]=DeleteDuplicates[cyl[[k,2]]]];
			cyl=Sort[cyl,#1[[1,i]]<#2[[1,i]]&];
			*)
			If[verbose,Print["Merged Sections= ",cyl[[1;;-1,1]]]];
			If[Length[bands]!=0,(*Add the bands*)
				(*If[Length[cyl]==0,cyl={{Append[p[[1]],0],Table[ListJ[[i,bands[[t,4,1]]]],{t,1,Length[bands]}]}},
				tmp=Join[{{Append[p[[1]],RationalApproximant[cyl[[1,1,i]]-1,1/2]],{}}},Table[{Append[p[[1]],RationalApproximant[(cyl[[t,1,i]]+cyl[[t+1,1,i]])/2,(cyl[[t+1,1,i]]-cyl[[t,1,i]])/2]],{}},{t,1,Length[cyl]-1}],{{Append[p[[1]],RationalApproximant[cyl[[-1,1,i]]+1,1/2]],{}}}];
				cyl=Riffle[tmp,cyl];
				For[k=1,k<=Length[cyl],k++,
					cyl[[k,2]]=Join[cyl[[k,2]],Table[ListJ[[i,bands[[t,4,1]]]],{t,1,Length[bands]}]]
				]
			];*)
				If[Length[cyl]==0,cyl={{Append[p[[1]],0],Table[ListJ[[i,bands[[t,4,1]]]],{t,1,Length[bands]}],{Append[p[[3,1]],x[[i]]],Append[p[[3,2]],1]}}},
				tmp=Join[{{Append[p[[1]],RationalApproximant[cyl[[1,1,i]]-1,1/2]],{},{Append[p[[3,1]],x[[i]]-RationalApproximant[cyl[[1,1,i]]-1,1/2]],Append[p[[3,2]],1]}}},Table[{Append[p[[1]],RationalApproximant[(cyl[[t,1,i]]+cyl[[t+1,1,i]])/2,(cyl[[t+1,1,i]]-cyl[[t,1,i]])/4]],{},{Append[p[[3,1]],x[[i]]-RationalApproximant[(cyl[[t,1,i]]+cyl[[t+1,1,i]])/2,(cyl[[t+1,1,i]]-cyl[[t,1,i]])/4]],Append[p[[3,2]],1]}},{t,1,Length[cyl]-1}],{{Append[p[[1]],RationalApproximant[cyl[[-1,1,i]]+1,1/2]],{},{Append[p[[3,1]],x[[i]]-RationalApproximant[cyl[[-1,1,i]]+1,1/2]],Append[p[[3,2]],1]}}}];
				cyl=Riffle[tmp,cyl];
				For[k=1,k<=Length[cyl],k++,
					cyl[[k,2]]=Join[cyl[[k,2]],Table[ListJ[[i,bands[[t,4,1]]]],{t,1,Length[bands]}]]
				]
			];
			];
			If[verbose,Print["The cylinder over p=",cyl]];
			(*Relabel*)
			If[i<n,
			For[k=1,k<=Length[cyl],k++,
				(*labels={};
				tmp=Join@@cyl[[1;;-1,2]]; 
				tmp=Select[ListS[[i]],MemberQ[tmp,#[[1]]]& ];
				
				For[l=1,l<=Length[cyl[[k,2]]],l++,
					(*For[t=1,t<=Length[ListS[[i]]],t++,
						(*If[(ListS[[i,t,1]]===cyl[[k,2,l]])\[And](FullSimplify[(ListS[[i,t,2]]/.Table[x[[u]]->cyl[[k,1,u]],{u,1,i}])!=0]),AppendTo[labels,ListS[[i,t]]],Nothing,Print["Warning! Cannot decide the truth value in relabel phase"]];*)
						If[(ListS[[i,t,1]]===cyl[[k,2,l]])\[And](Not[TimeConstrained[PossibleZeroQ[(ListS[[i,t,2]]/.Table[x[[u]]->cyl[[k,1,u]],{u,1,i}]),Method->"ExactAlgebraics"],1,PossibleZeroQ[(ListS[[i,t,2]]/.Table[x[[u]]->cyl[[k,1,u]],{u,1,i}])]]]),AppendTo[labels,ListS[[i,t]]],Nothing,Print["Warning! Cannot decide the truth value in relabel phase"]];
					]*)
					For[t=1,t<=Length[tmp],t++,
						If[(tmp[[t,1]]===cyl[[k,2,l]])\[And]Not[(TimeConstrained[PossibleZeroQ[(tmp[[t,2]]/.Table[x[[u]]->cyl[[k,1,u]],{u,1,i}]),Method->"ExactAlgebraics"],1,PossibleZeroQ[(tmp[[t,2]]/.Table[x[[u]]->cyl[[k,1,u]],{u,1,i}])]])],
							AppendTo[labels,tmp[[t]]];
						]
					]
					
				];*)
				tmp=Join@@(cyl[[k,2]]/.JtoS); (*Candidates for Basic Constructible Sets*)
				t=If[i<n,Join@@(cyl[[k,2]]/.ancestorsRule[[i]]),{}]; (*Impossible Basic Constructible Sets From the Rules*)
				cyl[[k,2]]=Select[tmp,!MemberQ[t,#[[1;;2]]]&];
				(*tmp=Select[tmp,!MemberQ[t,#[[1;;2]]]&];
				cyl[[k,2]]=Select[tmp,!PossibleZeroQ[#[[2]]/.(Table[x[[u]]->cyl[[k,1,u]],{u,1,i}])]&];*)
				(*For[l=1,l<=Length[tmp],l++,
					If[Not[TimeConstrained[PossibleZeroQ[tmp[[l,2]]/.(Table[x[[u]]->cyl[[k,1,u]],{u,1,i}]),Method->"ExactAlgebraics"],1,PossibleZeroQ[tmp[[l,2]]/.(Table[x[[u]]->cyl[[k,1,u]],{u,1,i}])]]],
						AppendTo[labels,tmp[[l]]];
					]
				];*)
				(*cyl[[k,2]]=SortBy[labels,#[[4]]&];*)
				(*If[Length[labels]==0,Print["Empty label at ",cyl[[k]]]];*)
			];
			];
			relabeltime=SessionTime[]-lifttime-mergetime-sol;
			cellcache=Join[cellcache,cyl];
			If[(Mod[j,1000]==0)\[Or](j==Length[cells[[i-1]]]),
			cells[[i]]=Join[cells[[i]],cellcache];
			cellcache={};
			];
			sol=SessionTime[]-sol;
			If[sol>2,Print["Lifting slow @ ",j,". Time used = ",sol,". LIFT = ",lifttime,", MERGE = ",mergetime,", RELABEL = ",relabeltime]];
		];
		If[verbose,Print["Cells at level ",i,"= ",cells[[i]]]];
	];
	Return[cells];
]


GeometricCAD[L0_,x_]:=Module[{ListJ,ListS,i,n,S1,S2,S0,L},
	L=(GroebnerBasis[#,x,MonomialOrder->DegreeReverseLexicographic]&/@L0);
	ListJ={L};n=Length[x];ListS={Table[{L[[i]],1,1,{0}},{i,1,Length[L]}]};ancestorsRule=Table[{},{i,1,n}];
	For[i=n-1,i>=1,i--,
		(*S1=Join@@Table[EtaleStratification[ListJ[[1,k]],x[[1;;i]],x[[i+1]],{k}],{k,1,Length[ListJ[[1]]]}];*)
		Print["Projection Phase, i=", i, "Total=",Length[ListJ[[1]]]];
		S1=Join@@Table[EtaleStratification[ListJ[[1,k]],x[[1;;i]],x[[i+1]],{k},{}],{k,1,Length[ListJ[[1]]]}];
		S2=Join@@Join@@Table[If[(Not[ZeroDimensionalQ[ListJ[[1,j]],x[[1;;(i+1)]]]]\[And]Not[ZeroDimensionalQ[ListJ[[1,k]],x[[1;;(i+1)]]]])\[And]((ListJ[[1,j]]=!={})\[And](ListJ[[1,k]]=!={})),FreeStratification[Join[ListJ[[1,j]],ListJ[[1,k]]],x[[1;;i]],x[[i+1]],{j,k}],{}],{j,1,Length[ListJ[[1]]]},{k,1,j-1}];
		ancestorsRule[[i]]=Dispatch[Normal[Merge[ancestorsRule[[i]],DeleteDuplicates]]];
		(*S1=BasicConstructibleSetNormalize[#,x[[1;;i]]]&/@S1;
		S2=BasicConstructibleSetNormalize[#,x[[1;;i]]]&/@S2;*)
		S0=Join[S1,S2];
		PrependTo[ListS,DeleteDuplicates[S0]];
		PrependTo[ListJ,DeleteDuplicates[S0[[1;;-1,1]]]];
	];
	For[i=n-1,i>=1,i--,Print["Regions in Level ",i,": ",ListS[[i]]]];
	For[i=n,i>=1,i--,Print["Extraction in Level ",i,": ",ListJ[[i]]]];
	Return[Lift[ListS,ListJ,x][[1;;-1,1;;-1,1]]];
]


End[];


EndPackage[];
