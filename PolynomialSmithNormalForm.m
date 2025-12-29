(* ::Package:: *)

(* :Title: PolynomialSmithNormalForm, Version 1.0, 1994*)

(* :Author: David Jabon
	    Eastern Washington University
	    jabon@ewu.edu

  

*)

(* :Summary:
   A package that defines  (1)  a function that returns the
   Smith normal form of a matrix whose entries are
   polynomials in one variable with rational 
   coefficients (2) a function that returns the  
   invariant factors of such a matrix (3) a function
   which returns the Smith normal form as well as
   matrices which transform the given matrix into 
   its Smith normal form.
*)

(* :Context: PolynomialSmithNormalForm` *)

(* :Package Version: 1.0 *)

(* :Copyright: Copyright 1994 *)

(* :History:
  Created by David Jabon at Eastern Washington
  University, 1993-4
*)

(* :Keywords: 

  Smith normal form, invariant factors *)


(* :Mathematica Version: 2.2 *)

(* :Limitations: 

This package can only be used with matrices whose
entries are polynomials in a single variable with
rational coefficients.

*)


BeginPackage["PolynomialSmithNormalForm`"]


PolynomialSmithForm::usage =
     "PolynomialSmithForm[A,x] gives,for a matrix A 
     with entries which are polynomials in x with
     rational coefficients, the Smith normal form of A. "
     
ExtendedPolynomialSmithForm::usage =    
     "ExtendedPolynomialSmithForm[A,x] gives, for a 
      matrix A with  entries which are polynomials in 
      x with rational coefficients, {D, {P,Q}} where 
      D is in Smith normal form and P and Q are 
      matrices such that P A Q = D. "      
 
PolynomialInvariantFactors::usage=     
     "PolynomialInvariantFactors[A,x] gives, for a 
      matrix A with entries which are polynomials 
      in x with rational coefficients, the invariant 
      factors of A."
     
Begin["`Private`"]    
             
LeadingCoefficient[p_, x_]:=Coefficient[p,x,Exponent[p,x]];

PolynomialExtendedGCD[a1_,b1_,var_]:=Module[{x,
               a, b, u=1 ,v,d, v1,v3,t1,t3},
          a=a1 /. var-> x;
          b=b1 /. var-> x;
          d=a;
          
          If[Expand[b,x]  ===0,(v=0;Print["b=0"]),
          (v1=0; v3=b; While[v3=!=0, (
          q=PolynomialQuotient[d,v3,x];
           t3=Expand[d- q v3,x];
           t1=Expand[u-q v1,x];
           u=v1;
           d=v3;
           v1=t1;
           v3=t3)]; v=PolynomialQuotient[ d - a u, b, x])];
           Return[Expand[{d, {u,v}}/Coefficient[d,x,Exponent[d,x]],x]/. x->var]];
          
                


NormalizedPolynomialExtendedGCD[a_,b_,x_]:=
          If[ PolynomialRemainder[b,a,x]===0, 
          Return[Expand[{a,{1,0}}/LeadingCoefficient[a,x] ]],
          Return[PolynomialExtendedGCD[a,b,x]]];
                

R1[i_,u_,A_]:= 
      Array[Which[ #==i, u A[[i]] , True, A[[#]] ] &, Length[A] ];
C1[i_,u_,A_]:=Transpose[R1[i,u, Transpose[A]]];
R2[c_,i_,j_,A_]:=Array[Which[ # == j, A[[j]]+c A[[i]], 
             True, A[[#  ]]] &, Length[A]];
C2[c_, i_,j_,A_]:=Transpose[R2[c,i,j,Transpose[A] ]];
R3[i_,j_, A_]:= Array[Which[ # == i, A[[j]], # ==j, 
                A[[i]], True, A[[#  ]]] &, Length[A] ];              
C3[i_,j_, A_]:= Transpose[R3[i,j,Transpose[A]]];
R4[i_,j_,d_,a_,b_,u_,v_,A_,x_] := Array[Which[ # == i, 
                     u A[[i]]+ v A[[j]],
                     # == j, 
                     PolynomialQuotient[-b,d,x]  A[[i]] +
                     PolynomialQuotient[a,d,x] A[[j]], True, A[[#]] ] &,
                     Length[A]] ;
                            
C4[i_,j_,d_,a_,b_,u_,v_,A_,x_] := 
                     Transpose[R4[i,j,d,a,b,u,v,Transpose[A],x]];
             
 PolynomialEliminateCol[A_,x_]:=
            Module[{nA=A,ExtGCD},
            
            Do[If[nA[[m,j]] =!= 0,
            (ExtGCD=NormalizedPolynomialExtendedGCD[nA[[m,m]],
             nA[[m,j]],x ];
            
            nA=Expand[C4[m,j,ExtGCD[[1]],nA[[m,m]], nA[[m,j]],
            ExtGCD[[2,1]], ExtGCD[[2,2]], nA,x],x]
            ), (Continue[ ])],
             {j,m+1, cols}];
            Return[nA]];   


            
 PolynomialEliminateRow[A_,x_]:=
            Module[{nA=A,ExtGCD},
            
            Do[If[nA[[j,m]] =!= 0,
            (ExtGCD=NormalizedPolynomialExtendedGCD[nA[[m,m]], nA[[j,m]],x ];
            nA=Expand[R4[m,j,ExtGCD[[1]],nA[[m,m]], nA[[j,m]],
            ExtGCD[[2,1]], ExtGCD[[2,2]], nA,x],x]
            ), (Continue[ ])],
             {j,m+1, rows}];
            Return[nA]];            
                       
            
            
PolynomialThirdStep[A_,x_]:=Module[{nA=A,InterchangeQ=False},
                (Do[ ( Do[If[ PolynomialRemainder[ A[[i, j]] ,
                 A[[m,m]] ,x] === 0, 
                (Continue[ ]),
                     (nA=R2[1,i, m,nA];
                     
                     nA=PolynomialEliminateCol[nA,x];
                     
                     InterchangeQ=True;
                      Break[ ]) ],
                     {j, m+1, Dimensions[A][[2]]}]),
                 
                  {i,m+1,Dimensions[A][[1]]}];
                  
                  If[InterchangeQ , 
                  nA= PolynomialEliminateRow[nA,x]
                  ];
                  Return[nA])];             

PolynomialSmithForm[A_,var_] :=Block[ {x,nA=Expand[A,var],
                        rows, cols,MinEntry=0, Loc,
                        ZeroMatrixQ,NonZeroRowQ=True,NonZeroColQ=
                        True},
          (
                
          (* Some Initialization*)
          {rows, cols}= Dimensions[A];
           nA=nA /. var->x;
          
                
           (* Now we start the big loop on m*)
           Do[(
           
          (*We first find the min  non-zero value in the remaining
          principal submatrix*)     
          Loc={m,m};ZeroMatrixQ=True;
          Do[ Which[nA[[i,j]] =!= 0 && ZeroMatrixQ, 
                       (MinEntry=nA[[i,j]];Loc={i,j};
                        ZeroMatrixQ=False), 
                       nA[[i,j]] =!= 0 &&
                        Exponent[nA[[i,j]],x] < Exponent[MinEntry,x],
                       (MinEntry=nA[[i,j]];
                        Loc={i,j} ), 
                       True, Continue[ ] ], 
                      {i,m,rows},{j, m,cols} 
                      ]; 
           If[ZeroMatrixQ,  Break[ ]];  (*If the remaining
           principal submatrix has all zeros we are done*)        
           
           
           (*First Step: Put min value in (m,m) position *)
           
           If[Loc[[1]] != m, nA=R3[m,Loc[[1]],nA] ];
           If[Loc[[2]] != m, nA=C3[m, Loc[[2]],nA]];
           leadcoeff=LeadingCoefficient[nA[[m,m]],x];
           If[leadcoeff != 1, nA=Expand[R1[m,1/leadcoeff,nA],x ]];
           
           (*Second Step:  Eliminate row and column *)
           
           If[ m< Min[rows, cols], (
           
           
           
           While[(Do[(
           If[ nA[[i,m]] =!=0, (NonZeroRowQ=True;Break[ ]), (Continue[ ])]),
           {i,m+1, rows}];
           If[!NonZeroRowQ,
           Do[(If[ nA[[m,j]] =!=0, (NonZeroColQ=True;
           Break[ ]), 
           (Continue[ ])]),
           {j,m+1,cols}]];
           NonZeroRowQ  || NonZeroColQ),
           
           
           If[NonZeroRowQ,nA = PolynomialEliminateRow[nA,x]];
           
           
           nA = PolynomialEliminateCol[ nA,x];
           
           NonZeroRowQ=False;NonZeroColQ=False];
           
           (*Third Step: Make sure m,m entry divides the rest*)
           nA = PolynomialThirdStep[nA,x]
           
       ),
            (
            Which[rows < cols, 
            
           nA = PolynomialEliminateCol[nA,x], 
           rows> cols, 
           nA = PolynomialEliminateRow[nA,x]
           , rows==cols, (
           Break [ ] )])]
                
                
                ),{m,1, Min[rows, cols]}];
                
                Return[nA /. x->var]
                ) 
                ];               

 ExtendedPolynomialEliminateCol[P_,A_,Q_,x_]:=
            Module[{nA=A,nP=P, nQ=Q,ExtGCD},
            
            Do[If[nA[[m,j]] =!= 0,
            (ExtGCD=NormalizedPolynomialExtendedGCD[nA[[m,m]], nA[[m,j]],x ];
            nQ=Expand[C4[m,j,ExtGCD[[1]],nA[[m,m]], nA[[m,j]],
            ExtGCD[[2,1]], ExtGCD[[2,2]], nQ,x],x];
            nA=Expand[C4[m,j,ExtGCD[[1]],nA[[m,m]], nA[[m,j]],
            ExtGCD[[2,1]], ExtGCD[[2,2]], nA,x],x]
            ), (Continue[ ])],
             {j,m+1, cols}];
            Return[{nP,nA,nQ}]];   


            
 
 ExtendedPolynomialEliminateRow[P_,A_,Q_,x_]:=
            Module[{nA=A,nP=P,nQ=Q,ExtGCD},
            
            Do[If[nA[[j,m]] =!= 0,
            (ExtGCD=NormalizedPolynomialExtendedGCD[nA[[m,m]], nA[[j,m]],x ];
            nP=Expand[R4[m,j,ExtGCD[[1]],nA[[m,m]], nA[[j,m]],
            ExtGCD[[2,1]], ExtGCD[[2,2]], nP,x],x];
            nA=Expand[R4[m,j,ExtGCD[[1]],nA[[m,m]], nA[[j,m]],
            ExtGCD[[2,1]], ExtGCD[[2,2]], nA,x],x]
            ), (Continue[ ])],
             {j,m+1, rows}];
            Return[{nP,nA,nQ}]];            
                       
            
            
ExtendedPolynomialThirdStep[P_,A_,Q_,x_]:=Module[{nA=A,nP=P,nQ=Q,
                                                InterchangeQ=False},
                (Do[ ( Do[If[ PolynomialRemainder[ A[[i, j]] ,
                 A[[m,m]] ,x] === 0, 
                (Continue[ ]),
                     ({nA, nP}=Map[R2[1,i, m,#] &, {nA, nP}];
                     
                     {nP,nA, nQ}=ExtendedPolynomialEliminateCol[nP,nA,nQ,x];
                     
                     InterchangeQ=True;
                      Break[ ]) ],
                     {j, m+1, Dimensions[A][[2]]}]),
                 
                  {i,m+1,Dimensions[A][[1]]}];
                  
                  If[InterchangeQ , 
                  {nP,nA, nQ}=ExtendedPolynomialEliminateRow[nP,nA,nQ,x]
                  ];
                  Return[{nP,nA,nQ}])];             

ExtendedPolynomialSmithForm[A_,var_] := Block[ {x,nA=Expand[A,var],
                        rows, cols,MinEntry=0, Loc,
                        ZeroMatrixQ,NonZeroRowQ=True,NonZeroColQ=
                        True},
          (
                
          (* Some Initialization*)
          nA=nA /. var-> x;
          {rows, cols}= Dimensions[A];
           nP=IdentityMatrix[rows];
           nQ=IdentityMatrix[cols];
          
                
           (* Now we start the big loop on m*)
           Do[(
           
          (*We first find the min  non-zero value in the remaining
          principal submatrix *)     
          Loc={m,m};ZeroMatrixQ=True;
          Do[ Which[nA[[i,j]] =!= 0 && ZeroMatrixQ, 
                       (MinEntry=nA[[i,j]];Loc={i,j};
                        ZeroMatrixQ=False), 
                       nA[[i,j]] =!= 0 &&
                        Exponent[nA[[i,j]],x] < Exponent[MinEntry,x],
                       (MinEntry=nA[[i,j]];
                        Loc={i,j} ), 
                       True, Continue[ ] ], 
                      {i,m,rows},{j, m,cols} 
                      ]; 
           If[ZeroMatrixQ,  Break[ ]];  (*If the remaining
           principal submatrix has all zeros we are done*)        
           
           
           (*First Step: Put min value in (m,m) position *)
           
           If[Loc[[1]] != m, (nA=R3[m,Loc[[1]],nA] ;nP=R3[m,Loc[[1]],nP]) ];
           If[Loc[[2]] != m, (nA=C3[m, Loc[[2]],nA];nQ=C3[m, Loc[[2]],nQ])];
           leadcoeff=LeadingCoefficient[nA[[m,m]],x];
           If[leadcoeff != 1, (nP=Expand[R1[m,1/leadcoeff,nP],x ];
           nA=Expand[R1[m,1/leadcoeff,nA],x ])];
           
           (*Second Step:  Eliminate row and column *)
           
           If[ m< Min[rows, cols], (
           
           
           
           While[(Do[(
           If[ nA[[i,m]] =!=0, (NonZeroRowQ=True;Break[ ]), (Continue[ ])]),
           {i,m+1, rows}];
           If[!NonZeroRowQ,
           Do[(If[ nA[[m,j]] =!=0, (NonZeroColQ=True;
           Break[ ]), 
           (Continue[ ])]),
           {j,m+1,cols}]];
           NonZeroRowQ  || NonZeroColQ),
           
           
           If[NonZeroRowQ,{nP,nA,nQ} = ExtendedPolynomialEliminateRow[nP,nA,nQ,x]];
           
           
           {nP,nA,nQ} =ExtendedPolynomialEliminateCol[ nP,nA,nQ,x];
           
           NonZeroRowQ=False;NonZeroColQ=False];
           
           (*Third Step: Make sure m,m entry divides the rest*)
           {nP,nA,nQ} = ExtendedPolynomialThirdStep[nP,nA,nQ,x];
           
       ),
            (
            Which[rows < cols, 
            
           {nP,nA,nQ} = ExtendedPolynomialEliminateCol[nP,nA,nQ,x], 
           rows> cols, 
           {nP,nA,nQ} = ExtendedPolynomialEliminateRow[nP,nA,nQ,x]
           , rows==cols, (
           Break [ ] )])]
                
                
                ),{m,1, Min[rows, cols]}];
                
                Return[{nA, {nP, nQ}} /. x-> var]
                ) 
                ];               

               
  PolynomialInvariantFactors[A_,x_]:=Module[{B=PolynomialSmithForm[A,x]} , 
  
Return[Table[B[[i,i]],{i,1,Min[Dimensions[B]] }]]] 

End[ ] 
EndPackage[ ]





