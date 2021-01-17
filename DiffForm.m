(* :Title: DiffForm.m *)
(* :Context: mTensor` *)
(* :Author: Dal-Ho Park *)
(* :Summary: Manipulation of Differential Forms *)
(* :Package Version: 2020.12 *)
(* :Mathematica Version: 10.4 *)

(********************************************************************)
BeginPackage["mTensor`"]

evalXD::usage = ""

(********************************************************************)
Begin["`Private`"]

(******************** Define differential forms *********************)
(* is oName defined as a differential form? *)
IndexedFormQ[fName_?IndexedOperandQ] := getType[fName] === IndexedFormQ
IndexedFormQ[___] := False

Fdefine[fName_Symbol,                p_Integer?NonNegative, permS_String:""] := Fdefine[fName, ToString[fName], p, permS]
Fdefine[fName_Symbol, prtStr_String, p_Integer?NonNegative, permS_String:""] := defineForm[fName, prtStr, p, permS, {DefaultKind}, If [permS === "", {}, {-1}]]

Fdefine[fNameL:{(_Symbol)..},                        p_Integer?NonNegative, permS_String:""] := Fdefine[fNameL, ToString /@ fNameL, p, permS]
Fdefine[fNameL:{(_Symbol)..}, prtStr_String,         p_Integer?NonNegative, permS_String:""] := Fdefine[fNameL, {prtStr}, p, permS]
Fdefine[fNameL:{(_Symbol)..}, prtStrL:{(_String)..}, p_Integer?NonNegative, permS_String:""] := (
        If [Length[fNameL] =!= Length[prtStrL], Message[Msg::err, "incompatible arguments:", fNameL, "and", prtStrL]; Return[]];
        MapThread[Fdefine[#1, #2, p, permS]&, {fNameL, prtStrL}];
    )

Fdefine[fNameL:{(_Symbol)..}, pL:{(_Integer?NonNegative)..}, permS_String:""] := (
        If [Length[fNameL] =!= Length[pL], Message[Msg::err, "incompatible arguments:", fNameL, "and", pL]; Return[]];
        MapThread[Fdefine[#1, #2, #3, permS]&, {fNameL, ToString /@ fNameL, pL}];

    )
Fdefine[fNameL:{(_Symbol)..}, prtStrL:{(_String)..}, pL:{(_Integer?NonNegative)..}, permS_String:""] := (
        If [Length[fNameL] === Length[prtStrL] === Length[pL],
            MapThread[Fdefine[#1, #2, #3, permS]&, {fNameL, prtStrL, pL}],
        (* else *)
            Message[Msg::err, "different numbers of elements in lists", fNameL, prtStrL, pL]
        ];
    )

(* 주의:
    1. 함수 정의에서 패턴매칭의 순서가 중요함
    2. Fdefine의 첫 번째 인자가 {}이면 fName == List인 경우로 패턴매칭
    3. 따라서 Fdefine을 정의할 때 첫 번째 인자가 List인 경우를 먼저 정의해야 함 *)

(* zero-rank *)
Fdefine[fName_Symbol[],                p_Integer?NonNegative] := Fdefine[fName[], ToString[fName], p]
Fdefine[fName_Symbol[], prtStr_String, p_Integer?NonNegative] := Fdefine[fName, prtStr, p]

(* various shapes *)
Fdefine[fName_Symbol[shapes:((_Symbol)..)], p_Integer?NonNegative]                  := Fdefine[fName[shapes], ToString[fName], p]
Fdefine[fName_Symbol[shapes:((_Symbol)..)], p_Integer?NonNegative, permS_String]    := Fdefine[fName[shapes], ToString[fName], p, permS]

Fdefine[fName_Symbol[shapes:((_Symbol)..)], prtStr_String, p_Integer?NonNegative] :=
    With[{permS = StringJoin @ Take[Alphabet[], Length @ {shapes}]},
        defineForm[fName, prtStr, p, permS, indexKind /@ {shapes}, dnupState /@ {shapes}];
    ]
Fdefine[fName_Symbol[shapes:((_Symbol)..)], prtStr_String, p_Integer?NonNegative, permS_String] := (
        If [permS === "", Message[Msg::err, "incompatible arguments:", {shapes}, "and", "\"\""]; Return[]];
        defineForm[fName, prtStr, p, permS, indexKind /@ {shapes}, dnupState /@ {shapes}];
    )

Fdefine[___] := Message[Fdefine::usage]

(*** Local Functions ***)

defineForm[fName_Symbol, prtStr_String, p_Integer, permS_String, kindL_List, dnupL_List] := (
		With [{nDim = GetDimension[DefaultKind]},
	        If [PositiveIntegerQ[nDim] && p > nDim,
	        	Message[Msg::warn, "degree", p, "exceeds the dimension", nDim];
	            fName[args___] := 0 /; FreePatternQ[{args}],
        	(* else *)
                getDegree[fName] ^= p;
                defineOperand[fName, prtStr, permS, kindL, dnupL, IndexedFormQ]
        	]
		];

        fName/: MakeBoxes[fName, StandardForm] :=
            interpretBox[fName,
                    If [GetRank[fName] === 0,
                        StyleBox[prtStr, FontWeight -> "Bold"],  (* as a Diff. form *)
                    (* else *)
                        prtStr                                   (* as a tensor *)  (* ERROR! *)
                    ]
                ];

        fName/: MakeBoxes[fName[args___], StandardForm] :=
            interpretBox[fName[args],
                If [Length[{args}] === 0,
                    If [GetRank[fName] === 0,
                        StyleBox[prtStr, FontWeight -> "Bold"],  (* as a Diff. form *)
                    (* else *)
                        prtStr                                   (* as a tensor *)  (* ERROR! *)
                    ],
                (* else *)
                    Module[ {idxL},
                        idxL = Transpose[
                            With[ {rc = indexCharSpace[#]}, If [indexKind[#] =!= errorIndex && UpIndexQ[#], rc[[{2, 1}]], rc[[{1, 2}]] ] ]& /@ {args}
                        ];
                        If [Length[{args}] === GetRank[fName],  (* as a Diff. form *)
                            SubsuperscriptBox[StyleBox[prtStr, FontWeight -> "Bold"],
                                              TemplateBox[idxL[[1]], "RowDefault"], TemplateBox[idxL[[2]], "RowDefault"]],
                        (* else *)                             (* as a tensor *)  (* if Length[{args}] =!= getDegree[fName] + GetRank[fName], ERROR! *)
                            SubsuperscriptBox[prtStr, TemplateBox[idxL[[1]], "RowDefault"], TemplateBox[idxL[[2]], "RowDefault"]]
                        ]
                    ]
                ]
            ];
    )

(******************* Operators on Diff. Forms ***********************)

(*** Local Constants ***)
formOpList = {IP, XP, XD, HodgeStar, CoXD}  (* used on freeFormQ *)

(*** interior product ***)
defineOperator[IP, "\[Iota]", LD]

(* rules *)
IP[v_, IP[v_, expr_]]    := 0 /; FreePatternQ[{v, expr}] && vectorNameQ[v] && DegreeForm[expr] >= 2
IP[v_, expr_Plus]        := Map[IP[v, #]&, expr] /; FreePatternQ[{v, expr}]
IP[v_, a_ * expr_]       := a IP[v, expr] /; FreePatternQ[{v, expr}] && ZeroDegreeQ[a] && DegreeForm[expr] >= 1
IP[v_, XP[pre_, post__]] := XP[IP[v, pre], post] + (-1)^DegreeForm[pre] XP[pre, IP[v, post]] /; FreePatternQ[{v, pre, post}] && vectorNameQ[v]

(*** exterior product ***)
defineOperator[XP, "", XP]

(* automatically convert Wedge to XP for diff. forms *)
(* NB: 1) Alias of Wedge is :^: in Notebook environment.
       2) Without the context Global`, the symbol Wedge is in Private in Ver. 4.1
          In Ver. 6, Wedge is in System` *)
If [System`$VersionNumber >= 6.0, Wedge[a_, b__] := XP[a, b] /; FreePatternQ[{a, b}] && !AllTrue[{a, b}, freeFormQ]]

(* for formatting operator XP *)
XP/: MakeBoxes[XP[arg1_, args__], StandardForm] := interpretBox[XP[arg1, args],
        TemplateBox[MakeBoxes[#, StandardForm]& /@ (Flatten @ Fold[List[#1, "\[Wedge]", #2]&, arg1, {args}]), "RowDefault"]
    ]

(* rules *)
XP[expr_]                           := expr /; FreePatternQ[expr]
XP[pre___, expr_Plus,  post___]     := Map[XP[pre, #, post] &, expr] /; FreePatternQ[{pre, expr, post}]
XP[pre___, expr_Times, post___]     := XP[pre, Sequence @@ expr, post] /; FreePatternQ[{pre, expr, post}]
XP[pre___, XP[args__], post___]     := XP[pre, args, post] /; FreePatternQ[{pre, args, post}]
XP[]                                := 1
XP[pre___, a_, post___]             := a * XP[pre, post] /; FreePatternQ[{pre, a, post}] && ZeroDegreeQ[a]
XP[args__]                          := 0 /; FreePatternQ[{args}] && PositiveIntegerQ[GetDimension[DefaultKind]]  \
                                            && (Plus @@ Map[DegreeForm, {args}]) > GetDimension[DefaultKind]
XP[pre___, a_, mid___, a_, post___] := 0 /; FreePatternQ[{pre, a, mid, post}] && OddQ[DegreeForm[a]]
XP[args__]                          :=
    Module[ {fL = {args}, rcL = {}, sign = 1, i},
        For [i = Length[fL], i >= 1, --i,
            rcL = exteriorProduct[fL[[i]], rcL];
            If [rcL[[1]] === 0, Return[0]];

            sign *= rcL[[1]]; rcL = rcL[[2]]
        ];

        sign * XP[Sequence @@ rcL]
    ] /; FreePatternQ[{args}] && !OrderedQ[{args}, formOrderedQ]

    (* return {sign, fL}. fL is sorted *)
    exteriorProduct[aF_, {}]      := {1, {aF}}
    exteriorProduct[aF_, fL_List] := (* insert aF to fL and sort in accending order. return {sign, rcFL} *)
        Module[ {rcFL = fL, aDeg, bDeg, rcDeg = 0, i},
            aDeg = DegreeForm[aF];
            Do [
                bDeg = DegreeForm @ fL[[i]];

                (* if ordered, insert *)
                If [formOrderedWithQ[aF, aDeg, fL[[i]], bDeg],
                    rcFL = Insert[fL, aF, i]; Break[]
                ];

                rcDeg += bDeg,

               {i, Length[fL]}
            ];

            If [rcFL === fL, rcFL = Append[fL, aF]];
            {(-1)^(aDeg * rcDeg), rcFL}
        ]

(*** exterior derivative ***)
defineOperator[XD, "d", XD]

(* rules *)
XD[expr_Plus]  := Map[XD, expr] /; FreePatternQ[expr]
XD[a_ * b_]   := XP[XD[a], b] + XP[a, XD[b]] /; FreePatternQ[{a, b}]
XD[XD[expr_]] := 0 /; FreePatternQ[expr]
XD[XP[fs__]]  :=
    Module[ {fL = {fs}, rc = 0, deg, rcDeg = 0, i},
        If [PositiveIntegerQ[GetDimension[DefaultKind]],
            If [DegreeForm[XP[fs]] >= GetDimension[DefaultKind], Return[0]] (* when p > Dimension *)
        ];

        Do [
            deg = DegreeForm[fL[[i]]];
            If [Head[fL[[i]]] =!= XD, rc += (-1)^(rcDeg * deg) XP[XD[fL[[i]]], XP[Sequence @@ Drop[fL, {i}]]]];
            rcDeg += deg,
            {i, Length[fL]}
        ];
        rc
    ] /; FreePatternQ[{fs}]
XD[fName_Symbol]    := XD[fName[]] /; FreePatternQ[fName] && IndexedFormQ[fName]
XD[fName_[args___]] := 0 /; FreePatternQ[{fName, args}]                                               \
                            && ( IndexedFormQ[fName] && (PositiveIntegerQ[GetDimension[DefaultKind]]  \
                                 && DegreeForm[fName[args]] >= GetDimension[DefaultKind]) )
XD[c_?constantQ]    := 0

LD[v_, XP[fs__]] :=
    Module[{rcL},
        rcL = Map[LD[v, #]&, {fs}];
        Sum[ReplacePart[XP[fs], i -> rcL[[i]]], {i, 1, Length[{fs}]}]
    ]

LDtoXDRule[] = {
        LD[v_, aF_] :> IP[v, XD[aF]] + XD[IP[v, aF]] /; FreePatternQ[{v, aF}] && vectorNameQ[v] && !freeFormQ[aF]
    }

(*** HodgeStar ***)
defineOperator[HodgeStar, "*", XD]

(* rules *)
HodgeStar[expr_Plus]        := Map[HodgeStar, expr] /; FreePatternQ[expr]
HodgeStar[HodgeStar[expr_]] :=
    With[{n = GetDimension[DefaultKind], s = GetSignature[DefaultKind], p = DegreeForm[expr]},
        (-1)^((n-s)/2 + p*(n-p)) * expr /; FreePatternQ[expr]
    ]
HodgeStar[s_. * expr_]      := -HodgeStar[Abs[s] * expr] /; FreePatternQ[{s, expr}] && Negative[s]

(*** CoXD ***)
defineOperator[CoXD, "\[Delta]", XD]

(* rules *)
CoXD[expr_Plus]   := Map[CoXD, expr] /; FreePatternQ[expr]
CoXD[CoXD[expr_]] := 0 /; FreePatternQ[expr]
CoXD[expr_]       := 0 /; FreePatternQ[expr] && ZeroDegreeQ[expr]
CoXD[s_. * expr_] := -CoXD[Abs[s] * expr] /; FreePatternQ[{s, expr}] && Negative[s]

CoXDRule[] = {
        CoXD[expr_] :>
            With[{n = GetDimension[DefaultKind], s = GetSignature[DefaultKind], p = DegreeForm[expr]},
                (-1)^((n-s)/2 + n(p-1) + 1) HodgeStar[XD[HodgeStar[expr]]]
            ]
    }

(* apply XD to an expr *)
ApplyXD[expr_List] := Map[ApplyXD, expr] /; FreePatternQ[expr]
ApplyXD[expr_]     :=
	With[{rcExpr = expandObject[expr]},
		If [Head[rcExpr] === Plus, applyXDTerm /@ rcExpr, applyXDTerm[rcExpr]]
	] /; VectorQ[tCoordinates[DefaultKind]]
ApplyXD[expr__] := XD[expr]

	applyXDTerm[term_] :=
		Module[{ordTerm, fTerm},
			{ordTerm, fTerm} = splitForm[term];
			Plus @@ ((BD[#, ordTerm] * XP[XD[#], fTerm])& /@ tCoordinates[DefaultKind])	+ ordTerm * XD[fTerm]
		]

CollectForm[expr_, opts___] :=
    Module[{rcExpr = expandObject[expr, opts], posL, i, j},
        If [Head[rcExpr] === Plus,
            rcExpr = Append[#, False]& /@ splitForm /@ (List @@ rcExpr);  (* {{ord, form, False} ..} *)
            Do [
                posL = Position[rcExpr[[i+1 ;; -1]], rcExpr[[i,2]]][[All,1]] + i;
                Do [
                    If [rcExpr[[posL[[j]],3]] =!= True, rcExpr[[i,1]] += rcExpr[[posL[[j]],1]]];
                    rcExpr[[posL[[j]],3]] = True,  (* mark *)
                    {j, Length[posL]}
                ],
                {i, Length[rcExpr]}
            ];
            rcExpr = (#[[1]] * #[[2]])& /@ Select[rcExpr, (#[[3]] =!= True)&];  (* {ord * form, ..} *)
            $PROTECTEXPANDING[Plus @@ rcExpr],
        (* else *)
            rcExpr
        ]
    ]

(* return degree of a form *)
DegreeForm[fName_Symbol]     := If [GetRank[fName] =!= 0,              0, getDegree[fName]] /; IndexedFormQ[fName]
DegreeForm[fName_[args___]]  := If [GetRank[fName] =!= Length[{args}], 0, getDegree[fName]] /; IndexedFormQ[fName]
DegreeForm[XD[expr_]]        := 1 + DegreeForm[expr]
DegreeForm[XP[args__]]       := Plus @@ Map[DegreeForm, {args}]
DegreeForm[LD[v_, expr_]]    := DegreeForm[expr]
DegreeForm[IP[v_, expr_]]    := DegreeForm[expr] - 1
DegreeForm[HodgeStar[expr_]] := GetDimension[DefaultKind] - DegreeForm[expr]
DegreeForm[CoXD[expr_]]      := DegreeForm[expr] - 1
DegreeForm[expr_Times]       := Plus @@ Map[DegreeForm, List @@ expr]
DegreeForm[___]              := 0

(* is expr zero-form or non-form? *)
ZeroDegreeQ[fName_Symbol]     := DegreeForm[fName]       === 0 /; IndexedFormQ[fName]
ZeroDegreeQ[fName_[args___]]  := DegreeForm[fName[args]] === 0 /; IndexedFormQ[fName]
ZeroDegreeQ[XD[_]]            := False
ZeroDegreeQ[XP[args__]]       := False  (* label args is required!! Is it a BUG? *)
ZeroDegreeQ[LD[v_, expr_]]    := ZeroDegreeQ[expr]
ZeroDegreeQ[IP[v_, expr_]]    := DegreeForm[expr] === 1
ZeroDegreeQ[HodgeStar[expr_]] := DegreeForm[expr] === GetDimension[DefaultKind]
ZeroDegreeQ[CoXD[expr_]]      := DegreeForm[expr] === 1
ZeroDegreeQ[expr_]            := True   (* non-form or function of zero-form *)

(***** Local Functions *****)

(* ordered by degree *)
formOrderedQ[aF_, bF_] := formOrderedWithQ[aF, DegreeForm[aF], bF, DegreeForm[bF]]

formOrderedWithQ[_,               aDeg_, _,               bDeg_] := True  /; aDeg < bDeg
formOrderedWithQ[_,               aDeg_, _,               bDeg_] := False /; aDeg >  bDeg
formOrderedWithQ[fName_,          _,     XD[_],           _]     := False /; IndexedFormQ[fName]
formOrderedWithQ[fName_[___],     _,     XD[_],           _]     := False /; IndexedFormQ[fName]
formOrderedWithQ[XD[_],           _,     fName_,          _]     := True  /; IndexedFormQ[fName]
formOrderedWithQ[XD[_],           _,     fName_[___],     _]     := True  /; IndexedFormQ[fName]
formOrderedWithQ[fName_[args___], _,     fName_[brgs___], _]     := IndexOrderedQ[{args}, {brgs}] /; IndexedFormQ[fName]
formOrderedWithQ[op_[aF_],        _,     op_[bF_],        _]     := formOrderedQ[aF, bF] /; MemberQ[formOpList, op]
formOrderedWithQ[aName_[___],     _,     bName_[___],     _]     := OrderedQ[{aName, bName}]
formOrderedWithQ[aF_,             _,     bF_,             _]     :=
	If [VectorQ[tCoordinates[DefaultKind]] && SubsetQ[tCoordinates[DefaultKind], {aF, bF}],  (* Ordering with the coordinate systems *)
		Position[tCoordinates[DefaultKind], aF][[1,1]] <= Position[tCoordinates[DefaultKind], bF][[1,1]],
	(* else *)
		OrderedQ[{aF, bF}]
	]

freeFormQ[LD[aV_?vectorNameQ, expr_]] := freeFormQ[expr]  (* LD is both the tensor and the diff. form operator *)
freeFormQ[fname_?IndexedFormQ]        := False
freeFormQ[expr_]                      := freeObjectQ[expr, HeadQs -> {(IndexedFormQ[#] || MemberQ[formOpList, #])&}]
freeFormQ[___]                        := True

splitForm[term_Times]      := Times @@ Map[splitForm, List @@ term]
splitForm[fName_[args___]] := If [GetRank[fName] =!= Length[{args}], {fName[args], 1}, {1, fName[args]}] /; IndexedFormQ[fName]  (* cover fname[components] *)
splitForm[fOp_[arg_]]      := {1, fOp[arg]} /; MemberQ[formOpList, fOp]
splitForm[term_]           := {1, term} /; !freeFormQ[term]  (* cover fname *)
splitForm[expr_]           := {expr, 1}

(***** ToTensor *****)

ToTensor[expr_Equal, arg_]                                  := ToTensor[#, arg]& /@ expr
ToTensor[expr_, {}]                                         := toTensor[Dum @ expr, {}]
ToTensor[expr_, indexL:{(_Symbol | _String | _Integer) ..}] := toTensor[Dum @ expr, indexL] /; DeleteDuplicates[indexKindProper /@ indexL] === {DefaultKind}
ToTensor[___] := Message[ToTensor::usage]

    toTensor[expr_, indexL_List] :=
        Module[{rcExpr = expandObject[expr], term, freeL},
            If [!FreeQ[rcExpr, HodgeStar],
                If [!PositiveIntegerQ[GetDimension[DefaultKind]], Message[Msg::err, "Need to SetDimension[]","", "", ""]; Return[]]
            ];
            If [PositiveIntegerQ[GetDimension[DefaultKind]],
                If [Length[indexL] > GetDimension[DefaultKind], Message[Msg::err, "Invalid numbers of indices: ", indexL, "", ""]; Return[]]
            ];

            If [Head[rcExpr] === Plus, term = rcExpr[[1]], term = rcExpr];
            freeL = findFreeIndicesAll[term, IndexQs -> {KindIndexQ[DefaultKind]}];  (* all free indices of the "term" (including non-zero rank diff. forms *)
            If [Intersection[Join[freeL, FlipIndex /@ freeL], indexL] =!= {},
                Message[Msg::err, "invalid indices: ", indexL, "for free indices", freeL]; Return[]
            ];
            If [PositiveIntegerQ[GetDimension[DefaultKind]],
                If [Length[freeL]  > GetDimension[DefaultKind], Message[Msg::err, "Invalid numbers of free indices: ", freeL, "", ""]; Return[]]
            ];

            If [Head[rcExpr] === Plus, toTensorTerm[#, indexL]& /@ rcExpr, toTensorTerm[rcExpr, indexL]]
        ]

        toTensorTerm[term_, indexL_] :=
            Module[{ordTerm, oTerm, rcL, findexL, i, p},
            {ordTerm, oTerm} = splitForm[term];
            If [oTerm === 1, Return[term]];

            If [DegreeForm[oTerm] =!= Length[indexL], Message[Msg::err, "invalid number of indices", indexL, "for", oTerm]; Return[]];

            rcL = If [Head[oTerm] === Times, List @@ oTerm, List[oTerm]];  (* {A1, A2, ...} *)
            findexL = indexL;
            Do [ (* for each forms in the term *)
                p = DegreeForm[rcL[[i]]];
                rcL = ReplacePart[rcL, i -> f2tObject[rcL[[i]], Take[findexL, p]]];  (* update rcL *)
                findexL = Drop[findexL, p],                                          (* update findexL *)
                {i, Length[rcL]}
            ];
            ordTerm * (Times @@ rcL)
        ]

    f2tObject[fName_Symbol,    indexL_] := fName[Sequence @@ indexL]       /; IndexedFormQ[fName]
    f2tObject[fName_[args___], indexL_] := fName[Sequence @@ indexL, args] /; IndexedFormQ[fName]
    f2tObject[XD[expr_],       indexL_] :=
        Module[{op = If[TorsionFreeQ[CD] && flagTable[XDtoCDfrag], CD, BD]},
            Length[indexL] * (TindexSort @ AntisymmetrizeIndices[indexL, op[First @ indexL, ToTensor[expr, Drop[indexL, 1]]]])
        ]
    f2tObject[XP[args__],      indexL_] :=
        Module[{rcL = {args}, findexL = indexL, ip, i},
            Do [
                ip = DegreeForm[rcL[[i]]];
                rcL = ReplacePart[rcL, i -> (1/Factorial[ip]) * ToTensor[rcL[[i]], Take[findexL, ip]]];  (* update rcL *)
                findexL = Drop[findexL, ip],                                                             (* update findexL *)
                {i, Length[rcL]}
            ];
            Factorial[Length @ indexL] * TindexSort @ AntisymmetrizeIndices[indexL, Times @@ rcL]
        ]
    f2tObject[LD[v_, f_],      {}]      := With[{pair = DummyPair[]}, v[pair[[2]]] CD[pair[[1]], f]] /; vectorNameQ[v] && ZeroDegreeQ[f]
    f2tObject[LD[v_, expr_],   indexL_] := LD[v, ToTensor[expr, indexL]] /; indexL =!= {}
    f2tObject[IP[v_, expr_],   indexL_] :=
        Module[{pair = DummyPair[], findexL},
            findexL = Prepend[indexL, pair[[1]]];
            v[pair[[2]]] * (TindexSort @ AntisymmetrizeIndices[findexL, ToTensor[expr, findexL]])  (* NB: f2tObject but not "ToTensor" *)
        ]
    f2tObject[HodgeStar[expr_], indexL_] :=
        Module[{n = GetDimension[DefaultKind], p, dnL, upL},
            If [!PositiveIntegerQ[n], Message[Msg::err, "Need to SetDimension[]","", "", ""]; Return[HodgeStar[expr]]];

            p = DegreeForm[expr];
            If [Length[indexL] =!= n - p, Message[Msg::err, "invalid number of indices", indexL, "for", HodgeStar[expr]]; Return[]];

            If [p === 0,
                DualStar[ToTensor[expr, {}], indexL],
            (* else *)
                {dnL, upL} = Transpose@Table[DummyPair[], p];
                DualStar[ToTensor[expr, dnL], Join[upL, indexL]]
            ]
        ]
    f2tObject[CoXD[expr_],     indexL_] :=
        With[{pair = DummyPair[]},
            -CD[pair[[2]], ToTensor[expr, Prepend[indexL, pair[[1]]]]]
        ]
    f2tObject[expr_, _, _] := expr

(***** CoordRep *****)

CoordRep[form_, coSys_List] :=
    With[{p = DegreeForm[form], n = Length[coSys]},
        If [p == 0 || n == 0, form, coordRep[form, p, n, coSys]]
    ]

CoordRep[form_, n_:GetDimension[Latin]] :=
    With[{p = DegreeForm[form]},
        If [p == 0,
            form,
        (* else *)
            If [!PositiveIntegerQ[n],
                Message[Msg::err, "Dimension", n, "is required to be a positive integer!", ""];
                form,
            (* else *)
                coordRep[form, p, n]
            ]
        ]
    ]

    coordRep[form_, p_, n_, coSys_:{}] :=
        Module[{pairL = Table[DummyPair[Latin], {p}], rc},
            If [!IndexedFormQ[coordX],
                (* Fdefine[coordX[ua], 0] *)
                getDegree[coordX] ^= 0;
                defineOperand[coordX, "x", "a", {Latin}, {1}, IndexedFormQ]
            ];
            
            If [coSys === {},
                clearComponents[coordX, 1, {n}, {+1}],
            (* else *)
                (* SetComponents[coordX[ua], coSys] *)
                tableToComponents[coordX, 1, {+1}, coSys]
            ];

            rc = (1/p!) ToTensor[form, #[[1]]& /@ pairL] ( XP @@ (XD /@ coordX /@ (#[[2]]& /@ pairL)) );
            CollectForm @ TindexSort @ (SumDum[{1, n}, rc, Latin])
        ]

Unprotect[Off]  (* turn off a flag *)
Off[XDtoCDfrag] := (flagTable[XDtoCDfrag] = False;)
Protect[Off]

Unprotect[On]  (* turn on a flag *)
On[XDtoCDfrag] := (flagTable[XDtoCDfrag] = True;)
Protect[On]

(********************************************************************)

initForm[] := (
        (***** Flag Table *****)
        flagTable[XDtoCDfrag] = True;

        (***** Predefined Operators *****)
        reservedNameList = Join[reservedNameList, {IP, HodgeStar, CoXD}];

        (***** Finish initForm *****)
        reservedNameList = DeleteDuplicates[reservedNameList];
    )
initForm[]

End[ ] (* end the private context *)

EndPackage[ ]  (* end the package context *)

(********************************************************************)
