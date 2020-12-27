(* :Author: Dal-Ho Park *)
(* :Summary: Manipulating indexed tensors in Mathematica *)
(* :Package Version: 2020.12 *)
(* :Mathematica Version: 10.4 *)

(********************************************************************)
BeginPackage["mTensor`", {"mTensor`xPermML`"}]

(********************************************************************)
Begin["`Private`"]

(********************** Predefined Structures ***********************)

(***** generic rules of linear derivative operators *****)

derivativeRules[derD_Symbol, argCheck_:(True&)] := (
        (* update definedDerivativeList for Absorb of Kronecka Delta *)
        definedDerivativeList = DeleteDuplicates @ Append[definedDerivativeList, derD];

        derD[arg_, expr_Plus]  := Map[derD[arg, #]&, expr] /; FreePatternQ[{arg, expr}] && argCheck[arg];  (* Linear *)
        derD[arg_, expr_Times] :=                                                                          (* Leibnitz rule *)
            Module[ {expd = expandObject[expr], rcL},
                Switch [Head[expd],
                    Plus,  Map[derD[arg, #]&, expd],
                    Times, rcL = Map[derD[arg, #]&, List @@ expd];
                           Sum[ReplacePart[expd, i -> rcL[[i]]], {i, 1, Length[expd]}],
                    _,     derD[arg, expd]
                ]
            ] /; FreePatternQ[{arg, expr}] && argCheck[arg];
        derD[arg_, c_?constantQ] := 0 /; FreePatternQ[{arg, c}] && argCheck[arg];                          (* Derivation *)

        (* derD[_, Kronecka Delta] --> 0 *)
        derD[arg_, Kdelta[a_, b_]] := 0 /; FreePatternQ[{arg, a, b}] && !upupdndnIndexQ[{a, b}]  \
                                           && Switch [getType[derD],
                                                  CD, ValidIndicesQ[{arg, a, b}, KindOf[derD, arg]],
                                                  LD, If [derD === LD, vectorNameQ[arg] && ValidIndicesQ[{a,b}, KindOf[derD, arg]],
                                                      (* else *)       ValidIndicesQ[{a, b}, KindOf[derD, arg]]],
                                                  _,  False
                                              ];

        (* Scalar functions *)
        derD[arg_, sf_?ScalarFunctionQ[expr_]] := sf'[expr] * derD[arg, DumFresh[expr]] /; sf =!= Tscalar;
        derD[arg_, Power[expr1_, expr2_]]      := DumFresh[expr2] * Power[expr1, expr2 - 1] * derD[arg, DumFresh[expr1]]
                                                  + Power[expr1, expr2] * Log[DumFresh[expr1]] * derD[arg, DumFresh[expr2]];
    )

(***** Covariant Structure *****
	(* derOp's properties *)
    TorsionFreeQ[derOp]      = True | False
    getDerOp[Gamma][derOp]   = SymbolJoin[Gamma,   derOp];
    getDerOp[Ricci][derOp]   = SymbolJoin[Ricci,   derOp];
    getDerOp[Riemann][derOp] = SymbolJoin[Riemann, derOp];
    getDerOp[Scalar][derOp]  = SymbolJoin[Scalar,  derOp];
    getDerOp[Weyl][derOp]    = SymbolJoin[Weyl,    derOp];

	(* kind's properties *)
    MetricSpaceQ[kind]    = True | False
    constantMetricQ[kind] = False | True

    getDerOps[kind]     = {derOp,...}  <-- derivative operators
    GetDimension[kind]
    GetEpsilon[kind]    = Epsilon or SymbolJoin[Epsilon, kind]
    GetMetric[kind]     = metric       <-- unique metric
    GetSignature[kind]
    GetStructuref[kind] = Structuref or SymbolJoin[Structuref, kind]
    GetTorsion[kind]    = Torsion or SymbolJoin[Torsion, kind]

    tCoordinates[kind]
	tCoordinatesStr[kind]
    basisMatrix[kind]

	(* metric's properties *)
    MetricQ[metric]           = True | False
    getCovDs[metric]          = {torFreeCovD, torCovD}  <-- unique (up to torsion) metric-compatible covDs
    getMetricSymmetry[metric] = +1|-1

	In DefaultKind, CD is the torsion-free CovD compatible with the symmetric-metric Metricg.
 *****)

(* is defined by DefineDerivativeOperator? *)
DerivativeOperatorQ[opName_Symbol?IndexedOperatorQ] := MemberQ[getDerOps[KindOf @ opName], opName]
DerivativeOperatorQ[___]                            := False

(* define a derivative operator *)
Options[DefineDerivativeOperator] = {TorsionFreeQ -> True}
DefineDerivativeOperator[derOp_Symbol,                             opts___Rule] := DefineDerivativeOperator[derOp, ToString[derOp], DefaultKind, opts]
DefineDerivativeOperator[derOp_Symbol, prtStr_String,              opts___Rule] := DefineDerivativeOperator[derOp, prtStr, DefaultKind, opts]
DefineDerivativeOperator[derOp_Symbol, prtStr_String, kind_Symbol, opts___Rule] := (
        If [!checkName[derOp], Return[]];
        If [!checkIndexKind[kind, True], Return[]];

        defineDerOp[derOp, prtStr, kind, opts];
    )
DefineDerivativeOperator[___] := Message[DefineDerivativeOperator::usage]

defineDerOp[derOp_Symbol, prtStr_String, kind_, opts___] :=
    With[ {oldKind = KindOf[derOp]},
        (* update oldKind's getDerOps property *)
        If [oldKind =!= kind,
            If [derOp =!= CD && DerivativeOperatorQ[derOp],
                getDerOps[oldKind] = DeleteCases[getDerOps[oldKind], derOp];
            ]
        ];

        (* update kind's getDerOps property *)
        getDerOps[kind] = DeleteDuplicates @ Append[getDerOps[kind], derOp];

        (* define CD-type operator *)
        defineOperator[derOp, prtStr, CD, kind];

        (* options *)
		TorsionFreeQ[derOp] = TorsionFreeQ /. {opts} /. Options[DefineDerivativeOperator];

        (* joined symbols *)
        getDerOp[Gamma]  [derOp] = SymbolJoin[Gamma,   derOp];
        getDerOp[Ricci]  [derOp] = SymbolJoin[Ricci,   derOp];
        getDerOp[Riemann][derOp] = SymbolJoin[Riemann, derOp];
        getDerOp[Scalar] [derOp] = SymbolJoin[Scalar,  derOp];
        getDerOp[Weyl]   [derOp] = SymbolJoin[Weyl,    derOp];

        (* define tensors having the joined-names *)
        defineOperand[getDerOp[Gamma][derOp], prtStrJoinDerOp["\[CapitalGamma]", derOp],
        	          If [CoordinateBasisQ[kind] && TorsionFreeQ[derOp], "+bac", "abc"],  (* symmetric or no-symmetry *)
        	          {kind}, {-1, -1, +1}];
        If [TorsionFreeQ[derOp],
            defineOperand[getDerOp[Ricci][derOp],   prtStrJoinDerOp["R", derOp], "+ba",             {kind}, {-1}];  (* symmetric *)
            defineOperand[getDerOp[Riemann][derOp], prtStrJoinDerOp["R", derOp], "-bacd-abdc+cdab", {kind}, {-1}];
            defineOperand[getDerOp[Weyl][derOp],    prtStrJoinDerOp["C", derOp], "-bacd-abdc+cdab", {kind}, {-1}],
        (* else *)
            defineOperand[getDerOp[Ricci][derOp],   prtStrJoinDerOp["R", derOp], "ab",         {kind}, {-1}];  (* no symmetry *)
            defineOperand[getDerOp[Riemann][derOp], prtStrJoinDerOp["R", derOp], "-bacd-abdc", {kind}, {-1}];
            defineOperand[getDerOp[Weyl][derOp],    prtStrJoinDerOp["C", derOp], "-bacd-abdc", {kind}, {-1}];
        ];
        defineOperand[getDerOp[Scalar][derOp], prtStrJoinDerOp["R", derOp], "", {kind}, {}];

        (* update non-tensors *)
        nonTensorList = DeleteDuplicates @ Append[nonTensorList, getDerOp[Gamma][derOp]];

        (* Rules for symbol-joined tensors *)
        With [{kkind = If [derOp === CD, DefaultKind, kind]},  (* delayed evaluation for the DefaultKind *)
            getDerOp[Riemann][derOp][a_, b_, c_, d_] :=  getDerOp[Ricci][derOp][b,d] /; FreePatternQ[{a, b, c, d}] && ValidIndexQ[a, kkind] && PairIndexQ[a,c];
            getDerOp[Riemann][derOp][a_, b_, c_, d_] := -getDerOp[Ricci][derOp][b,c] /; FreePatternQ[{a, b, c, d}] && ValidIndexQ[a, kkind] && PairIndexQ[a,d];
            getDerOp[Riemann][derOp][a_, b_, c_, d_] := -getDerOp[Ricci][derOp][a,d] /; FreePatternQ[{a, b, c, d}] && ValidIndexQ[b, kkind] && PairIndexQ[b,c];
            getDerOp[Riemann][derOp][a_, b_, c_, d_] :=  getDerOp[Ricci][derOp][a,c] /; FreePatternQ[{a, b, c, d}] && ValidIndexQ[b, kkind] && PairIndexQ[b,d];
            getDerOp[Ricci]  [derOp][a_, b_]         :=  getDerOp[Scalar][derOp][]   /; FreePatternQ[{a, b}]       && ValidIndexQ[a, kkind] && PairIndexQ[a,b]
        ];

        (* Rules for the derOp *)
        derivativeRules[derOp];
        derOp[opIndex_, moreIndices__, expr_] := Fold[derOp[#2, #1]&, expr, Reverse[{opIndex, moreIndices}]] /; FreePatternQ[{opIndex, moreIndices, expr}];
    ]

prtStrJoinDerOp[prtStr_String, CD]           := prtStr                                    (* predefined covariant derivative *)
prtStrJoinDerOp[prtStr_String, derOp_Symbol] := prtStr <> "[" <> getPrtStr[derOp] <> "]"  (* symbol-joining covariant derivative *)

RemoveDerivativeOperator[derOp_Symbol?DerivativeOperatorQ] :=
    With[ {kind = KindOf[derOp]},
        (* protect CD *)
        If [MemberQ[reservedNameList, derOp], Message[Msg::err, "Reserved name", derOp, "cannot be removed!", ""]; Return[]];

		If [MetricSpaceQ[kind],
		    With[ {metric = GetMetric[kind]},
		        If [covariantNameQ[derOp, metric],
        	       Message[Msg::warn, derOp, "was a member of metric-compatible derivatives of", metric, ""];
        	       ClearMetricConnection[derOp, metric]
		        ]
		    ]
        ];

        (* update definedDerivativeList for Kdelta *)
        definedDerivativeList = DeleteCases[definedDerivativeList, derOp];

        (* update non-tensors *)
        nonTensorList = DeleteCases[nonTensorList, getDerOp[derOp, Gamma]];

        (* remove symbol-joined tensors *)
        removeObject @ getDerOp[Gamma]  [derOp];
        removeObject @ getDerOp[Ricci]  [derOp];
        removeObject @ getDerOp[Riemann][derOp];
        removeObject @ getDerOp[Scalar] [derOp];
        removeObject @ getDerOp[Weyl]   [derOp];

        (* update kind's getDerOps property *)
        getDerOps[kind] = DeleteCases[getDerOps[kind], derOp];

		(* remove derOp *)
        removeObject[derOp];
    ]
RemoveDerivativeOperator[___] := Message[RemoveDerivativeOperator::usage]

(* define an unique metric for each kind *)
DefineMetric[metric_Symbol,                             sym_Integer:+1] := DefineMetric[metric, ToString[metric], DefaultKind, sym]
DefineMetric[metric_Symbol,                kind_Symbol, sym_Integer:+1] := DefineMetric[metric, ToString[metric], kind, sym]
DefineMetric[metric_Symbol, prtStr_String,              sym_Integer:+1] := DefineMetric[metric, prtStr, DefaultKind, sym]
DefineMetric[metric_Symbol, prtStr_String, kind_Symbol, sym_Integer:+1] := (
        If [!checkName[metric], Return[]];
        If [!checkIndexKind[kind, True], Return[]];
        If [!MemberQ[{+1, -1}, sym],
            Message[Msg::err, "Either symmetric (+1) or anti-symmetric (-1) is required, but not", sym, ".", ""]; Return[]
        ];

        (* Protect Metricg *)
        If [flagTable[MetricgFlag] && kind === DefaultKind,
            Message[Msg::err, "Use On[MetricgFlag] or Off[MetricgFlag] to change the metric state of DefaultKind", kind, "", ""]; Return[]
        ];

        defineMetric[metric, prtStr, If [sym === -1, "-ba", "+ba"], kind];
    )
DefineMetric[___] := Message[DefineMetric::usage]

defineMetric[metric_Symbol, prtStr_String, permS_String, kind_Symbol] := (
        (* define metric as a tensor and then check its rank *)
        defineOperand[metric, prtStr, permS, {kind}, {-1}];
        If [!IndexedTensorQ[metric], Return[]];  (* errors in defineOperand *)
        If [GetRank[metric] =!= 2,
        	Message[Msg::err, metric, "is not rank-2 tensor", "", ""]; removeObject[metric]; Return[]
        ];

        (* setup for MetricSpaceQ and GetMetric *)
        MetricSpaceQ[kind] = True;    (* unique metric for each kind *)
        GetMetric[kind]    = metric;

        (**** setup properties of metric *****)

        (* setup metric symmetry *)
        getMetricSymmetry[metric] =
            Switch [GetSymmetry[metric],
                GenSet[{Cycles[{{1,2}}],-1}], -1,
                "Antisymmetric",              -1,
                GenSet[{Cycles[{{1,2}}],+1}], +1,
                "Symmetric",                  +1,
                _,                            +1   (* default *)
            ];

        (* Rules. NB: If the metric is anti-symmetric, Kdelta is also anti-symmetric! *)
        If [metric === Metricg, (* The kind of Metricg is always DefaultKind. NB: delayed evaluation of DefaultKind *)
           	metric[a_, b_] := Kdelta[a, b] /; flagTable[KdeltaFlag] && FreePatternQ[{a, b}] && AllTrue[{a, b}, TensorialIndexQ] \
               	                              && !upupdndnIndexQ[{a, b}] && ValidIndicesQ[{a, b}, DefaultKind],
		(* else *)
           	metric[a_, b_] := Kdelta[a, b] /; flagTable[KdeltaFlag] && FreePatternQ[{a, b}] && AllTrue[{a, b}, TensorialIndexQ] \
                                        	  && !upupdndnIndexQ[{a, b}] && ValidIndicesQ[{a, b}, kind]
        ];

		MetricQ[metric]  = True;
		getCovDs[metric] = {};
    )

RemoveMetric[metric_Symbol?MetricQ] :=
	With [{kind = KindOf[metric]},
        If [(metric =!= Metricg && MemberQ[reservedNameList, metric]) || (metric === Metricg && flagTable[MetricgFlag]),
            Message[Msg::err, "RemoveMetric:", "Reserved name", metric, "cannot be removed!"]; Return[]
        ];

		(* un-set kind's properties related with the metric *)
		MetricSpaceQ[kind] = False;
        GetMetric[kind]    = Null;  (* Don't Unset *)

        (**** un-set properties of metric *****)

       	(* unlink from the metric-compatible covDs *)
		clearMetricCompatible[#, metric, kind]& /@ getCovDs[metric];
		getCovDs[metric] = {};

		MetricQ[metric] = False;
        getMetricSymmetry[metric] = .;

        If [metric === Metricg,  (* if called from Off[MetricgFlag], *)
            ClearAll @ Metricg,  (* remove all values associated with Metricg *)
        (* else *)
            removeObject @ metric
        ];
   	]

(* add metric-compatible derivatives *)
MakeMetricConnection[BD,                        metric_?MetricQ] := makeMetricConnection[BD, metric, KindOf[metric]]
MakeMetricConnection[covD_?DerivativeOperatorQ, metric_?MetricQ] :=
	With [{kind = KindOf[metric]},
		If [!kindMatchQ[kind, KindOf[covD]], Message[Msg::err, "Non-compatible kinds of", covD, "and", metric]; Return[]];
        If [covariantNameQ[covD, metric], Return[]];

        (* NB: The metric-compatible covDs should be unique, up to the torsion. (See Wald, Theorem 3.1.1 for torsion-free and coordinate-basis)
           When TorsionFreeQ[covD1] = True and TorsionFreeQ[covD2] = False, getCovDs[metric] === {covD1, covD2}
        If [Or @@ ((#[[2]] >= 2)& /@ Tally[TorsionFreeQ /@ getCovDs[metric]]),
            Message[Msg::err, "TorsionFreeQ of", covD, "is", TorsionFreeQ[covD], "and that type of a derivative is already included."];
            getCovDs[metric] = DeleteCases[getCovDs[metric], covD];  (* restore *)
            Return[]
        ]; *)

        makeMetricConnection[covD, metric, kind];
    ]
MakeMetricConnection[___] := Message[MakeMetricConnection::usage]

    makeMetricConnection[covD_, metric_, kind_] := (
        getCovDs[metric] = DeleteDuplicates @ Append[getCovDs[metric], covD];
        makeMetricCompatible[covD, metric, kind];
    )

ClearMetricConnection[BD,                        metric_?MetricQ] := clearMetricConnection[BD, metric, KindOf[metric]];
ClearMetricConnection[covD_?DerivativeOperatorQ, metric_?MetricQ] :=
	With [{kind = KindOf[metric]},
        If [!covariantNameQ[covD, metric], Message[Msg::warn, covD, "is not a member of", metric, "-compatible derivatives."]; Return[]];

		clearMetricConnection[covD, metric, kind];
	]
ClearMetricConnection[___] := Message[ClearMetricConnection::usage]

    clearMetricConnection[covD_, metric_, kind_] := (
            getCovDs[metric] = DeleteCases[getCovDs[metric], covD];
            clearMetricCompatible[covD, metric, kind];
        )

MetricSpaceQ[___] := False
MetricQ[___]      := False

(* un-set metric and volume-form to be covariant constants of covD *)
clearMetricCompatible[covD_, metric_, kind_] :=
    With [{volForm = GetEpsilon[kind], nDim = GetDimension[kind]},
        covD[opIndex_, metric[a_, b_]]     = . /; FreePatternQ[{opIndex, a, b}] && AllTrue[{a, b}, TensorialIndexQ] && ValidIndicesQ[{opIndex, a, b}, kind];
        covD[opIndex_, volForm[indices__]] = . /; FreePatternQ[{opIndex, indices}]  \
                                                  && AllTrue[{indices}, TensorialIndexQ] && ValidIndicesQ[{opIndex, indices}, kind]
                                                  && (!PositiveIntegerQ[nDim] || (PositiveIntegerQ[nDim] && Length[{indices}] === nDim));
    ]

(* is opName covariantly compatible with metric? *)
covariantNameQ[opName_Symbol, metric_Symbol?MetricQ, cOptL_:{}] := MemberQ[Join[If[cOptL =!= {}, cOptL[[1,2]], {}], getCovDs[metric]], opName]
covariantNameQ[BD,            arg_,                  cOptL_:{}] := covariantNameQaux[BD,     indexKindProper @ arg, cOptL]
covariantNameQ[opName_Symbol, arg_,                  cOptL_:{}] := covariantNameQaux[opName, KindOf[opName, arg],   cOptL]
covariantNameQ[___] := False

    covariantNameQaux[opName_Symbol, kind_, cOptL_] :=
        If [MetricSpaceQ[kind],
            covariantNameQ[opName, GetMetric[kind], cOptL],
        (* else *)
            MemberQ[If[cOptL =!= {}, cOptL[[1,2]], {}], opName]
        ]

(* set metric and volume-form to be covariant constants of covD *)
makeMetricCompatible[covD_, metric_, kind_] :=
    With [{volForm = GetEpsilon[kind], nDim = GetDimension[kind]},
        covD[opIndex_, metric[a_, b_]]     := 0 /; FreePatternQ[{opIndex, a, b}] && AllTrue[{a, b}, TensorialIndexQ] && ValidIndicesQ[{opIndex, a, b}, kind];
        covD[opIndex_, volForm[indices__]] := 0 /; FreePatternQ[{opIndex, indices}]  \
                                                   && AllTrue[{indices}, TensorialIndexQ] && ValidIndicesQ[{opIndex, indices}, kind]
                                                   && (!PositiveIntegerQ[nDim] || (PositiveIntegerQ[nDim] && Length[{indices}] === nDim));
    ]

metricSymmetry[metric_?MetricQ]    := getMetricSymmetry[metric]
metricSymmetry[kind_?MetricSpaceQ] := getMetricSymmetry[GetMetric[kind]]
metricSymmetry[___]                := +1  (* default *)

(***** Set DefaultKind, Dimension, Signature, and Coordinates *****)

(* set default kind and initialize related structures *)
SetDefaultKind[kind_Symbol] := (
        If [kind =!= DefaultKind,  (* When changing the DefaultKind *)
            If [!checkIndexKind[kind, True], Return[]];

            (* Reset rules for RiemannCD in previous DefaultKind. cf: defineDerOp *)
            Unset[RiemannCD[a_, b_, c_, d_]]; (* FreePatternQ[{a, b, c, d}] && ValidIndexQ[a, DefaultKind] && PairIndexQ[a,c]; *)
            Unset[RicciCD[a_, b_]];           (* FreePatternQ[{a, b}]       && ValidIndexQ[a, DefaultKind] && PairIndexQ[a,b]; *)

            (* CD, Metricg, Torsion, and Epsilon were in previous DefaultKind *)
            (* cf: RemoveDerivativeOperator and RemoveMetric *)
            If [MetricSpaceQ[DefaultKind],
                With [{metric = GetMetric[DefaultKind]},
                    If [covariantNameQ[CD, metric], ClearMetricConnection[CD, metric]];
                    If [metric === Metricg,
                        GetMetric[DefaultKind]    = Null;
                        MetricSpaceQ[DefaultKind] = False;
                    ]
                ]
            ];
            getDerOps[DefaultKind] = DeleteCases[getDerOps[DefaultKind], CD];  (* update kind's getDerOps property *)

            defineOperand[SymbolJoin[Epsilon, DefaultKind], "\[Epsilon][" <> ToString[DefaultKind] <> "]", "*-",   {DefaultKind}, {-1}];
            defineOperand[SymbolJoin[Torsion, DefaultKind], "t["          <> ToString[DefaultKind] <> "]", "-bac", {DefaultKind}, {-1, -1, +1}];
            GetEpsilon[DefaultKind] = SymbolJoin[Epsilon, DefaultKind];
            GetTorsion[DefaultKind] = SymbolJoin[Torsion, DefaultKind];

            If [!CoordinateBasisQ[DefaultKind],
                defineOperand[SymbolJoin[Structuref, DefaultKind], "f", "-bac", {DefaultKind}, {-1, -1, +1}];
                GetStructuref[DefaultKind] = SymbolJoin[Structuref, DefaultKind]
            ];

            (* update DefaultKind *)
            DefaultKind := kind
        ];

        (* CD, Metricg, Torsion, and Epsilon always in DefaultKind *)
        defineOperand[Epsilon, "\[Epsilon]", "*-",   {kind}, {-1}];
        defineOperand[Torsion, "t",          "-bac", {kind}, {-1, -1, +1}];
        GetEpsilon[kind] = Epsilon;
        GetTorsion[kind] = Torsion;

        defineDerOp[CD, "\[Del]", kind];
        If [flagTable[MetricgFlag],
            On[MetricgFlag],  (* side-effect: MakeMetricConnection *)
        (* else *)
            Off[MetricgFlag]
        ];

        If [!CoordinateBasisQ[kind],
            defineOperand[Structuref, "f", "-bac", {kind}, {-1, -1, +1}];
            GetStructuref[kind] = Structuref
        ];
    )
SetDefaultKind[___] := Message[SetDefaultKind::usage]

(* sig is the number of minuses occuring in the signature of the metric *)
SetDimension[n_?PositiveIntegerQ]              := SetDimension[n, DefaultKind]
SetDimension[n_?PositiveIntegerQ, kind_Symbol] := ( If [checkIndexKind[kind, True], GetDimension[kind] = n]; )
SetDimension[__]                               := Message[SetDimension::usage]

GetDimension[] := GetDimension[DefaultKind]

ClearDimension[]            := ClearDimension[DefaultKind]
ClearDimension[kind_Symbol] := ( If [checkIndexKind[kind, True], GetDimension[kind] = .]; )
ClearDimension[__]          := Message[ClearDimension::usage]

SetSignature[sig_Integer]              := SetSignature[sig, DefaultKind]
SetSignature[sig_Integer, kind_Symbol] := ( If [checkIndexKind[kind, True], GetSignature[kind] = sig]; )
SetSignature[__]                       := Message[SetSignature::usage]

GetSignature[] := GetSignature[DefaultKind]

ClearSignature[]            := ClearSignature[DefaultKind]
ClearSignature[kind_Symbol] := ( If [checkIndexKind[kind, True], GetSignature[kind] = .]; )
ClearSignature[__]          := Message[ClearSignature::usage]

SetCoordinates[coSys_ /; VectorQ[coSys, AtomQ]]              := SetCoordinates[coSys, DefaultKind]
SetCoordinates[coSys_ /; VectorQ[coSys, AtomQ], kind_Symbol] :=
    With[{nDim = Length[coSys]},
        If [!checkIndexKind[kind, True], Return[]];

        If [!CoordinateBasisQ[kind], Message[Msg::err, "use SetCoordinates[coSys, basis] for non-coordinate basis", "", "", ""]; Return[]];

        With[ {kDim  = GetDimension[kind]},
            If [PositiveIntegerQ[kDim] && kDim =!= nDim, Message[Msg::err, "incompatible number of coordinates with dimension", kDim, "", ""]; Return[]]
        ];

        tCoordinates[kind]    = coSys;
        tCoordinatesStr[kind] = ToString /@ coSys;  (* String form of the coordinate system *)
        SetDimension[nDim, kind];
    ]
SetCoordinates[coSys_ /; VectorQ[coSys, AtomQ], basis_List?SquareMatrixQ]              := SetCoordinates[coSys, basis, DefaultKind]
SetCoordinates[coSys_ /; VectorQ[coSys, AtomQ], basis_List?SquareMatrixQ, kind_Symbol] :=
    With[{nDim = Length[coSys]},
        If [!checkIndexKind[kind, True], Return[]];

        If [CoordinateBasisQ[kind], Message[Msg::err, "Use SetCoordinates[coSys] for coordinate basis", "", "", ""]; Return[]];

        If [nDim =!= Length[basis[[1]]], Message[Msg::err, "incompatible number of elements between coSys and basis", "", "", ""]; Return[]];

        With[ {kDim = GetDimension[kind]},
            If [PositiveIntegerQ[kDim] && kDim =!= nDim, Message[Msg::err, "incompatible number of coordinates with dimension", kDim, "", ""]; Return[]]
        ];

        tCoordinates[kind]    = coSys;
        tCoordinatesStr[kind] = ToString /@ coSys;  (* String form of the coordinate system *)
        basisMatrix[kind]     = basis;              (* basis matrix: \xi_a = h_a^{\mu} \pd_{\mu} *)
        SetDimension[nDim, kind];
    ]
SetCoordinates[__] := Message[SetCoordinates::usage]

ClearCoordinates[]            := ClearCoordinates[DefaultKind]
ClearCoordinates[kind_Symbol] := (
        If [checkIndexKind[kind, True] && VectorQ[tCoordinates[kind], AtomQ],
            tCoordinates[kind] = .; tCoordinatesStr[kind] = .;
            ClearDimension[kind];
            If [!CoordinateBasisQ[kind], basisMatrix[kind] = .]
        ];
    )
ClearCoordinates[__] := Message[ClearCoordinates::usage]

(***** Status *****)

Status[]      := Status[DefaultKind]
Status[kind_] :=
    Module[ {flagStrL, flagL},
        If [!checkIndexKind[kind, True], Return []];

        If [kind === DefaultKind,
            flagStrL = {"AutoFlag", "MarkErrorFlag", "ResetDummiesFlag", "SyntaxCheckFlag",
                        "EvaluateBDFlag", "KdeltaFlag", "MetricgFlag",
                        "InitCTensorFlag", "TorsionFreeQ of CD", "----------"};
            flagL = {flagTable[AutoFlag], flagTable[MarkErrorFlag], flagTable[ResetDummiesFlag], flagTable[SyntaxCheckFlag],
                     flagTable[EvaluateBDFlag], flagTable[KdeltaFlag], flagTable[MetricgFlag],
                     flagTable[initCTensorFlag], TorsionFreeQ[CD], "-----"},
        (* else *)
            flagStrL = {}; flagL = {}
        ];
        AppendTo[flagStrL, #]& /@ {"Kind", "Dimension", "Signature", "Coordinates"};

        AppendTo[flagL, Sequence @@ kind];
        With[ {nDim = GetDimension[kind]}, If [PositiveIntegerQ[nDim], AppendTo[flagL, nDim], AppendTo[flagL, "Any"]]];
        With [ {sig = GetSignature[kind]}, If [IntegerQ[sig], AppendTo[flagL, sig], AppendTo[flagL, "Any"]]];
        If [VectorQ[tCoordinates[kind]], AppendTo[flagL, tCoordinates[kind]], AppendTo[flagL, "none"]];

        AppendTo[flagStrL, "CoordinateBasisQ"]; AppendTo[flagL, CoordinateBasisQ[kind]];

        TableForm[Transpose[{flagStrL, flagL}]]
    ]

(***** Predefined Tensorial Operators *****)

(*** basis derivative ***)

BD[opIndex_, moreIndices__, expr_] := Fold[BD[#2, #1]&, expr, Reverse[{opIndex, moreIndices}]] /; FreePatternQ[{opIndex, moreIndices, expr}];

(* evaluate component expr if EvaluateBDFlag is On *)
BD[opIndex_?ComponentIndexQ, expr_] := bdComponentEval[opIndex, expr, DefaultKind]                                            \
    /; flagTable[EvaluateBDFlag] && FreePatternQ[{opIndex, expr}] && freeObjectQ[expr]                                        \
       && PositiveIntegerQ[GetDimension[DefaultKind]] && Abs[opIndex] <= GetDimension[DefaultKind]                            \
       && ( (CoordinateBasisQ[DefaultKind] && VectorQ[tCoordinates[DefaultKind]])                                             \
            || (!CoordinateBasisQ[DefaultKind] && VectorQ[tCoordinates[DefaultKind]] && MatrixQ[basisMatrix[DefaultKind]]) )  \
       && ( DnIndexQ[opIndex] || (UpIndexQ[opIndex] && MetricSpaceQ[DefaultKind]) )
BD[kind_Symbol][opIndex_?ComponentIndexQ, expr_] := bdComponentEval[opIndex, expr, kind]                               \
    /; flagTable[EvaluateBDFlag] && FreePatternQ[{opIndex, expr}] && freeObjectQ[expr] && checkIndexKind[kind, False]  \
       && PositiveIntegerQ[GetDimension[kind]] && Abs[opIndex] <= GetDimension[kind]                                   \
       && ( (CoordinateBasisQ[kind] && VectorQ[tCoordinates[kind]])                                                    \
            || (!CoordinateBasisQ[kind] && VectorQ[tCoordinates[kind]] && MatrixQ[basisMatrix[kind]]) )                \
       && ( DnIndexQ[opIndex] || (UpIndexQ[opIndex] && MetricSpaceQ[kind]) )

BD[opIndex_Symbol, expr_] := bdComponentEval[-Position[tCoordinates[DefaultKind], opIndex][[1,1]], expr, DefaultKind]         \
	/; flagTable[EvaluateBDFlag] && FreePatternQ[{opIndex, expr}] && freeObjectQ[expr]                                        \
  	   && ( (CoordinateBasisQ[DefaultKind] && VectorQ[tCoordinates[DefaultKind]])                                             \
		    || (!CoordinateBasisQ[DefaultKind] && VectorQ[tCoordinates[DefaultKind]] && MatrixQ[basisMatrix[DefaultKind]]) )  \
	   && MemberQ[tCoordinates[DefaultKind], opIndex]
BD[kind_Symbol][opIndex_Symbol, expr_] := bdComponentEval[-Position[tCoordinates[kind], opIndex][[1,1]], expr, kind]  \
    /; flagTable[EvaluateBDFlag] && FreePatternQ[{opIndex, expr}] && freeObjectQ[expr]                                \
       && ( (CoordinateBasisQ[kind] && VectorQ[tCoordinates[kind]])                                                   \
		    || (!CoordinateBasisQ[kind] && VectorQ[tCoordinates[kind]] && MatrixQ[basisMatrix[kind]]) )               \
       && MemberQ[tCoordinates[kind], opIndex]

    bdComponentEval[opIndex_, expr_, kind_] :=
        If [DnIndexQ[opIndex],
            bdD[Abs[opIndex], expr, kind],
        (* else *)
            Sum[ GetMetric[kind][opIndex,m] bdD[m, expr, kind], {m, GetDimension[kind]} ]
    ]

bdD[a_, expr_]        := bdD[a, expr, DefaultKind]
bdD[a_, expr_, kind_] := (* basis derivative: D_a = h_a^mu \pd_mu *)
    If [CoordinateBasisQ[kind], D[expr, tCoordinates[kind][[a]]],  (* ordinary derivative *)
    (* else *)                  Sum[basisMatrix[kind][[a,mu]] D[expr, tCoordinates[kind][[mu]]], {mu, GetDimension[kind]}] ]

(*** Lie derivative ***)
LD[aV_, aV_[a_]] := 0 /; UpIndexQ[a] && TensorialIndexQ[a] && vectorNameQ[aV] && ValidIndexQ[a, KindOf @ aV]

(***** On / Off *****)

Unprotect[Off]  (* turn off a flag *)
Off[CoordinateBasisFlag]        := Off[CoordinateBasisFlag[DefaultKind]]
Off[CoordinateBasisFlag[kind_]] := (
        If [!checkIndexKind[kind, True], Return[]];

        (* update all GammaDerOp's symmetry *)
        If [CoordinateBasisQ[kind] === True,  (* previously *)
            defineOperand[getDerOp[Gamma][#], prtStrJoinDerOp["\[CapitalGamma]", #], "abc", {kind}, {-1, -1, +1}]& /@ getDerOps[kind]
        ];

        (* define Structuref *)
        If [kind === DefaultKind,
            defineOperand[Structuref, "f", "-bac", {kind}, {-1, -1, +1}],
        (* else *)
            defineOperand[SymbolJoin[Structuref, kind], "f", "-bac", {kind}, {-1, -1, +1}]
        ];

        CoordinateBasisQ[kind] = False;
    )
Off[EvaluateBDFlag] := (flagTable[EvaluateBDFlag] = False;)
Off[KdeltaFlag]     := (flagTable[KdeltaFlag] = False;)
Off[MetricgFlag]    := (
        flagTable[MetricgFlag] = False;
        RemoveMetric[Metricg];
    )
Protect[Off]

Unprotect[On]  (* turn on a flag *)
On[CoordinateBasisFlag]        := On[CoordinateBasisFlag[DefaultKind]]
On[CoordinateBasisFlag[kind_]] := (
        If [!checkIndexKind[kind, True], Return[]];

        (* update all GammaDerOp's symmetry *)
        If [CoordinateBasisQ[kind] === False,
            defineOperand[
                getDerOp[Gamma][#], prtStrJoinDerOp["\[CapitalGamma]", #], If [TorsionFreeQ[#], "+bac", "abc"], {kind}, {-1, -1, +1}
            ]& /@ getDerOps[kind]
        ];

        (* clear Structuref[kind] *)
        If [kind === DefaultKind,
            If [IndexedTensorQ[Structuref], Clear[Structuref]],
        (* else *)
            If [IndexedTensorQ[SymbolJoin[Structuref, kind]], removeObject @ SymbolJoin[Structuref, kind]]
        ];

        CoordinateBasisQ[kind] = True;
   )
On[EvaluateBDFlag] := (flagTable[EvaluateBDFlag] = True;)
On[KdeltaFlag]     := (flagTable[KdeltaFlag] = True;)
On[MetricgFlag]    := (
        flagTable[MetricgFlag] = True;
        defineMetric[Metricg, "g", "+ba", DefaultKind];
        MakeMetricConnection[CD, Metricg];
    )
Protect[On]

(***** Absorb Kdelta *****)

(* Wald's Notation:
  Symmetric or no metric:
   	Kdelta[ua,lb] = +Kdelta[lb,ua]
	V^a = +Kdelta[ua,lb] V^b
	V_a = +Kdelta[la,ub] V_b
  Antisymmetric metric:
   	Kdelta[ua,lb] = -Kdelta[lb,ua]
	V_a = +Kdelta[la,ub] V_b  (up-to-dn contraction)
	V^a = -Kdelta[ua,lb] V^b  (dn-to-up contraction)

    V^a =  Eps[ua,ub] V_b  (up-to-dn contraction)
    V_a = -Eps[la,lb] V^b  (dn-to-up contraction)

    Eps[ua,uc] Eps[lb,lc] = Kdelta[ua,lb]  => Kdelta[+1,-1] = +1 = -Kdelta[-1,+1]
*)

(* Kdelta_a^b T^b *)
Kdelta/: Kdelta[a_, b_] * oName_?IndexedOperandQ[pre___, c_, post___] :=
    absorbKdeltaSign[b, 2] * oName[pre, a, post] /; flagTable[KdeltaFlag] && FreePatternQ[{a,b, oName, pre, c, post}]  \
                                                    && !upupdndnIndexQ[{a, b}] && ValidIndicesQ[{a, b}, indexKind @ a] && PairIndexQ[b,c]
Kdelta/: Kdelta[a_, b_] * oName_?IndexedOperandQ[pre___, c_, post___] :=
    absorbKdeltaSign[a, 1] * oName[pre, b, post] /; flagTable[KdeltaFlag] && FreePatternQ[{a,b, oName, pre, c, post}]  \
                                                    && !upupdndnIndexQ[{a, b}] && ValidIndicesQ[{a, b}, indexKind @ a] && PairIndexQ[a,c]

(* Kdelta_a^b derOp[c, T] *)
Kdelta/: Kdelta[a_, b_] * opName_?IndexedOperatorQ[c_, expr_] :=
    absorbKdeltaSign[b, 2] * opName[a, expr] /; flagTable[KdeltaFlag] && FreePatternQ[{a, b, opName, c, expr}]  \
                                                && !upupdndnIndexQ[{a, b}] && ValidIndicesQ[{a, b}, indexKind @ a] && PairIndexQ[b, c]
Kdelta/: Kdelta[a_, b_] * opName_?IndexedOperatorQ[c_, expr_] :=
    absorbKdeltaSign[a, 1] * opName[b, expr] /; flagTable[KdeltaFlag] && FreePatternQ[{a, b, opName, c, expr}]  \
                                                && !upupdndnIndexQ[{a, b}] && ValidIndicesQ[{a, b}, indexKind @ a] && PairIndexQ[a, c]

(* Kdelta_a^b CD[c, T^a] or Kdelta_a^b XD[A^a] or Kdelta_a^b XP[..., A^a, ...]. NB: opName[_, Kdelta] === 0 for all operators. *)
Kdelta/: Kdelta[a_, b_] * opName_?IndexedOperatorQ[pre___, expr_, post___] :=
    opName[pre, Kdelta[a, b] * expr, post] /; flagTable[KdeltaFlag] && FreePatternQ[{a, b, opName, pre, expr, post}]                     \
                                              && !upupdndnIndexQ[{a, b}] && covariantNameQ[opName, a, {CovDs -> definedDerivativeList}]  \
                                              && ValidIndicesQ[{a, b}, indexKind @ a] && absorbKdeltaQ[expr, a, b]

    absorbKdeltaQ[expr_, a_, b_] :=
        With[ {idxL = findIndices[expr, IndexQs -> {TensorialIndexQ}]},
            MemberQ[idxL, FlipIndex @ a] || MemberQ[idxL, FlipIndex @ b]
        ]

    absorbKdeltaSign[idx_, pos_] :=
        With[ {metric = GetMetric[indexKind @ idx]},
            (getMetricSymmetry[metric])^(pos + If[DnIndexQ[idx], 1, 0])
        ] /; MetricSpaceQ[indexKind @ idx]
    absorbKdeltaSign[idx_, pos_] := +1

(***** Absorb *****)

SetAttributes[Absorb, HoldAll]
(* NB: aMetric can be any (anti)symmetric rank-2 tensor. *)
Absorb[expr_, aMetric_Symbol?IndexedOperandQ, opts___Rule] :=
    Module[ {mSym, hOptL = FilterRules[{opts}, HeadQs], cOptL = FilterRules[{opts}, CovDs], mKind = KindOf @ aMetric},
        (* aMetric should be a rank-2 tensor *)
        If [GetRank[aMetric] =!= 2,
            Message[Msg::warn, aMetric, "is not a rank-2 tensor. It has rank", GetRank @ aMetric, ""]; Return[expr]
        ];

        mSym =
            Switch [GetSymmetry @ aMetric,  (* for a 'general' 2-rank tensor, which can be antisymmetric or no-symmetric *)
                GenSet[{Cycles[{{1,2}}],-1}], -1,
                "Antisymmetric",              -1,
                GenSet[{Cycles[{{1,2}}],+1}], +1,
                "Symmetric",                  +1,
                _,                             0
            ];

        (* aMetric should be symmetric or antisymmetric *)
        If [!MemberQ[{+1, -1}, mSym],
            Message[Msg::warn, aMetric, "should be symmetric or antisymmetric.", "", ""]; Return[expr]
        ];

        (* aMetric should satisfy HeadQs option *)
        If [hOptL =!= {} && !allQoptions[HeadQs][aMetric, hOptL],
            Message[Msg::warn, aMetric, "does not satisfy the option", HeadQs /. hOptL, ""]; Return[expr]
        ];

        (* check covariant-derivative option *)
        If [cOptL =!= {} && !AllTrue[CovDs /. cOptL, IndexedOperatorQ],
            Message[Msg::err, "not defined operator(s)", CovDs /. cOptL, "", ""]; Return[expr]
        ];

        absorb[expr, aMetric, mKind, mSym, FilterRules[{opts}, IndexQs], hOptL, cOptL]
    ]
Absorb[___] := Message[Absorb::usage]

Absorbg[expr_, opts___Rule] := Absorb[expr, Metricg, opts]
Absorbg[___]                := Message[Absorbg::usage]

absorb[expr_, aMetric_, mKind_, mSym_, iOptL_List, hOptL_List, cOptL_List] :=
    expandObject[expr, Sequence @@ hOptL] //. absorbRuleWith[aMetric, mKind, mSym, iOptL, hOptL, cOptL]

    absorbRuleWith[aMetric_, mKind_, mSym_, iOptL_List, hOptL_List, cOptL_List] := {
        (* 1. No operators or inside of scalarFunction: g_{ab} T^b or Tscalar[g_{ab} R^{ab}]^2 *)
        (* g_{ab} T^b *)
        aMetric[a_, b_] * tName_?IndexedOperandQ[pre___, c_, post___] :>
            absorbSign[b, 2, mSym] * tName[pre, a, post] /; allQoptions[HeadQs][tName, hOptL] && ValidIndicesQ[{a, b}, mKind]  \
                                                            && pairQabsorb[tName[pre, c, post], {b,c}, mKind, iOptL],

        (* g_{ba} T^b *)
        aMetric[a_, b_] * tName_?IndexedOperandQ[pre___, c_, post___] :>  (* NB: considering anti-symmetric contraction *)
            absorbSign[a, 1, mSym] * tName[pre, b, post] /; allQoptions[HeadQs][tName, hOptL] && ValidIndicesQ[{a, b}, mKind]  \
                                                            && pairQabsorb[tName[pre, c, post], {a,c}, mKind, iOptL],

        (* 2. Matching with the index of CD-type operator: g_{ab} \pd^b T *)
        (* g_{ab} \pd^b T *)
        aMetric[a_, b_] * opName_?IndexedOperatorQ[c_, expr_] :>
            absorbSign[b, 2, mSym] * opName[a, expr] /; allQoptions[HeadQs][opName, hOptL] && ValidIndicesQ[{a, b}, mKind]  \
                                                        && kindMatchQ[mKind, KindOf[opName, c]] && pairQabsorb[opName, {b,c}, iOptL],

        (* g_{ba} \pd^b T *)
        aMetric[a_, b_] * opName_?IndexedOperatorQ[c_, expr_] :>
            absorbSign[a, 1, mSym] * opName[b, expr] /; allQoptions[HeadQs][opName, hOptL] && ValidIndicesQ[{a, b}, mKind]  \
                                                        && kindMatchQ[mKind, KindOf[opName, c]] && pairQabsorb[opName, {a,c}, iOptL],

        (* 3. Not matching with the index of CD-type operator: *)
        (* g_{ab} CD[lc, T] --> CD[lc, g_{ab} T] *)
        aMetric[a_, b_] * opName_?IndexedOperatorQ[arg_, expr_, post___] :>
            opName[arg, aMetric[a, b] * expr //. absorbRuleWith[aMetric, mKind, mSym, iOptL, hOptL, cOptL], post]          \
            /; upupdndnIndexQ[{a, b}] && ValidIndicesQ[{a, b}, mKind] && kindMatchQ[mKind, KindOf[opName, arg]]            \
               && covariantNameQ[opName, aMetric, cOptL] && ValidIndexQ[arg, mKind] && allQoptions[HeadQs][opName, hOptL]  \
               && absorbQ[expr, {a, b}, mKind, mSym, iOptL, hOptL, cOptL]
    }

    (* is raising or lowering possible *)
    (* g_{ab} T^b or g_{ab} T^a *)
    absorbQ[(tName_?IndexedOperandQ)[args__], {a_, b_}, mKind_, mSym_, iOptL_, hOptL_, cOptL_] :=
        If [   (Or @@ (pairQabsorb[tName[args], {b, #}, mKind, iOptL]& /@ {args}))  \
            || (Or @@ (pairQabsorb[tName[args], {a, #}, mKind, iOptL]& /@ {args})),
            True,
        (* else *)
            False
        ] /; allQoptions[HeadQs][tName, hOptL]

    (* g_{ab} \pd^b T or g_{ab} \pd^a T *)
    absorbQ[(opName_?IndexedOperatorQ)[c_, expr_], {a_, b_}, mKind_, mSym_, iOptL_, hOptL_, cOptL_] :=
        True /; allQoptions[HeadQs][opName, hOptL] && kindMatchQ[mKind, KindOf[opName, c]]      \
                && (pairQabsorb[opName, {b, c}, iOptL] || (pairQabsorb[opName, {a, c}, iOptL]))

    (* g_{ab} \pd_c T *)
    absorbQ[(opName_?IndexedOperatorQ)[arg_, expr__], {_, _}, mKind_, mSym_, _, hOptL_, cOptL_] :=
        False /; !allQoptions[HeadQs][opName, hOptL] || !covariantNameQ[opName, GetMetric[mKind], cOptL] || !kindMatchQ[mKind, KindOf[opName, arg]]

    (* g_{ab} CD[lc, T] *)
    absorbQ[(opName_?IndexedOperatorQ)[arg_, expr__], {a_, b_}, mKind_, mSym_, iOptL_, hOptL_, cOptL_] :=
        absorbQ[expr, {a, b}, mKind, mSym, iOptL, hOptL, cOptL] /; allQoptions[HeadQs][opName, hOptL] && kindMatchQ[mKind, KindOf[opName, arg]]  \
                                                                   && getType[opName] === CD && covariantNameQ[opName, GetMetric[mKind], cOptL]

    (* g_{ab} d(T^b) *)
    absorbQ[(opName_?IndexedOperatorQ)[expr_], {a_, b_}, mKind_, mSym_, iOptL_, hOptL_, cOptL_] :=
        absorbQ[expr, {a, b}, mKind, mSym, iOptL, hOptL, cOptL] /; allQoptions[HeadQs][opName, hOptL] && kindMatchQ[mKind, KindOf[opName, expr]]  \
                                                                   && getType[opName] === XD && covariantNameQ[opName, GetMetric[mKind], cOptL]

    (* g_{ab} XP[..., T^b, ...] *)
    absorbQ[(opName_?IndexedOperatorQ)[pre___, expr_, post___], {a_, b_}, mKind_, mSym_, iOptL_, hOptL_, cOptL_] :=
        absorbQ[expr, {a, b}, mKind, mSym, iOptL, hOptL, cOptL] /; allQoptions[HeadQs][opName, hOptL] && kindMatchQ[mKind, KindOf[opName, pre, expr]]  \
                                                                   && getType[opName] === XP && covariantNameQ[opName, GetMetric[mKind], cOptL]
    absorbQ[___] := False

        (* \phi^{ab} R_{ab} -> R_a^a and \phi^{ab} \pd_b -> \pd_a *)
        pairQabsorb[tName_?IndexedOperandQ[indices___], {a_, b_?TensorialIndexQ}, mKind_, iOptL_] := kindMatchQ[mKind, KindOf[tName[indices], b]]  \
                                                                                                     && pairQabsorbAux[{a, b}, iOptL]
        pairQabsorb[opName_?IndexedOperatorQ,          {a_, b_?TensorialIndexQ},         iOptL_] := pairQabsorbAux[{a, b}, iOptL] && (getType[opName] === CD)
        pairQabsorb[___]                                                                         := False

            pairQabsorbAux[{a_, b_}, iOptL_] := PairIndexQ[a,b] && (And @@ Map[allQoptions[IndexQs][#, iOptL]&, {a,b}])

    absorbSign[idx_, pos_, -1] := (-1)^(pos + If[DnIndexQ[idx], 1, 0])
    absorbSign[idx_, pos_, +1] := +1

(***** PutMetric *****)

PutMetric[expr_, idx_?TensorialIndexQ, opts___Rule] :=
    Module[ {kind = indexKind[idx]},
        If [MetricSpaceQ[kind],
            forEachObject[expr, FilterRules[{opts}, HeadQs], putMetricObject, idx, kind, GetMetric[kind], opts],
        (* else *)
            expr
        ]
    ]
PutMetric[___] := Message[PutMetric::usage]

    putMetricObject[(oName_?IndexedOperandQ)[indices__], idx_, kind_, metric_, opts___] :=
        Module[ {indexL = {indices}, pos, pair},
            If [MemberQ[indexL, idx] && kindMatchQ[kind, KindOf[oName[indices], idx]],
                pos = Position[indexL, idx][[1,1]];
                pair = DummyPair[kind];
                If [DnIndexQ[idx], getMetricSymmetry[metric] * metric[idx, pair[[1]]] * (oName @@ ReplacePart[indexL, pos -> pair[[2]]]),
                (* else *)                                     metric[idx, pair[[2]]] * (oName @@ ReplacePart[indexL, pos -> pair[[1]]])],
            (* else *)
                oName[indices]
            ]
        ]
    putMetricObject[(opName_?IndexedOperatorQ)[arg_, expr___], idx_, kind_, metric_, opts___] :=
        If [kindMatchQ[kind, KindOf[opName, arg]],
            Switch [getType[opName],
                CD, If [arg === idx,
                        With[ {pair = DummyPair[kind]},
                            If [DnIndexQ[idx], getMetricSymmetry[metric] * metric[idx, pair[[1]]] * opName[pair[[2]], expr],
                            (* else *)                                     metric[idx, pair[[2]]] * opName[pair[[1]], expr]]
                        ],
                    (* else *)
                        opName[arg, putMetricObject[expr, idx, kind, metric, opts]]
                    ],
                LD, If [MemberQ[findIndicesAll[expr, opts], idx] && FreeQ[expr, BD | Alternatives @@ nonTensorList],
                        opName[arg, putMetricObject[expr, idx, kind, metric, opts]],
                    (* else *)
                        opName[arg, expr]
                    ],
                XD, opName[putMetricObject[arg, idx, kind, metric, opts], expr],
                XP, opName[Sequence @@ (putMetricObject[#, idx, kind, metric, opts]& /@ {arg, expr})]
            ],
        (* else *)
            opName[arg, expr]
        ]
    putMetricObject[obj_, idx_, kind_, metric_, opts___] := obj

        (* TODO: insert metrics according the shape of tensors
        putMetricShape[Kdelta[a_, b_]] := Kdelta[b, a] /; UpIndexQ[a] && DnIndexQ[b]  (* \delta^a_{\ b} --> \delta_b^{\ a} *)
        putMetricShape[Kdelta[a_, b_]] :=
            With[{iKind = indexKindOf @ a},
                If [MetricSpaceQ[iKind],
                    If [DnIndexQ[a],                     MetricOf[iKind][a,b]    (* g_{ab} *)
                    (* else *)       SymbolJoin[Inverse, MetricOf[iKind]][a,b]], (* g^{ab} *)
                (* else *)
                    ErrorT[Kdelta[a, b]]
                ]
            ] /; upupdndnIndexQ[{a,b}]
         *)

(***** SeparateMetric *****)

SeparateMetric[expr_, opts___Rule] := forEachObject[expr, FilterRules[{opts}, HeadQs], separateMetricObject, opts]
SeparateMetric[___]                := Message[SeparateMetric::usage]

    separateMetricObject[(oName_?IndexedOperandQ)[indices__], opts___] :=
        Module[ {indexL = {indices}, dnupL, kind, dummyPair, rc = 1, i},
            dnupL = dnupOf[oName, indexL];
            Do [
                If [dnupL[[i]] =!= dnupState[indexL[[i]]],
                    kind = indexKindProper @ indexL[[i]];
                    If [MetricSpaceQ[kind],
                        dummyPair = DummyPair[kind];
                        If [DnIndexQ[indexL[[i]]],
                            rc *= GetMetric[kind][indexL[[i]], dummyPair[[1]]]; indexL = ReplacePart[indexL, i -> dummyPair[[2]]],
                        (* else *)
                            rc *= GetMetric[kind][indexL[[i]], dummyPair[[2]]]; indexL = ReplacePart[indexL, i -> dummyPair[[1]]]
                        ]
                    ]
                ],
                {i, Length[indexL]}
            ];
            rc * oName[Sequence @@ indexL]
        ]
    separateMetricObject[(opName_?IndexedOperatorQ)[arg_, expr___], opts___] :=
        Module [{kind, dummyPair, opIndex, rc = 1},
            Switch [getType[opName],
                CD, opIndex = arg;
                    If [UpIndexQ[arg],
                        kind = If [opName === BD, indexKindProper[arg], KindOf[opName, arg]];
                        If [MetricSpaceQ[kind],
                            dummyPair = DummyPair[kind];
                            rc *= GetMetric[kind][arg, dummyPair[[2]]]; opIndex = dummyPair[[1]]
                        ]
                    ];
                    rc * opName[opIndex, separateMetricObject @ expr],
                LD, opName[arg, separateMetricObject @ expr],
                XD, opName[separateMetricObject @ arg, expr],
                XP, opName[Sequence @@ (separateMetricObject /@ {arg, expr})]
            ]
        ]
    separateMetricObject[obj_, opts___] := obj

(***** DualStar *****)

DualStar[expr_, indexL:{(_Symbol | _String | _Integer) ..}]              := DualStar[expr, indexL, indexKindProper @ indexL[[1]]]
DualStar[expr_, indexL:{(_Symbol | _String | _Integer) ..}, kind_Symbol] := dualStar[Dum @ expr, indexL, kind] /; DeleteDuplicates[indexKindProper /@ indexL] === {kind}
DualStar[___]                                                 := Message[DualStar::usage]

    dualStar[expr_, indexL_List, kind_Symbol] :=
        Module[{rcExpr = expandObject[expr], term, freeL, nDim = GetDimension[kind]},
            If [Head[rcExpr] === Plus, term = rcExpr[[1]], term = rcExpr];

            If [Length[indexL] < 2 || (PositiveIntegerQ[nDim] && Length[indexL] =!= nDim),
                Message[Msg::err, "Invalid numbers of indices: ", indexL, "", ""]; Return[]
            ];

            (* $FormDropIndices -> True for non-zero rank diff. forms *)
            freeL = findFreeIndicesAll[term, IndexQs -> {KindIndexQ[kind]}, $FormDropIndices -> True];
            freeL = Select[freeL, (DnIndexQ[#] || UpIndexQ[#])&];
            If [PositiveIntegerQ[nDim] && Length[freeL] > nDim,
                Message[Msg::err, "Invalid numbers of free indices: ", freeL, "", ""]; Return[]
            ];

            If [freeL =!= {} && (Intersection[freeL, indexL] =!= {} || Intersection[FlipIndex /@ freeL, indexL] === {}),
                Message[Msg::err, "Ill-formed indices: ", indexL, "", ""]; Return[]
            ];

            dualStarTerm[rcExpr, freeL, indexL, kind]
        ]

        dualStarTerm[term_, freeL_, indexL_, kind_] := With[ {eps = GetEpsilon[kind]}, (1/Length[freeL]!) term eps[Sequence @@ indexL]]

(********************************************************************)

initTensor[] := (
        (***** Predefined Indexed Objects: Kdelta *****)
        defineOperand[Kdelta, "\[Delta]", "2",  {Latin}, {-1, +1}];  (* \delta_a^{\ b} *)
        reservedNameList = Join[reservedNameList, {Kdelta}];

        Kdelta[i_Integer, j_Integer] := 0 /; i =!= -j && ((i > 0 && j < 0) || (i < 0 && j > 0));
        (* See KdeltaSumRule[]:
        Kdelta[i_Integer, j_Integer] := +1                          /; (i > 0 &&) && j === -i;
        Kdelta[i_Integer, j_Integer] := metricSymmetry[DefaultKind] /; (i < 0 &&) && j === -i;
        *)

        (***** Flag Table *****)
        flagTable[EvaluateBDFlag]  = False;
		flagTable[KdeltaFlag]      = True;  (* absorb Kdelta *)
        flagTable[MetricgFlag]     = True;  (* Metricg is defined on DefaultKind *)
        flagTable[initCTensorFlag] = False;

        (* initialize *)
        definedDerivativeList = {};  (* See derivativeRules and absorb Kdelta *)
        nonTensorList         = {};  (* for non-Tensors *)

        (* Option for specifying covariant derivatives *)
        reservedNameList = Join[reservedNameList, {CovDs}];

        (***** set DefaultKind, and define CD, Metricg, Structuref *****)
        SetDefaultKind[Latin];
		On[CoordinateBasisFlag[DefaultKind]];
        reservedNameList = Join[reservedNameList, {Metricg}];

        (* covariant-structure related symbols *)
        reservedNameList = Join[reservedNameList, {
            Gamma,   Ricci,   Riemann,   Scalar,   Weyl,
            GammaCD, RicciCD, RiemannCD, ScalarCD, WeylCD
        }];

        (***** Predefined Operators *****)
		defineOperator[BD, "\[PartialD]", CD];
        derivativeRules[BD];
        BD/: MakeBoxes[BD[arg_, expr___], StandardForm] := interpretBox[BD[arg, expr],
                With[{kind = indexKindProper[arg]},
                    TemplateBox[{If[kind =!= errorIndex && UpIndexQ[arg], SuperscriptBox, SubscriptBox]
                                 [If [kind === errorIndex,
                                     OverscriptBox["\[PartialD]", "^"],
                                  (* else *)
                                     If [CoordinateBasisQ[kind], "\[PartialD]", OverscriptBox["\[PartialD]", "^"]]
                                  ], First @ indexCharSpace[arg]
                                 ],
                                MakeBoxes[expr, StandardForm]}, "RowDefault"]
                ]
            ];
        reservedNameList = Join[reservedNameList, {BD}];

        (* LD *)
        defineOperator[LD, "\[ScriptCapitalL]", LD];  (* NB: The kind of LD is that of the first argument. *)
        derivativeRules[LD, vectorNameQ];

		(***** Finish initTensor *****)
		reservedNameList = DeleteDuplicates[reservedNameList];
    )
initTensor[]

(********************************************************************)
End[]

EndPackage[]
