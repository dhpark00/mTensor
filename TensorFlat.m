
(********************************************************************)
BeginPackage["mTensor`", {"mTensor`xPermML`"}]

ClearConstantMetric::usage = "ClearConstantMetric[<kind>]"
MakeConstantMetric::usage  = "MakeConstantMetric[vec, <coSys>, <kind>]"

(********************************************************************)
Begin["`Private`"]

ClearConstantMetric[]      := ClearConstantMetric[DefaultKind]
ClearConstantMetric[kind_] :=
    Module[ {metric = GetMetric[kind], epsilon, n = GetDimension[kind], rangeL, tSymL},
        If [PositiveIntegerQ[n],
			epsilon = GetEpsilon[kind];
            epsilon[args:(_Integer ..)] = . /; Length[{args}] === n && Length[Abs[{args}]] =!= Length[Union[Abs[{args}]]];

            rangeL = Range[n];
	        tSymL = ToImag[#, n]& /@ MakePermGroup[symToGenSet["Antisymmetric", n], n];
	        (epsilon[ Sequence @@ (-rangeL)[[ List @@ (signTerm[#] * #) ]] ] = .)& /@ tSymL;
	        (epsilon[ Sequence @@ (+rangeL)[[ List @@ (signTerm[#] * #) ]] ] = .)& /@ tSymL;

            clearComponents[metric, 2, {n, n}, {-1,-1}];
            clearComponents[metric, 2, {n, n}, { 1, 1}];

            ClearSignature[kind];
            ClearCoordinates[kind];
        ];

        ClearMetricConnection[BD, metric];

        constantMetricQ[kind] = False;
    ] /; MetricSpaceQ[kind] && constantMetricQ[kind] === True
ClearConstantMetric[___] := Message[ClearConstantMetric::usage]

MakeConstantMetric[]            := MakeConstantMetric[DefaultKind]
MakeConstantMetric[kind_Symbol] := (
            If [!MetricSpaceQ[kind], Message[Msg::err, kind, "is not a metric space.", "", ""]; Return[]];
            constantMetricQ[kind] = True;
            MakeMetricConnection[BD, GetMetric[kind]];
        )

MakeConstantMetric[arg_List]              := MakeConstantMetric[arg, DefaultKind]
MakeConstantMetric[arg_List, kind_Symbol] :=
    With[{coSys = SymbolJoin /@ Table[{"x", ToString[i]}, {i, First @ Dimensions[arg]}]},
        MakeConstantMetric[arg, coSys, kind]
    ] /; VectorQ[arg, IntegerQ] || (SquareMatrixQ[arg] && VectorQ[Flatten @ arg, IntegerQ])

MakeConstantMetric[arg_List, coSys_?VectorQ]              := MakeConstantMetric[arg, coSys, DefaultKind]
MakeConstantMetric[arg_List, coSys_?VectorQ, kind_Symbol] :=
    Module[ {metric, matg, epsilon, n = First @ Dimensions[arg], s, rangeL, tSymL},
        If [!MetricSpaceQ[kind], Message[Msg::err, kind, "is not a metric space.", "", ""]; Return[]];
        If [!CoordinateBasisQ[kind], Message[Msg::err, kind, "is not in coordinate basis.", "", ""]; Return[]];
        If [n =!= Length[coSys], Message[Msg::err, "incompatible arguments:", vec, "and", coSys]; Return[]];

        GetDimension[kind] = n;

        constantMetricQ[kind] = True;
        SetCoordinates[coSys, kind];

        (* m + p = n, -m + p = s *)
        s = If [VectorQ[arg], Total[arg], Total[Eigenvalues[arg]]];
        SetSignature[s, kind];  (* Assumption: vec == {-1 or +1,..} *)

        metric = GetMetric[kind];
        MakeMetricConnection[BD, metric];

        matg = If [VectorQ[arg], DiagonalMatrix[arg], arg];
        tableToComponents[metric, 2, {-1,-1}, matg];
        tableToComponents[metric, 2, { 1, 1}, matg];

		epsilon = GetEpsilon[kind];
        rangeL = Range[n];
        tSymL = ToImag[#, n]& /@ MakePermGroup[symToGenSet["Antisymmetric", n], n];
        (epsilon[ Sequence @@ (-rangeL)[[ List @@ (signTerm[#] * #) ]] ] =                  signTerm[#])& /@ tSymL;
        (epsilon[ Sequence @@ (+rangeL)[[ List @@ (signTerm[#] * #) ]] ] = (-1)^((n-s)/2) * signTerm[#])& /@ tSymL;
        epsilon[args:(_Integer ..)] := 0 /; Length[{args}] === n && Length[Abs[{args}]] =!= Length[Union[Abs[{args}]]]
    ] /;  VectorQ[arg, IntegerQ] || (SquareMatrixQ[arg] && VectorQ[Flatten @ arg, IntegerQ]) && VectorQ[coSys, AtomQ]
MakeConstantMetric[___] := Message[MakeConstantMetric::usage]

(********************************************************************)
initTensorFlat[] := (

		(***** Finish initTensorGRG *****)
		loadedTensorFlat = True;  (* guard reloding *)
    )
initTensorFlat[]

(********************************************************************)
End[ ] (* end the private context *)

EndPackage[ ]  (* end the package context *)

(********************************************************************)
