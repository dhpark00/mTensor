(* :Title: Hypersurface.m (Experimental) *)
(* :Context: mTensor` *)
(* :Author: Dal-Ho Park *)
(* :Summary: Tensor Analysis for Hypersurfaces *)
(* :Package Version: 2017.08 *)
(* :Mathematica Version: 10.4 *)

(********************************************************************)
BeginPackage["mTensor`"]

(********** Usage messages for the exported functions **********)
DefineHypersurface::usage = ""
TangentialD::usage = ""

(***** Exported Variables *****)
SubCD::usage = ""
SubMetric::usage = ""
ExtrinsicK::usage = ""
SubBasis::usage = ""
NormalV::usage = ""

(********************************************************************)
Begin["`Private`"]

(************************ Exported Functions ************************)
DefineHypersurface[subKind_Symbol, normSign_:+1] :=
    Module[{},
        If [!checkIndexKind[subKind, True], Return[]];
        If [normSign =!= +1 && normSign =!= -1, Message[Msg::err, "un-supported norm of NormalV:", normSign, "", ""]; Return[]];

        DefineDerivativeOperator[SubCD, "D", subKind];
        DefineMetric[SubMetric, "\[Gamma]", subKind];
        MakeMetricConnection[SubCD, SubMetric];
        defineOperand[ExtrinsicK, "K", "ba", {subKind}, {-1}];
        defineOperand[SubBasis, "h", "ab", {subKind, DefaultKind}, {-1, +1}];
        defineOperand[NormalV, "n", "a", {DefaultKind}, {+1}];

        NormalV/: NormalV[a_]      NormalV[b_] := normSign /; FreePatternQ[{a, b}] && ValidIndicesQ[{a, b}, DefaultKind] && PairIndexQ[a, b];
        NormalV/: SubBasis[a_, b_] NormalV[c_] := 0 /; FreePatternQ[{a, b, c}] && ValidIndexQ[a, subKind] && ValidIndicesQ[{b, c}, DefaultKind] && PairIndexQ[b, c];

        SubBasis/: SubBasis[a_, b_] SubBasis[c_, d_] :=
            SubMetric[a, c] /; FreePatternQ[{a, b, c, d}] && ValidIndicesQ[{a, c}, subKind] && ValidIndicesQ[{b, d}, DefaultKind] && PairIndexQ[b, d];

        SubBasis/: SubBasis[a_, b_] SubBasis[c_, d_] Metricg[e_, f_] :=
            SubMetric[a, c] /; FreePatternQ[{a, b, c, d, e, f}] && ValidIndicesQ[{a, c}, subKind] && ValidIndicesQ[{b, d, e, f}, DefaultKind] \
                               && ((PairIndexQ[b, e] && PairIndexQ[d, f]) || (PairIndexQ[b, f] && PairIndexQ[d, e]));

        derivativeRules[TangentialD];
        TangentialD[a_, SubBasis[b_, c_]] :=
            Module [{dummyDn, dummyUp, affine = getDerOp[Gamma][SubCD]},
                {dummyDn, dummyUp} = DummyPair[subKind];
                affine[a, b, dummyUp] SubBasis[dummyDn, c] - normSign ExtrinsicK[a, b] NormalV[c]
            ] /; ValidIndicesQ[{a, b}, subKind] && ValidIndexQ[c, DefaultKind];

        TangentialD[a_, NormalV[b_]] :=
            Module [{dummyDn, dummyUp},
                {dummyDn, dummyUp} = DummyPair[subKind];
                ExtrinsicK[a, dummyUp] SubBasis[dummyDn, b]
            ] /; ValidIndexQ[a, subKind] && ValidIndexQ[b, DefaultKind];

        TangentialD[a_, expr_] := BD[a, expr] /; ValidIndexQ[a, subKind] && NoIndexQ[expr, IndexQs -> { !(KindIndexQ[DefaultKind][#]&) }]
    ]

(********************************************************************)

End[ ] (* end the private context *)

EndPackage[ ]  (* end the package context *)

(********************************************************************)
