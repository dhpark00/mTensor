(* :Title: Variation.m (Experimental) *)
(* :Context: mTensor` *)
(* :Author: Dal-Ho Park *)
(* :Summary: Variational Derivative for mTensor *)
(* :Package Version: 2019.08 *)
(* :Mathematica Version: 10.4 *)

(********************************************************************)
BeginPackage["mTensor`", {"mTensor`xPermML`"}]

(********************************************************************)
Begin["`Private`"]

(********************* Variational Derivative ***********************)

Options[VD] = {BD -> {BD}, IndependentVD -> {}, ByPartsVD -> False};
VD[arg_, expr_, opts___Rule] := VD[arg, DumFresh[expr], 1, opts] /; FreePatternQ[{arg, expr, opts}]

(* define XP-type operator VD *)
VD/: MakeBoxes[VD[arg_, expr_, 1,     opts___Rule], StandardForm] := interpretBox[VD[arg, expr, 1, opts],
        TemplateBox[{"[", "(",
                     SubscriptBox["\[Delta]", MakeBoxes[arg, StandardForm]], MakeBoxes[expr, StandardForm], ")", "]"}, "RowDefault"]
    ]
VD/: MakeBoxes[VD[arg_, expr_, rest_, opts___Rule], StandardForm] := interpretBox[VD[arg, expr, rest, opts],
        TemplateBox[{"[", MakeBoxes[rest, StandardForm], "(",
                     SubscriptBox["\[Delta]", MakeBoxes[arg, StandardForm]], MakeBoxes[expr, StandardForm], ")", "]"}, "RowDefault"]
    ]

(* Linear *)
VD[arg_, expr_Plus, rest_, opts___Rule] := VD[arg, #, rest, opts]& /@ expr

(* Leibnitz rule *)
VD[arg_, expr_Times, rest_, opts___Rule] := Sum[varDtake[arg, rest, List @@ expr, cnt, opts], {cnt, Length @ expr}]

    varDtake[arg_, rest_, lst_List, n_Integer, opts___Rule] := VD[arg, lst[[n]], Times @@ ReplacePart[lst, n -> rest], opts]

(* Derivation *)
VD[arg_, c_?constantQ,         rest_, opts___Rule] := 0
VD[arg_, c_?constantQ * expr_, rest_, opts___Rule] := c * VD[arg, expr, rest, opts]

(* Scalar functions *)
VD[arg_, sf_?ScalarFunctionQ[expr_], rest_, opts___Rule] := VD[arg, DumFresh[expr], sf'[expr] * rest, opts] /; sf =!= Tscalar
VD[arg_, Power[expr1_, expr2_],      rest_, opts___Rule] := (
          VD[arg, DumFresh[expr1], DumFresh[expr2] * Power[expr1, expr2 - 1]  * rest, opts]
        + VD[arg, DumFresh[expr2], Power[expr1, expr2] * Log[DumFresh[expr1]] * rest, opts]
    )

(* Remove Tscalar head because the result is in general not a scalar *)
VD[arg_, Tscalar[expr_], rest_, opts___Rule] := VD[arg, DumFresh[expr], rest, opts]

(* Same tensor: metric *)
VD[metric_[a_, b_], (metric_Symbol?MetricQ)[c_, d_], rest_, opts___Rule] :=
    With [{fa = FlipIndex[a], fb = FlipIndex[b]},
        mSign[a, b, c, d] * rest * (metric[fa, c]*metric[fb, d] + metric[fa, d]*metric[fb, c])/2
    ]

    mSign[a_, b_, c_, d_] :=  1 /; upupdndnIndexQ[{a, b, c, d}]
    mSign[a_, b_, c_, d_] := -1 /; upupdndnIndexQ[{a, b}] && upupdndnIndexQ[{c, d}] && !upupdndnIndexQ[{a, c}]
    mSign[_,  _,  _,  _]  :=  0

(* Same tensor. Place indices in proper delta positions. TODO: How in spinor calculus? *)
VD[t_[i1___], t_?IndexedOperandQ[i2___], rest_, opts___Rule] :=
    Module [{idxL = FlipIndex /@ {i1}},
        imposeSymmetry[Inner[combTwoIndices[#1, #2, t[i2]]&, idxL, {i2}, Times], idxL, getGenSetOf[t[i1]]] * rest
    ] /; Length[{i1}] === Length[{i2}]
VD[t_[i1___], t_?IndexedOperandQ[i2___], rest_, opts___Rule] := (
        Message[Msg::warn, "Different lengths of indices:", Length @ {i1}, "and", Length @ {i2}]; t[i2]
    ) /; Length[{i1}] =!= Length[{i2}]

    combTwoIndices[a_, b_, t_[i2___]] := (
            Message[Msg::warn, "Different kinds of indices:", a, "and", b]; ErrorT[Kdelta][a, b]
        ) /; indexKind[a] =!= errorIndex && indexKind[a] =!= indexKind[b]
    combTwoIndices[a_, b_, t_[i2___]] := Kdelta[a, b] /; !upupdndnIndexQ[{a,b}]
    combTwoIndices[a_, b_, t_[i2___]] := With [{kind = KindOf[t[i2], b]},
                                             If [MetricSpaceQ[kind],
                                                 GetMetric[kind],
                                             (* else *)
                                                 Message[Msg::warn, "No metric for", kind, "", ""]; ErrorT[Kdelta]
                                             ][a, b]
                                         ] /; upupdndnIndexQ[{a,b}]
    combTwoIndices[a_, b_, t_[i2___]] := Null[a, b]

    imposeSymmetry[expr_, idxL_List, GS_GenSet] :=
        With [{gr =  MakePermGroup[GS, Length @ idxL]},
            If [gr === {}, expr,
            (* else *)     Plus @@ (permuteIndices[expr, idxL, #]& /@ gr) / Length[gr]]
        ]

        permuteIndices[expr_, {},        _]     := expr
        permuteIndices[expr_, {_},       _]     := expr
        permuteIndices[expr_, idxL_List, perm_] := perm[[2]] * (expr /. Inner[Rule, idxL, PermuteList[idxL, perm], List])

(* Different tensors *)
VD[t1_[i1___], t2_?IndexedTensorQ[i2___], rest_, opts___Rule] := 0 /; MemberQ[IndependentVD /. {opts} /. Options[VD], t2]

(* Integration by parts *)
VD[t_, pd_Symbol?IndexedOperatorQ[ind_, expr_], rest_, opts___Rule] :=
    -VD[t, expr, pd[ind, rest], opts] /; (ByPartsVD /. {opts} /. Options[VD]) && MemberQ[BD /. {opts} /. Options[VD], pd]

(* simplification rules *)
VD[arg_, expr_, 0, opts___Rule] := 0

(********************************************************************)
initVariation[] := (
        defineOperator[VD, "\[Delta]", XP];
        reservedNameList = Join[reservedNameList, {VD}];

        (***** Finish initVariation *****)
        reservedNameList = DeleteDuplicates[reservedNameList];
    )
initVariation[]

(********************************************************************)
End[]

EndPackage[]
