(* NB: In GRG, the metric is always symmetric. *)

(********************************************************************)
BeginPackage["mTensor`", {"mTensor`xPermML`"}]

CDtoGamma::usage      = "CDtoGamma[expr, <CovD>]"
CommuteCD::usage      = "CommuteCD[{a,b}, expr, <CovD>]"
GammaToMetric::usage  = "GammaToMetric[expr, <CovD>]"
LDtoCD::usage         = "LDtoCD[expr, <CovD>]"
RiemannToGamma::usage = "RiemannToGamma[expr, <curvR>, <CovD>]"
RiemannToWeyl::usage  = "RiemannToWeyl[expr, <covD>]"
WeylToRiemann::usage  = "WeylToRiemann[expr, <covD>]"

SetComponents::usage   = "SetComponents[tensor, value(s)]"
ClearComponents::usage = "ClearComponents[tensor]"

Pushforward::usage     = "Pushborward[from, coSys, newCoSys, <simpCmd>]"
Pullback::usage        = "Pullback[from, coSys, newCoSys, <simpCmd>]"
PushTensor::usage      = "PushTensor[undnL, fromT, coSys, newCoSys, rightRule, leftRule, <simpCmd>]"
Ttransform::usage      = "Ttransform[oldT<name>, newT<name>, coSys, newCoSys, <simpCmd>]"

Commutator::usage  = "Commutator[vecMatrix, <simpCmd>]"
LineElement::usage = "LineElement[coSys, metric, <simpCmd>]"

(********************************************************************)
Begin["`Private`"]

(*********************** Tensor Operations **************************)

(***** CDtoGamma *****)
CDtoGamma[expr_]                            := CDtoGamma[expr, CD]
CDtoGamma[expr_, covD_?DerivativeOperatorQ] := forEachObject[expandObject[expr], {}, cdToGammaTensor, covD, KindOf[covD]]
CDtoGamma[___] := Message[CDtoGamma::usage]

    cdToGammaTensor[covD_[a_, expr_], covD_, kind_] :=
        Module[ {rc = BD[a, expr], indexL, gamSymb, dummyDn, dummyUp, i},
            (* remove contracted indices *)
            indexL = dropPairs @ findIndices @ expr;

            gamSymb = getDerOp[Gamma][covD];
            If [indexL =!= {},
                {dummyDn, dummyUp} = DummyPair[kind];
                Do [
                    aIndex = indexL[[i]];
                    If [DnIndexQ[aIndex], rc -= gamSymb[a, aIndex, dummyUp] * (expr /. aIndex -> dummyDn),
                    (* else *)            rc += gamSymb[a, dummyDn, aIndex] * (expr /. aIndex -> dummyUp)],

                    {i, Length[indexL]}
                ]
            ];
            rc
        ] /; !freeObjectQ[expr] && FreeQ[expr, BD | Alternatives @@ nonTensorList]
    cdToGammaTensor[covD_[a_, expr_], covD_, kind_] := BD[a, cdToGammaTensor[expr, covD, kind]] /; freeObjectQ[expr]
    cdToGammaTensor[BD[a_, expr_],    covD_, kind_] := BD[a, cdToGammaTensor[expr, covD, kind]]
    cdToGammaTensor[expr_,              ___]        := expr

CommuteCD[idxL_List, expr_]                            := CommuteCD[idxL, expr, CD]
CommuteCD[idxL_List, expr_, covD_?DerivativeOperatorQ] :=
    With[ {kind = KindOf[covD]},
        If [!ValidIndicesQ[idxL, kind], Return[expr]];

        forEachObject[expandObject[expr], {}, commuteCDTensor, idxL, covD, kind]
    ] /; Length[idxL] === 2 && AllTrue[idxL, RegularIndexQ]
CommuteCD[___] := Message[CommuteCD::usage]

    commuteCDTensor[opName_[a_, expr_],          {_, _},   covD_, kind_] := opName[a, expr]  (* do nothing *)                                                      \
                                                                            /; !FreeQ[expr, BD | Alternatives @@ nonTensorList]  (* for BD or improper tensors *)  \
                                                                               || (opName === covD && FreeQ[expr, covD])         (* for one CovD *)                \
                                                                               || freeObjectQ[expr]
    commuteCDTensor[covD_[c_, expr_],            {a_, b_}, covD_, kind_] := covD[c, commuteCDTensor[expr, {a, b}, covD, kind]] /; a =!= c && b =!= c
    commuteCDTensor[covD_[a_, covD_[b_, expr_]], {a_, b_}, covD_, kind_] := commuteCDTensorAux[a, b, expr, covD, kind] /; ObjectQ[Head[expr]]
    commuteCDTensor[covD_[b_, covD_[a_, expr_]], {a_, b_}, covD_, kind_] := commuteCDTensorAux[b, a, expr, covD, kind] /; ObjectQ[Head[expr]]
    commuteCDTensor[LD[aV_, expr_],              {a_, b_}, CD,    kind_] := LD[aV, commuteCDTensor[{a, b}, expr, CD, kind]]
    commuteCDTensor[expr_,                       ___]                    := expr

        commuteCDTensorAux[a_, b_, expr_, covD_, kind_] :=
            Module[ {rc, indexL, rSymb, dummyDn, dummyUp, i},
                rc = covD[b, covD[a, expr]];  (* CovD[a,b, T]] = CovD[b,a, T]] + ... *)

                (* get indices and then remove contracted indices *)
                indexL = dropPairs @ findIndices @ expr;

                If [indexL =!= {},
                    {dummyDn, dummyUp} = DummyPair[kind];
                    rSymb = getDerOp[Riemann][covD];
                    Do [
                        aIndex = indexL[[i]];
                        If [DnIndexQ[aIndex], rc = rc - (riemannSign) * rSymb[a, b, aIndex, dummyUp] * (expr /. aIndex -> dummyDn),
                        (* else *)            rc = rc + (riemannSign) * rSymb[a, b, dummyDn, aIndex] * (expr /. aIndex -> dummyUp)],

                        {i, Length[indexL]}
                    ]
                ];

                If [!TorsionFreeQ[covD],
                    {dummyDn, dummyUp} = DummyPair[kind];
                    rc -= GetTorsion[kind][a, b, dummyUp] covD[dummyDn, expr]
                ];

                rc
            ]

(***** GammaToMetric *****)
GammaToMetric[expr_]                            := GammaToMetric[expr, CD]
GammaToMetric[expr_, covD_?DerivativeOperatorQ] :=
    With[ {kind = KindOf[covD]},
        If [!MetricSpaceQ[kind], Message[Msg::err, kind, "is not a metric space", "", ""]; Return[expr]];

        forEachObject[expandObject[expr], {}, gammaToMetricTensor, covD, kind]
    ]
GammaToMetric[___] := Message[GammaToMetric::usage]

    gammaToMetricTensor[tName_[a_, b_, c_], covD_, kind_] :=
        Module[ {metric = GetMetric[kind], rc, p, q, r, addSymb},
            Switch [DnIndexQ /@ {a, b, c},
                {True,  True,  True},  rc = dndndnGamma[a, b, c, metric],
                {True,  True,  False}, p = Dummy[kind]; rc = metric[c, FlipIndex[p]] * dndndnGamma[a, b, p, metric],
                {True,  False, True},  p = Dummy[kind]; rc = metric[b, FlipIndex[p]] * dndndnGamma[a, p, c, metric],
                {True,  False, False}, {p, q} = {Dummy[kind], Dummy[kind]};
                                       rc = metric[b, FlipIndex[p]] * metric[c, FlipIndex[q]] * dndndnGamma[a, p, q, metric],
                {False, True,  True},  p = Dummy[kind]; rc = metric[a, FlipIndex[p]] * dndndnGamma[p, b, c, metric],
                {False, True,  False}, {p, q} = {Dummy[kind], Dummy[kind]};
                                       rc = metric[a, FlipIndex[p]] * metric[c, FlipIndex[q]] * dndndnGamma[p, b, q, metric],
                {False, False, True},  {p, q} = {Dummy[kind], Dummy[kind]};
                                       rc = metric[a, FlipIndex[p]] * metric[b, FlipIndex[q]] * dndndnGamma[p, q, c, metric],
                {False, False, False}, {p, q, r} = {Dummy[kind], Dummy[kind], Dummy[kind]};
                                       rc = metric[a, FlipIndex[p]]*metric[b, FlipIndex[q]]*metric[c, FlipIndex[r]] * dndndnGamma[p, q, r, metric]
            ];

            If [!CoordinateBasisQ[kind],
                addSymb = GetStructuref[kind];
                rc += ( addSymb[a, b, c] + addSymb[c, a, b] + addSymb[c, b, a] ) / 2
            ];
            If [!TorsionFreeQ[covD],
                addSymb = GetTorsion[kind];
                rc += ( addSymb[a, b, c] + addSymb[c, a, b] + addSymb[c, b, a] ) / 2
            ];
            rc
        ] /; tName === getDerOp[Gamma][covD]
    gammaToMetricTensor[BD[a_, expr_], covD_, kind_] := BD[a, gammaToMetricTensor[expr, covD, kind]]
    gammaToMetricTensor[expr_, ___]                  := expr

        dndndnGamma[a_, b_, c_, metric_] := ( BD[a, metric[b, c]] + BD[b, metric[a, c]] - BD[c, metric[a, b]] ) / 2

(***** LDtoCD: LD to torsion-free CD *****)
LDtoCD[expr_]                            := LDtoCD[expr, CD]
LDtoCD[expr_, BD]                        := forEachObject[expandObject[expr], {}, ldToCDTensor, BD]
LDtoCD[expr_, covD_?DerivativeOperatorQ] := If [TorsionFreeQ[covD], forEachObject[expandObject[expr], {}, ldToCDTensor, covD],
                                            (* else *)              Message[Msg::warn, covD, "is not torsion-free", "", ""]; expr]
LDtoCD[___]                              := Message[LDtoCD::usage]

    ldToCDTensor[LD[aV_, expr_],    covD_] := LD[aV, expr] /; !FreeQ[expr, BD | Alternatives @@ nonTensorList] || freeObjectQ[expr]  (* for BD or improper tensors *)
    ldToCDTensor[BD[a_,  expr_],    covD_] := BD[a, expr]  /; covD =!= BD  (* improper tensor *)
    ldToCDTensor[covD_[a_,  expr_], covD_] := covD[a, ldToCDTensor[expr, covD]] /; covD === BD || FreeQ[expr, BD | Alternatives @@ nonTensorList] || freeObjectQ[expr]
    ldToCDTensor[LD[aV_, expr_],    covD_] :=
        With[ {kind = KindOf[aV]},
             If [!kindMatchQ[kind, KindOf @ aV],
                 LD[aV, expr],  (* do nothing *)
             (* else *)
                Module[ {dummyDn, dummyUp, rc, indexL},
                    {dummyDn, dummyUp} = DummyPair[kind];
                    rc = aV[dummyUp] * covD[dummyDn, expr];  (* LD_V T = V^p \del_p T + ... *)

                    (* get indices and then remove contracted indices *)
                    indexL = Select[dropPairs @ findIndices @ expr, ValidIndexQ[#, kind]&];

                    If [indexL =!= {},
                        {dummyDn, dummyUp} = DummyPair[kind];
                        Do [
                            aIndex = indexL[[i]];
                            If [DnIndexQ[aIndex], rc += covD[aIndex, aV[dummyUp]] * (expr /. aIndex -> dummyDn),
                            (* else *)            rc -= covD[dummyDn, aV[aIndex]] * (expr /. aIndex -> dummyUp)],

                            {i, Length[indexL]}
                        ]
                    ];
                    rc
                ]
             ]
        ] /; vectorNameQ[aV]
    ldToCDTensor[expr_, ___] := expr

(***** RiemannToGamma *****)
(* If curvRL === {}, convert all. But, if curvRL =!= {}, convert only those contained in curvRL. *)
RiemannToGamma[expr_]                                         := RiemannToGamma[expr, {}]
RiemannToGamma[expr_,              covD_Symbol]               := RiemannToGamma[expr, {},     covD]
RiemannToGamma[expr_, curvRL_List]                            := RiemannToGamma[expr, curvRL, CD]
RiemannToGamma[expr_, curvRL_List, covD_?DerivativeOperatorQ] :=
    forEachObject[expandObject[expr], {}, riemannToGammaTensor, curvRL, covD, KindOf[covD]]  \
    /; And @@ (MemberQ[{getDerOp[Riemann][covD], getDerOp[Ricci][covD], getDerOp[Scalar][covD]}, #]& /@ curvRL)
RiemannToGamma[___] := Message[RiemannToGamma::usage]

    riemannToGammaTensor[opName_[a_,  expr_],    _,       covD_, kind_] := opName[a,  expr] /; DerivativeOperatorQ[opName]  (* do nothing *)
    riemannToGammaTensor[LD[aV_, expr_],         _,       covD_, kind_] := LD[aV, expr]                                     (* do nothing *)
    riemannToGammaTensor[BD[a_,  expr_],         curvRL_, covD_, kind_] := BD[a, riemannToGammaTensor[expr, curvRL, covD, kind]]
    riemannToGammaTensor[tName_[a_, b_, c_, d_], curvRL_, covD_, kind_] :=
        riemannToGammaAux[a, b, c, d, covD, kind] /; tName === getDerOp[Riemann][covD] && (curvRL === {} || MemberQ[curvRL, tName])
    riemannToGammaTensor[tName_[a_, b_],         curvRL_, covD_, kind_] :=
        Module[ {dummyDn, dummyUp},
            {dummyDn, dummyUp} = DummyPair[kind];
            riemannToGammaAux[a, dummyDn, b, dummyUp, covD, kind]
        ] /; tName === getDerOp[Ricci][covD] && (curvRL === {} || MemberQ[curvRL, tName])
    riemannToGammaTensor[tName_[],               curvRL_, covD_, kind_] :=
        Module[ {dummyDn1, dummyUp1, dummyDn2, dummyUp2},
            {dummyDn1, dummyUp1} = DummyPair[kind]; {dummyDn2, dummyUp2} = DummyPair[kind];
            riemannToGammaAux[dummyDn1, dummyDn2, dummyUp1, dummyUp2, covD, kind]
        ] /; tName === getDerOp[Scalar][covD] && (curvRL === {} || MemberQ[curvRL, tName])
    riemannToGammaTensor[expr_, ___] := expr

        riemannToGammaAux[a_, b_, c_, d_, covD_, kind_] := -riemannToGammaAux[b, a, c, d, covD, kind] /; UpIndexQ[a] && DnIndexQ[b] (* ordering to {dn, up, _, _} *)
        riemannToGammaAux[a_, b_, c_, d_, covD_, kind_] := -riemannToGammaAux[a, b, d, c, covD, kind] /; UpIndexQ[c] && DnIndexQ[d] (* ordering to {_, _, dn, up} *)
        riemannToGammaAux[a_, b_, c_, d_, covD_, kind_] :=
            Module[ {rc, gamSymb = getDerOp[Gamma][covD], metric, p, q, r},
                If [AllTrue[{a, b, c}, DnIndexQ] && UpIndexQ[d],  (* if not need the metric *)
                    rc = dndndnupDerGamma[a, b, c, d, gamSymb],
                (* else *)
                    If [!MetricSpaceQ[kind], Return[ getDerOp[Riemann][covD][a, b, c, d] ]];  (* do nothing *)

                    metric = GetMetric[kind];
                    Switch [Map[DnIndexQ, {a, b, c, d}],
                        {True,  True,  True,  True},  p = Dummy[kind]; rc = metric[d, p] * dndndnupDerGamma[a, b, c, FlipIndex[p], gamSymb],
                        {True,  True,  False, False}, p = Dummy[kind]; rc = metric[c, FlipIndex[p]] * dndndnupDerGamma[a, b, p, d, gamSymb],
                        {True,  False, True,  False}, p = Dummy[kind]; rc = metric[b, FlipIndex[p]] * dndndnupDerGamma[a, p, c, d, gamSymb],
                        {True,  False, True,  True},  p = Dummy[kind]; q = Dummy[kind];
                                                      rc = metric[b, FlipIndex[p]] * metric[d, q] * dndndnupDerGamma[a, p, c, FlipIndex[q], gamSymb],
                        {True,  False, False, False}, p = Dummy[kind]; q = Dummy[kind];
                                                      rc = metric[b, FlipIndex[p]] * metric[c, FlipIndex[q]] * dndndnupDerGamma[a, p, q, d, gamSymb],
                        {False, False, True,  False}, p = Dummy[kind]; q = Dummy[kind];
                                                      rc = metric[a, FlipIndex[p]] * metric[b, FlipIndex[q]] * dndndnupDerGamma[p, q, c, d, gamSymb],
                        {False, False, True,  True},  p = Dummy[kind]; q = Dummy[kind]; r = Dummy[kind];
                                                      rc = metric[a,FlipIndex[p]]*metric[b,FlipIndex[q]]*metric[d,r]*dndndnupDerGamma[p,q,c,FlipIndex[r],gamSymb],
                        {False, False, False, False}, p = Dummy[kind]; q = Dummy[kind]; r = Dummy[kind];
                                                      rc = metric[a,FlipIndex[p]]*metric[b,FlipIndex[q]]*metric[c,FlipIndex[r]]*dndndnupDerGamma[p,q,r,d,gamSymb]
                    ]
                ];
                p = Dummy[kind];
                rc += gamSymb[a, p, d] * gamSymb[b, c, FlipIndex[p]] - gamSymb[b, p, d] * gamSymb[a, c, FlipIndex[p]];

                If [!CoordinateBasisQ[kind],
                    p = Dummy[kind];
                    rc -= GetStructuref[kind][a, b, FlipIndex[p]] * gamSymb[p, c, d]
                ];
                (riemannSign) * rc
            ]

            dndndnupDerGamma[a_, b_, c_, d_, gam_] := BD[a, gam[b, c, d]] - BD[b, gam[a, c, d]]

(***** RiemannToWeyl and WeylToRiemann *****)
RiemannToWeyl[expr_]                            := RiemannToWeyl[expr, CD]
RiemannToWeyl[expr_, covD_?DerivativeOperatorQ] :=
    Module[{kind = KindOf[covD],
            riemann = getDerOp[Riemann][covD], weyl = getDerOp[Weyl][covD], ricci = getDerOp[Ricci][covD], scalar = getDerOp[Scalar][covD]},
        If [!MetricSpaceQ[kind], Message[Msg::warn, kind, "is not a metric space", "", ""]];

        expr /. riemannToWeylRule[riemann, GetMetric[kind], GetDimension[kind], weyl, ricci, scalar]
    ] /; MemberQ[definedKindList, KindOf[covD]]
RiemannToWeyl[___] := Message[RiemannToWeyl::usage]

    riemannToWeylRule[riemann_, metric_, nDim_, weyl_, ricci_, scalar_] := {
            riemann[a_,b_,c_,d_] :>
                weyl[a,b,c,d]
                    + (riemannSign) * (
                        - (metric[a,c] ricci[b,d] - metric[a,d] ricci[b,c]
                           + metric[b,d] ricci[a,c] - metric[b,c] ricci[a,d]) / (nDim - 2)
                        + scalar[] (metric[a,c] metric[b,d] - metric[a,d] metric[b,c]) / (nDim-1) / (nDim-2)
                    )
        }

WeylToRiemann[expr_]                            := WeylToRiemann[expr, CD]
WeylToRiemann[expr_, covD_?DerivativeOperatorQ] :=
    Module[{kind = KindOf[covD],
            weyl = getDerOp[Weyl][covD], riemann = getDerOp[Riemann][covD], ricci = getDerOp[Ricci][covD], scalar = getDerOp[Scalar][covD]},
        If [!MetricSpaceQ[kind], Message[Msg::warn, kind, "is not a metric space", "", ""]];

        expr /. weylToRiemannRule[weyl, GetMetric[kind], GetDimension[kind], riemann, ricci, scalar]
    ] /; MemberQ[definedKindList, KindOf[covD]]
WeylToRiemann[___] := Message[WeylToRiemann::usage]

    weylToRiemannRule[weyl_, metric_, nDim_, riemann_, ricci_, scalar_] := {
            weyl[a_,b_,c_,d_] :>
                riemann[a,b,c,d]
                    - (riemannSign) * (
                        - (metric[a,c] ricci[b,d] - metric[a,d] ricci[b,c]
                           + metric[b,d] ricci[a,c] - metric[b,c] ricci[a,d]) / (nDim - 2)
                        + scalar[] (metric[a,c] metric[b,d] - metric[a,d] metric[b,c]) / (nDim-1) / (nDim-2)
                    )
        }

(****************** Set/Clear Tensor Components *********************)

SetAttributes[SetComponents, HoldFirst]
SetComponents[(tName_?IndexedOperandQ)[indices___], expr_] :=  (* set one component *)
    Module[ {indexL = {indices}, len, tSymL},
        If [indexL === {}, tName[] = expr; Return[]];

        If [!checkComponentIndices[tName, indexL], Return[]];

        (* generates all symmetries of tName and then convert to Imag notation *)
        len = Length[indexL];
        tSymL = MakePermGroup[getGenSetOf[tName[indices]], len];
        If [tSymL === {},
            tName[indices] = expr,
        (* else *)
            tSymL = ToImag[#, len]& /@ tSymL;
            (tName[ Sequence @@ indexL[[ List @@ (signTerm[#] * #) ]] ] = signTerm[#] * expr)& /@ tSymL
        ];
    ] /; AllTrue[{indices}, ComponentIndexQ]
SetComponents[(tName_?IndexedOperandQ)[indices___], cTable_List] :=  (* set all components *)
    With[ {nRank = GetRank[tName], len = Length[{indices}]},
        If [nRank =!= -1 && len =!= nRank, Message[Msg::err, "invalid number of indices", {indices}, "with rank", nRank]; Return[]];
        If [len =!= ArrayDepth[cTable], Message[Msg::err, "incompatible components", "for a rank", len, ""]; Return[]];

        tableToComponents[tName, len, dnupListFrom[indices], cTable];
    ] /; AllTrue[{indices}, TensorialIndexQ]
SetComponents[___] := Message[SetComponents::usage]

SetAttributes[ClearComponents, HoldAll]
ClearComponents[(tName_?IndexedOperandQ)[indices___]] :=  (* clear one component *)
    Module[ {indexL = {indices}, len, tSymL},
        If [indexL === {} && ValueQ[tName[]], tName[] = .; Return[]];
        If [!checkComponentIndices[tName, indexL], Return[]];

        (* generates all symmetries of tName with ignoring the sign and then convert to Imag notation *)
        len = Length[indexL];
        tSymL = {#[[1]],+1}& /@ MakePermGroup[getGenSetOf[tName, len]];
Off[Unset::norep];
        If [tSymL === {},
            tName[indices] = .,
        (* else *)
            tSymL = ToImag[#, len]& /@ tSymL;
            tSymL = DeleteDuplicates[ indexL[[List @@ #]]& /@ tSymL ];  (* drop duplicate indices of tName: {1,1}[[1,2]] == {1,1}[[2,1]] *)
            (tName[ Sequence @@ # ] = .)& /@ tSymL
        ];
On[Unset::norep];
    ] /; AllTrue[{indices}, ComponentIndexQ]
ClearComponents[(tName_?IndexedOperandQ)[indices___]] :=  (* clear all components *)
    Module[ {i, len = Length[{indices}], n, dims = {}},
        For [i = 1, i <= len, ++i,
            n = GetDimension[KindOf[tName, i]];
            If [!PositiveIntegerQ[n], Message[Msg::err, "need to set dimension for the index", {indices}[[i]], "", ""]; Return[]];
            AppendTo[dims, n]
        ];

        clearComponents[tName, len, dims, dnupListFrom[indices]];
    ] /; AllTrue[{indices}, TensorialIndexQ]
ClearComponents[(tName_?IndexedOperandQ)[indices___], dims_?VectorQ] :=  (* clear all components *)
    Module[ {len = Length[{indices}], i, n},
        If [len =!= Length[dims], Message[Msg::err, "invalid format for the dimensions", dims, "", ""]; Return[]];
        For [i = 1, i <= len, ++i,
            n = GetDimension[KindOf[tName, i]];
            If [PositiveIntegerQ[n] && dims[[i]] > n, Message[Msg::err, "invalid input", dims[[i]], "for the dimension", n]; Return[]];
        ];

        clearComponents[tName, len, dims, dnupListFrom[indices]];
    ] /; AllTrue[{indices}, TensorialIndexQ]
ClearComponents[___] := Message[ClearComponents::usage]

    clearComponents[tName_, len_, dims_, dnupL_] :=
        Module[{tIndexL, expr1, i},
            tIndexL = Table[Unique["m"], {i, len}];  (* dummy indices for Table *)
            expr1 = Inner[List, tIndexL, dims, Sequence];

Off[Unset::norep];
            Table[ tName[Sequence @@ (dnupL * tIndexL)] = ., Evaluate[expr1] ];  (* clear all components *)
On[Unset::norep];
        ]

checkComponentIndices[tName_, indexL_List] :=
    Module[ {nRank = GetRank[tName], len = Length[indexL], i},
        If [nRank =!= -1 && len =!= nRank, Message[Msg::err, "incompatible number of indices", indexL, "with rank", nRank]; Return[False]];

        For [i = 1, i <= Length[indexL], ++i,
            If [!ValidIndexQ[indexL[[i]], KindOf[tName, i], True],  Return[False]]
        ];

        True
    ]

dnupListFrom[args___] := dnupState /@ {args}

(* set components in Table-format *)
tableToComponents[tName_, 0,    {},     value_]  := (tName[] = value;)
tableToComponents[tName_, len_, dnupL_, cTable_] :=
    Module[ {i, n, dims = Dimensions[cTable], tIndexL, expr1, expr2},
        For [i = 1, i < len, ++i,
            n = GetDimension[KindOf[tName, i]];
            If [PositiveIntegerQ[n] && dims[[i]] > n,
                Message[Msg::err, "invalid input for a ", i, "th dimension", n]; Return[]
            ]
        ];

        tIndexL = Table[Unique["m"], {i, len}];  (* dummy indices for Table *)

        expr1 = Hold[cTable[[ Sequence @@ tIndexL ]]];
        expr2 = Inner[List, tIndexL, dims, Sequence];

        (* set values into the corresponding tensor components *)
        Table[ tName[Sequence @@ (dnupL * tIndexL)] = ReleaseHold[expr1], Evaluate[expr2] ];
    ]

(******************* Coordinate Transformation **********************)

Pushforward[fromV_?VectorQ, coSys_?VectorQ, newCoSys_?VectorQ, simpCmd_:Simplify] :=
    With[ {trM = Table[D[newCoSys, coSys[[i]]], {i, Length[coSys]}] // simpCmd},
        Transpose[trM] . fromV // simpCmd
    ]
Pushforward[fromM_?MatrixQ, coSys_?VectorQ, newCoSys_?VectorQ, simpCmd_:Simplify] :=
    With[ {trM = Table[D[newCoSys, coSys[[i]]], {i, Length[coSys]}] // simpCmd},
        Transpose[trM] . fromM . trM // simpCmd
    ]
Pushforward[fromT_?ArrayQ, coSys_?VectorQ, newCoSys_?VectorQ, simpCmd_:Simplify] :=
    With[{trM = Table[D[newCoSys, coSys[[i]]], {i, Length[coSys]}] // simpCmd},
        pushpull[fromT, Transpose[trM], Length[coSys], Length[newCoSys], simpCmd]
    ] /; ArrayDepth[fromF] > 2

Pullback[fromF_?VectorQ, coSys_?VectorQ, newCoSys_?VectorQ, simpCmd_:Simplify] :=
    With[ {trM = Table[D[newCoSys, coSys[[i]]], {i, Length[coSys]}] // simpCmd},
        trM . fromF // simpCmd
    ]
Pullback[fromM_?MatrixQ, coSys_?VectorQ, newCoSys_?VectorQ, simpCmd_:Simplify] :=
    With[ {trM = Table[D[newCoSys, coSys[[i]]], {i, Length[coSys]}] // simpCmd},
        trM . fromM . Transpose[trM] // simpCmd
    ]
Pullback[fromT_?ArrayQ, coSys_?VectorQ, newCoSys_?VectorQ, simpCmd_:Simplify] :=
    With[{trM = Table[D[newCoSys, coSys[[i]]], {i, Length[coSys]}] // simpCmd},
        pushpull[fromT, trM, Length[newCoSys], Length[coSys], simpCmd]
    ] /; ArrayDepth[fromF] > 2

PushTensor[updnL_?VectorQ, fromT_?ArrayQ, coSys_?VectorQ, newCoSys_?VectorQ, rightRule_List, leftRule_List, simpCmd_:Simplify] :=
    Module[{rightM, leftM},
        (* check the rank *)
        If [Length[updnL] =!= ArrayDepth[fromT], Message[Msg::err, "incompatible ranks between", updnL, "and", fromT]; Return[]];

        rightM = Table[D[newCoSys /. rightRule, coSys[[i]]], {i, Length[coSys]}] // simpCmd;
        leftM = Table[D[coSys /. leftRule, newCoSys[[i]]], {i, Length[newCoSys]}] // simpCmd;
        pushTensor[updnL, fromT, rightM, leftM, Length[coSys], Length[newCoSys], simpCmd]
    ]

    pushpull[fromT_?ArrayQ, trM_?MatrixQ, fromDim_Integer, toDim_Integer, simpCmd_] := (* Pushforward or Pullback *)
        Module[{rank = ArrayDepth[fromT], idxL, rcL, i, m},
            idxL = Unique /@ (("i" <> #)& /@ ToString /@ Range[rank]);
            rcL = pushpullAUX[fromT, idxL];
            Do [
                rcL = rcL /. {idxL[[i]] -> m};
                rcL = Table[Sum[trM[[a, m]] rcL, {m, fromDim}], {a, toDim}] // simpCmd,

                {i, rank, 1, -1}
            ];
            rcL
        ]

    pushTensor[updnL_?VectorQ, fromT_?ArrayQ, rightM_?MatrixQ, leftM_?MatrixQ, fromDim_Integer, toDim_Integer, simpCmd_] :=
        Module[{rank = ArrayDepth[fromT], idxL, rcL, i, a, m},
            idxL = Unique /@ (("i" <> #)& /@ ToString /@ Range[rank]);
            rcL = pushpullAUX[fromT, idxL];
            Do [
                rcL = rcL /. {idxL[[i]] -> m};

                If [DnIndexQ[updnL[[i]]],
                    rcL = Table[Sum[leftM[[a, m]] rcL, {m, fromDim}], {a, toDim}] // simpCmd,
                (* else *)
                    rcL = Table[Sum[Transpose[rightM][[a, m]] rcL, {m, fromDim}], {a, toDim}] // simpCmd
                ],

                {i, rank, 1, -1}
            ];
            rcL
        ]

        pushpullAUX[fromT_, idxL:{__Integer}] := fromT[[Sequence @@ idxL]]

(* For diffeomorphic transformations *)
Ttransform[fromT:(fromTname_?IndexedTensorQ)[indices__], toTname_Symbol?IndexedTensorQ,
           leftCoSys_?VectorQ,                           rightCoSys_?VectorQ, simpCmd_:Simplify] :=
    Module[ {nDim = Length[leftCoSys], MM, upM, dnM, i},
        If [!checkTtransform[fromTname, toTname, nDim, leftCoSys, rightCoSys], Return[]];

        MM = Table[D[rightCoSys, leftCoSys[[i]]], {i, nDim}];
        upM = Transpose[MM] // simpCmd;  (* contravariant, -> *)
        dnM = Inverse[MM] // simpCmd;    (* covariant,     -> *)

        tTransformAUX[fromT, toTname, upM, dnM, nDim, simpCmd];
    ]
Ttransform[toTname_Symbol?IndexedTensorQ, fromT:(fromTname_?IndexedTensorQ)[indices__],
           leftCoSys_?VectorQ,            rightCoSys_?VectorQ, simpCmd_:Simplify] :=
    Module[ {nDim = Length[leftCoSys], MM, invUpM, invDnM, i},
        If [!checkTtransform[fromTname, toTname, nDim, leftCoSys, rightCoSys], Return[]];

        MM = Table[D[rightCoSys, leftCoSys[[i]]], {i, nDim}];
        invDnM = MM // simpCmd;                      (* covariant,     <- *)
        invUpM = Transpose[Inverse[MM]] // simpCmd;  (* contravariant, <- *)

        tTransformAUX[fromT, toTname, invUpM, invDnM, nDim, simpCmd];
    ]
Ttransform[___] := Message[Ttransform::usage]

    checkTtransform[fromTname_, toTname_, nDim_, leftCoSys_, rightCoSys_] := (
            (* check the rank *)
            If [GetRank[fromTname] =!= GetRank[toTname], Message[Msg::err, "incompatible ranks between", fromTname, "and", toTname]; Return[False]];

            If [nDim =!= Length[rightCoSys],  (* diffeomorphic *)
                Message[Msg::err, "incompatible coordinate systems between", leftCoSys, "and", rightCoSys]; Return[False]
            ];
            True
        )

    tTransformAUX[fromT:_[indices__], toTname_, upM_, dnM_, fromDim_, simpCmd_] :=
    (* NB: only considered dn/up signature, i.e., contracted pairs are not considered. *)
        Module[ {toDim, i, aIndexL = {indices}, rcL = fromT, a, m},
            toDim = fromDim;  (* diffeomorphic *)
            Do [
                If [DnIndexQ[aIndexL[[i]]],
                    (* prepare for Table generation: i-th indices -> component indices *)
                    rcL = rcL /. {aIndexL[[i]] -> -m};

                    rcL = Table[ Sum[dnM[[a, m]] rcL, {m, fromDim}], {a, toDim} ] // simpCmd,
                (* else *)
                    rcL = rcL /. {aIndexL[[i]] -> m};
                    rcL = Table[ Sum[upM[[a, m]] rcL, {m, fromDim}], {a, toDim} ] // simpCmd
                ],

                {i, Length[aIndexL], 1, -1}
            ];
            SetComponents[toTname[indices], rcL // simpCmd];
        ]

(************************* Misc. Commands ***************************)

(***** Commutator *****)

Commutator[vecList_?MatrixQ,              simpCmd_:Together] := Commutator[vecList, DefaultKind, simpCmd]
Commutator[vecList_?MatrixQ, kind_Symbol, simpCmd_:Together] :=
(* return commutation relations between two or more vectors *)
    Module[ {nDim = GetDimension[kind], nV, nullV, v1, v2, rc, i, j},
        If [!checkIndexKind[kind, True], Return[]];

        If [!VectorQ[tCoordinates[kind]], Message[Msg::err, "need to run SetCoordinates[..]", "", "", ""]; Return[]];

        If [!AllTrue[vecList, Length[#] === nDim], Message[Msg::err, "invalid number of components.", "", "", ""]; Return[]];

        nV = Length[Transpose[vecList][[1]]];  (* # of vectors *)
        nullV = Table[0, {i, nDim}];           (* null vector *)
        Do [
            v1 = vecList[[i]];
            Do [
                v2 = vecList[[j]];
                rc = commutatorTwoVectors[v1, v2, simpCmd, nDim, kind];
                If [rc =!= nullV, Print[SequenceForm[Subscript["[V", i], ",", Subscript["V", j], "] = ", rc]]],

                {j, i + 1, nV}
            ],
            {i, nV - 1}
        ]
    ]
Commutator[v1_?VectorQ, v2_?VectorQ,              simpCmd_:Together] := Commutator[v1, v2, DefaultKind, simpCmd]
Commutator[v1_?VectorQ, v2_?VectorQ, kind_Symbol, simpCmd_:Together] :=
    With[ {nDim = GetDimension[kind]},
        If [!checkIndexKind[kind, True], Return[]];

        If [!VectorQ[tCoordinates[kind]], Message[Msg::err, "need to run SetCoordinates[..]", "", "", ""]; Return[]];

        If [!(nDim == Length[v1] == Length[v2]), Message[Msg::err, "incompatible vectors", "", "", ""]; Return[]];

        commutatorTwoVectors[v1, v2, simpCmd, nDim, kind]
    ]
Commutator[___] := Message[Commutator::usage]

    commutatorTwoVectors[v1_List, v2_List, simpCmd_, nDim_, kind_] :=
    (* commutator between two vectors: v1 = {comp1, comp2,...} *)
        Module[ {rc1, rc2, rcL1 = {}, rcL2 = {}, i, j},
            Do [
                rc1 = 0; rc2 = 0;
                For [j = 1, j <= nDim, j++,
                    rc1 += v1[[j]] bdD[j, v2[[i]], kind]; rc2 += v2[[j]] bdD[j, v1[[i]], kind]
                ];
                AppendTo[rcL1, rc1]; AppendTo[rcL2, rc2],

                {i, nDim}
            ];
            (rcL1 - rcL2) // simpCmd
        ]

(***** LineElement *****)

LineElement[coSys_?VectorQ, metric_?SquareMatrixQ, simpCmd_:Together] :=
(* print line element *)
    Module[ {nDim = Length[coSys], rc = 0, i, j},
        If [nDim =!= Length[metric[[1]]], Message[Msg::err, "incompatible metric with", coSys, "", ""]; Return[]];

        Do [
            Do [
                If [i === j, rc = rc + metric[[i,j]] Row[{"d", Superscript[coSys[[i]], 2]}],
                (* else *)   rc = rc + 2 metric[[i,j]] Row[{"d", coSys[[i]], "d", coSys[[j]]}]],

                {j, i, nDim}
            ],

            {i, nDim}
        ];
        Row[{"d", Superscript["s",2], " = ", rc // simpCmd}]
    ]
LineElement[___] := Message[LineElement::usage]

(********************************************************************)
initTensorGRG[] := (
        (* the sign convention of RiemannCD *)
        riemannSign = -1;

		(***** Finish initTensorGRG *****)
		loadedTensorGRG = True;  (* guard reloding *)
    )
initTensorGRG[]

(********************************************************************)
End[ ] (* end the private context *)

EndPackage[ ]  (* end the package context *)

(********************************************************************)
