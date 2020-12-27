(* :Title: xToCanonical.m *)
(* :Context: mTensor` *)
(* :Summary: xTensor's ToCanonical for mTensor *)
(* :Package Version: 2020.12 *)
(* :Mathematica Version: 10.4 *)

(********************************************************************)
BeginPackage["mTensor`", {"mTensor`xPermML`"}]

(********************************************************************)
Begin["`Private`"]

errObject/: MakeBoxes[errObject[obj_], StandardForm] := interpretBox[errObject[obj], ToBoxes @ obj]

(************************* flattenObject ****************************)
(***** The flattened Object structure:
    xObject[obj, nameL, {aIndexL, freeL, dummyL, metricStates}]

        metricStates =
            {Up/Dn, Null,   _}     : no metric or blocked by non-metric-compatible derivatives. Index cannot up/dn and metric cannot be moved.
            {Up/Dn, metric, 0}     : there is a metric. Index can up/dn and metric cannot be moved. (See moveFlag)
            {Up/Dn, metric, +1/-1} : there is a metric. Index can up/dn and metric can be moved.
 *****)

(* for any objects and CD-type operators *)
metricState[idx_?TensorialIndexQ, Kdelta,                   _]      := {dnupState[idx], GetMetric[indexKind @ idx], 0}
metricState[idx_?TensorialIndexQ, opName_?IndexedOperatorQ, cOptL_] :=
    With [{kind = indexKind[idx]},
        {dnupState[idx], GetMetric[kind], If [covariantNameQ[opName, idx, cOptL], metricSymmetry[kind], 0]}
    ]
metricState[idx_?TensorialIndexQ, oName_?IndexedOperandQ, _] := With [{kind = indexKind[idx]}, {dnupState[idx], GetMetric[kind], metricSymmetry[kind]}]
metricState[idx_?ComponentIndexQ, _, _] := {dnupState[idx], Null, 0} (* NB: component indices can NOT be contracted, so {_, Null, 0} *)
metricState[idx_,                 __]   := {dnupState[idx], Null, 0} (* internal error *)

flattenObject[expr_Plus,  _]      := $flattenOTHER[expr]  (* Message[Msg::err, "flattenObject:", "not for Plus expressions", expr, ""] *)
flattenObject[expr_Times, cOptL_] := flattenObject[#, cOptL]& /@ xTensorTimes @@ expr

(* for indexed objects *)
flattenObject[oName_?IndexedOperandQ[], _] := If [MemberQ[{0, -1}, GetRank @ oName], xObject[oName[], {oName}, {{}, {}, {}, {}}],  (* scalar or arbitrary rank *)
                                              (* else *)                             errObject[ErrorT[oName][]]]
flattenObject[oName_?IndexedOperandQ[indices__], cOptL_] :=
    Module[{indexL = {indices}},
        If [!checkObject[oName, indexL], Return[errObject[ErrorT[oName][indices]]]];

        With[ {free = dropPairs[indexL], dum = takePairs[indexL]},  (* NB: 'free' includes components indices *)
            xObject[
                oName[Sequence @@ indexL],
                {oName},
                {indexL, free, dum, metricState[#, oName, cOptL]& /@ indexL}
            ]
        ]
    ]
flattenObject[(opName_?IndexedOperatorQ)[arg_, expr___], cOptL_] :=
    Switch [getType[opName],
        CD, If [!ValidIndexQ[arg, KindOf[opName, arg]], Return[errObject[ErrorT[opName][arg, expr]]]];  (* check validity of indices *)
            If [duplicatedIndicesQ @ Join[{arg}, findIndices @ expr], Return[errObject[ErrorT[opName][arg, expr]]]];
            addDerivative[CD, {opName, arg}, flattenObject[expr, cOptL], cOptL],
        LD, addDerivative[LD, {opName, arg}, flattenObject[expr, cOptL], cOptL],
        XD, addDerivative[XD, {opName},      flattenObject[arg,  cOptL], cOptL],
        XP, If [duplicatedIndicesQ[Flatten @ (findIndices /@ {arg, expr})], Return[errObject[ErrorT[opName][arg, expr]]]];  (* check validity of indices *)
            addDerivative[XP, {opName},      {arg, expr},          cOptL]
    ]

    addDerivative[CD, {opName_, opIndex_}, xObject[obj_, nameL_, inds_], cOptL_] :=
        xObject[
            opName[opIndex, obj],
            Join[{opName}, nameL],
            prependIndex[opName, opIndex, reCheckMetricStates[{opName, opIndex}, inds, cOptL], cOptL]
        ]

        prependIndex[op_,  idx_, {indexL_, freeL_, dummyL_, mStates_}, cOptL_] :=
            With[ {pidx = FlipIndex[idx]},
                Which[
                    TensorialIndexQ[idx] && MemberQ[freeL, pidx],  (* idx is contracted with the index in free indices *)
                        {Prepend[indexL, idx], DeleteCases[freeL, pidx], Prepend[Prepend[dummyL, pidx], idx], Prepend[mStates, metricState[idx, op, cOptL]]},
                    True,                                          (* idx is free or a component index *)
                        {Prepend[indexL, idx], Prepend[freeL, idx], dummyL, Prepend[mStates, metricState[idx, op, cOptL]]}
                ]
            ]

    addDerivative[LD, {opName_, vName_}, xObject[obj_, nameL_, inds_], cOptL_] :=
        xObject[
            opName[vName, obj],
            Join[{opName, vName}, nameL],
            reCheckMetricStates[{opName, vName}, inds, cOptL]
        ]
    addDerivative[XD, {opName_}, xObject[obj_, nameL_, inds_], cOptL_] :=
        xObject[
            opName[obj],
            Join[{opName}, nameL],
            reCheckMetricStates[{opName}, inds, cOptL]
        ]

    addDerivative[XP, {opName_}, {args__}, _] := $flattenOTHER[opName[args]]  (* NO canonicalization for XP-type operators *)

    addDerivative[_, {opName_, arg___}, errObject[obj_],       _] := errObject[ErrorT[opName][arg, obj]]
    addDerivative[_, {opName_, arg___}, $flattenOTHER[other_], _] := $flattenOTHER[opName[arg, other]]

flattenObject[Tscalar[expr_], cOptL_] :=
    If [findFreeIndices[expr, HeadQs -> {ObjectQ}] =!= {},
        Return[errObject[ErrorT[Tscalar][expr]]],
    (* else *)
        With [{expr1 = ResetDummies[If[$TOCANONICAL === True, ToCanonical[#, Sequence @@ cOptL]&, Identity] @ Dum @ expr, HeadQs -> {ObjectQ}]},  (* See xSort *)
            xObject[Tscalar[expr1], {expr1}, {{}, {}, {}, {}}]
        ]
    ]

(* Scalar-function of a single argument: e.g., Log[x] *)
flattenObject[x:(sf_?ScalarFunctionQ[expr_]), cOptL_] := If [findFreeIndices[expr, HeadQs -> {ObjectQ}] =!= {}, Return[errObject[ErrorT[sf][expr]]],
                                                         (* else *)                                             addHead1A[x, sf, flattenObject[Tscalar @ expr, cOptL]]]

    addHead1A[x_, head_, xObject[obj_, nameL_, inds_]] := xObject[head[obj], Join[{head}, nameL], inds]

(* Scalar-function of two arguments: e.g., Power[x, n] *)
flattenObject[x:(sf_?ScalarFunctionQ[expr1_, expr2_]), cOptL_] :=
    If [findFreeIndices[expr1, HeadQs -> {ObjectQ}] =!= {},
        Return[errObject[ErrorT[sf][expr1, expr2]]],
    (* else *)
        If [findFreeIndices[expr2, HeadQs -> {ObjectQ}] =!= {},
            Return[errObject[ErrorT[sf][expr1, expr2]]],
        (* else *)
            xObject[sf[expr1, expr2], Join[{sf}, {expr1}, {expr2}], {{}, {}, {}, {}}]
        ]
    ]

flattenObject[err_errObject, _]       := err
flattenObject[other_$flattenOTHER, _] := other                 (* one identity of $flattenOTHER *)
flattenObject[other_,              _] := $flattenOTHER[other]  (* wrap $flattenOTHER *)

reCheckMetricStates[der_, {indexL_, freeL_, dummyL_, mStates_}, cOptL_] := {indexL, freeL, dummyL, metricDerState[#, der, cOptL]& /@ mStates}

    (* modification of metricState induced by a derivative *)
    metricDerState[{updn_, metric_, mSign_}, der_, cOptL_] := {updn, metric, mSign} /; dnupDerQ[der, metric, cOptL]  (* keep metricState *)
    metricDerState[{updn_, _,       _},      der_, _]      := {updn, Null,   0}

        dnupDerQ[{opName_, arg___}, metric_, cOptL_] :=  (* can dn/up by a metric? Is opName metric-compatible? *)
            With [ {opType = getType[opName], mKind = KindOf[metric], opKind = KindOf[opName, arg]},
                covariantNameQ[opName, metric, cOptL] && ( (opType === CD && kindMatchQ[opKind, mKind] && ValidIndexQ[arg, mKind])
                                                           || (opType === LD || opType === XD) )
            ]

(****************************** xSort *******************************)

xSort[expr_Plus, opts___] := xSort[#, opts]& /@ expr
xSort[expr_List, opts___] :=
    Block[{$TOCANONICAL = True},
        objectSort @ markNoIndex[flattenObject[#, FilterRules[{opts}, CovDs]]& /@ (xTensorTimes @@ expr)]  (* for xSorting 'List @@ term' *)
    ]
xSort[expr_,     opts___] :=
    Block[{$TOCANONICAL = True},
        objectSort @ markNoIndex[flattenObject[expr, FilterRules[{opts}, CovDs]]]  (* See flattenObject[Tscalar[expr], cOptL] for $TOCANONICAL *)
    ]

    markNoIndex[obj:xObject[_, _, {_, {}, {}, _}]] := xNoIndex[obj]  (* no free/dummy indices *)
    markNoIndex[obj_xObject]                       := obj
    markNoIndex[err_errObject]                     := err
    markNoIndex[$flattenOTHER[other_]]             := xNoIndex[other]
    markNoIndex[expr_xTensorTimes]                 := markNoIndex /@ expr
    markNoIndex[expr_]                             := (Message[Msg::warn, "markNoIndex:", "not properly processed,", expr, ""]; expr)

    (* sort and mark CommutingObjects *)
    objectSort[expr_xObject]        := expr
    objectSort[expr_xNoIndex]       := expr
    objectSort[err_errObject]       := err
    objectSort[other_$flattenOTHER] := other
    objectSort[expr_xTensorTimes]   :=
        Block[{$freesForSorting = freeIndicesOf[expr]},
            breakCommObj /@ Split[Sort[expr, (objectOrder[#1, #2] >= 0)&], (objectOrder[#1, #2] == 0)&]
        ]
    objectSort[expr_] := (Message[Msg::warn, "objectSort:", "not properly processed,", expr, ""]; expr)

        breakCommObj[xTensorTimes[x_]]  := x
        breakCommObj[xTensorTimes[x__]] := xCommutingObjects[x]

        freeIndicesOf[xObject[_, _, {_, frees_, _, _}]] := frees
        freeIndicesOf[xNoIndex[_]]                      := {}
        freeIndicesOf[errObject[_]]                     := {}
        freeIndicesOf[other_$flattenOTHER]              := {}
        freeIndicesOf[expr_xCommutingObjects]           := takeFrees[Join @@ List @@ (freeIndicesOf /@ expr)]
        freeIndicesOf[expr_xTensorTimes]                := takeFrees[Join @@ List @@ (freeIndicesOf /@ expr)]

        objectOrder[_xNoIndex,    _]            :=  1
        objectOrder[_,            _xNoIndex]    := -1
        objectOrder[obj1_xObject, obj2_xObject] := Order[objectOrderItems @ obj1, objectOrderItems @ obj2]

            (* Selected items for sorting *)
            objectOrderItems[xObject[obj_, nameL_, {tIdxL_, free_, dum_, ms_}]] :=
                With[ {frees = Intersection[free, $freesForSorting]},
                    {nameL, Length[ms], -Length[frees], mStateOrderItems /@ ms}
                ]

                mStateOrderItems[{dnup_, Null,    _}] := dnup    (* keep dn/up *)
                mStateOrderItems[{_,     metric_, _}] := metric  (* neglect dn/up *)

xUnSort[xObject[obj_, _, _]]    := obj
xUnSort[xNoIndex[obj_]]         := xUnSort[obj]
xUnSort[expr_xCommutingObjects] := Apply[Times, xUnSort /@ expr]
xUnSort[expr_xTensorTimes]      := Apply[Times, xUnSort /@ expr]
xUnSort[errObject[obj_]]        := obj
xUnSort[$flattenOTHER[other_]]  := other
xUnSort[other_]                 := other

metricStatesOf[xObject[_, _, {_, _, _, mStateL_}]] := mStateL
metricStatesOf[xNoIndex[_]]                        := {}
metricStatesOf[expr_xCommutingObjects]             := Flatten[metricStatesOf /@ (List @@ expr), 1]
metricStatesOf[expr_xTensorTimes]                  := Flatten[metricStatesOf /@ (List @@ expr), 1]

(*************************** xSymmetryOf ****************************)
(*
    xSymmetry[
        the number of slots,
        expr with all indices replaced by slot numbers,
        a list of rules xSlot[n] -> index,
        a Generating Set of expr
    ]
 *)

Format[xSlot[n_Integer]] := "\[FilledCircle]" <> ToString[n]

(* to keep the order of the (already sorted) tensors. *)
SetAttributes[xTTimes, Flat]
xTTimes[1, x__] := xTTimes[x]

(* generates a list of rules xSlot[i] -> index, assuming that there are already n slots *)
toSlotRules[n_Integer, indexL_List] := MapIndexed[Rule[xSlot @@ (n + #2), #1]&, indexL]

emptySymmetry[x_]            := xSymmetry[0,             x, {},                   GenSet[]]
emptySymmetry[x_, inds_List] := xSymmetry[Length @ inds, x, toSlotRules[0, inds], GenSet[]]

(* moves the points by 'd' *)
displaceSlots[GS_GenSet,                         d_Integer] := GS /. Cycles[{cycs__}] :> Cycles[{cycs} + d]
displaceSlots[xSymmetry[n_, expr_, slotL_, GS_], d_Integer] := xSymmetry[n + d, Sequence @@ ({expr, slotL} /. xSlot[x_] -> xSlot[x + d]), displaceSlots[GS, d]]
displaceSlots[expr_,                             d_Integer] := expr /. xSlot[x_] -> xSlot[x + d]

xSymmetryOf[tName_?IndexedOperandQ[indices___], ___] :=
    With[ {len = Length[{indices}]},
        xSymmetry[len, tName @@ (First /@ #), #, getGenSetOf[tName[indices]]]& @ toSlotRules[0, {indices}]
    ]
xSymmetryOf[opName_?IndexedOperatorQ[arg_, expr___], opts___] :=
    Switch [getType[opName],
        CD, cdTypeSymmetryOf[{opName[arg]}, expr, opts],
        LD, MapAt[opName[arg, #]&, xSymmetryOf[expr, opts], 2],
        XD, MapAt[opName, xSymmetryOf[arg, opts], 2],
        XP, MapAt[opName, emptySymmetry[{arg, expr}], 2]
    ]

    cdTypeSymmetryOf[{cds__}, opName_[ind_, expr_], opts___] := cdTypeSymmetryOf[Join[{opName[ind]}, {cds}], expr, opts] /; IndexedOperatorQ[opName] && getType[opName] === CD
    cdTypeSymmetryOf[{cds__}, expr_,                opts___] := AD[Append[xSymmetryOf[expr, opts], tmpCovD[cds]], opts]

        (* If there are no more derivatives, return the symmetry *)
        AD[xSymmetry[n_, expr_, rules_, GS_, tmpCovD[]], ___] := xSymmetry[n, expr, rules, GS]

        (* If the first covd cannot commute, remove it *)
        AD[xSymmetry[n_, expr_, rules_, GS_, tmpCovD[covd_[a_], y___]], opts___] :=
            AD[
                Append[
                    displaceSlots[xSymmetry[n, covd[xSlot[0], expr], Join[{xSlot[0] -> a}, rules], GS], 1],
                    tmpCovD[y]
                ],
                opts
            ] /; (covD =!= BD && DerivativeOperatorQ[covD])  \
                 || (covD === BD && !covariantNameQ[BD, a, FilterRules[{opts}, CovDs]] && UpIndexQ[a])  (* CD[la, T] or BD[ua, T] *)

        (* If the first and second derivatives are different, remove the first *)
        AD[xSymmetry[n_, expr_, rules_, GS_, tmpCovD[covd1_[a1_], covd2_[a2_], y___]], opts___] :=
            AD[
                Append[
                    displaceSlots[xSymmetry[n, covd1[xSlot[0], expr], Join[{xSlot[0] -> a1}, rules], GS], 1],
                    tmpCovD[covd2[a2], y]
                ],
                opts
            ] /; covd1 =!= covd2

        (* Two equal covariant derivatives of a scalar commute if the derivative is torsion-free. *)
        AD[xSymmetry[n_, expr_, rules_, GS_, tmpCovD[covd_[a1_], covd_[a2_], y___]], opts___] :=
            Module[{xSym},
                xSym = displaceSlots[xSymmetry[n, covd[xSlot[-1], covd[xSlot[0], expr]], Join[{xSlot[-1] -> a2, xSlot[0] -> a1}, rules], GS], 2];
                AD[
                    Append[
                        ReplacePart[xSym, 4 -> Join[GenSet[{Cycles[{{1,2}}],+1}], xSym[[4]]]],
                        tmpCovD[y]
                    ],
                    opts
                ]
            ] /; DerivativeOperatorQ[covd] && TorsionFreeQ[covd] && AllTrue[{a1, a2}, TensorialIndexQ]  \
                 && NoIndexQ[expr /. rules] && ValidIndexQ[{a1, a2}, KindOf[covd]]                      \
                 && ( (DnIndexQ[a1] && DnIndexQ[a2]) || covariantNameQ[covd, a1, FilterRules[{opts}, CovDs]] );

        (* Other derivatives with the torsion are not commuted, even if they do commute; this is left to the user *)
        AD[xSymmetry[n_, expr_, rules_, GS_, tmpCovD[covd_[a_], y___]], opts___] :=
            AD[
                Append[
                    displaceSlots[xSymmetry[n, covd[xSlot[0], expr], Prepend[rules, xSlot[0] -> a], GS], 1],
                    tmpCovD[y]
                ],
                opts
            ] /; DerivativeOperatorQ[covd] && !TorsionFreeQ[covd]

        (* Drivers for the three remaining cases *)
        AD[xSymmetry[n_, expr_, rules_, GS_, tmpCovD[y:covd_[_].., covd1_[a_], z___]], opts___] :=
            ADSym[xSymmetry[n, expr, rules, GS, tmpCovD[y], tmpCovD[covd1[a], z]], opts] /; covd =!= covd1
        AD[xSymmetry[n_, expr_, rules_, GS_, tmpCovD[y:covd_[_].., covd_[a_],  z___]], opts___] :=
            ADSym[xSymmetry[n, expr, rules, GS, tmpCovD[y], tmpCovD[covd[a], z]], opts] /; !covariantNameQ[covd, a, FilterRules[{opts}, CovDs]] && UpIndexQ[a]
        AD[xSymmetry[n_, expr_, rules_, GS_, tmpCovD[y:covd_[_]..]], opts___]                   := ADSym[xSymmetry[n, expr, rules, GS, tmpCovD[y], tmpCovD[]], opts]

            (* If there are several BD derivatives that can commute, give GS *)
            ADSym[xSymmetry[n_, expr_, rules_, GS_, tmpCovD[y__], tmpCovD[z___]], opts___] :=
                Module[{opName, inds, newSym, newGS, slotRules, modSlotRules, sortedL},
                    opName = Head[First @ {y}];
                    inds = Apply[Identity, {y}, {1}];
                    slotRules = toSlotRules[0, Reverse @ inds];

                    (* shift slots in the operand *)
                    newSym = displaceSlots[xSymmetry[n, expr, rules, GS], Length @ {y}];
                    newGS = newSym[[4]];

                    (* BD[..., la, lB, lc, ..., T] *)
                    modSlotRules = slotRules;
                    If [!covariantNameQ[opName, First @ inds, FilterRules[{opts}, CovDs]], modSlotRules = Select[modSlotRules, DnIndexQ[#[[2]]]&]];
                    If [Length[modSlotRules] >= 2 && opName === BD,
                        sortedL = SplitBy[modSlotRules, (indexKindProper @ #[[2]])&];  (* CoordinateBasisQ[kind] *)

                        With [ {slots = First /@ First /@ #},
                            If [Length[slots] >= 2 && CoordinateBasisQ[indexKindProper[#[[1,2]]]], newGS = Join[symmetricGS[slots], newGS]]
                        ]& /@ sortedL
                    ];

                    AD[
                        xSymmetry[
                            n + Length[inds],
                            Last @ FoldList[opName[#2,#1]&, newSym[[2]], Reverse[xSlot /@ (First /@ First /@ slotRules)]],
                            Join[slotRules, newSym[[3]]],
                            newGS,
                            tmpCovD[z]
                        ],
                        opts
                    ]
                ]

                symmetricGS[inds_] := GenSet @@ ({Cycles[{#}],+1}& /@ Partition[Sort @ inds, 2, 1])

xSymmetryOf[x:_?ScalarFunctionQ[___],      ___]     := emptySymmetry[x]
xSymmetryOf[err_errObject,                 ___]     := emptySymmetry[err]
xSymmetryOf[other_$flattenOTHER,           ___]     := emptySymmetry[other]
xSymmetryOf[xObject[obj_, _, _],           opts___] := xSymmetryOf[obj, opts]
xSymmetryOf[expr_xTensorTimes,             opts___] := Fold[joinSymmetries, emptySymmetry[1], xSymmetryOf[#, opts]& /@ expr]
xSymmetryOf[xNoIndex[obj_],                ___]     := emptySymmetry[obj]
xSymmetryOf[xNoIndex[xObject[obj_, _, _]], ___]     := emptySymmetry[obj]
xSymmetryOf[xCommutingObjects[obj__],      opts___] :=
    Module[{sym, nsTotal, nObj = Length @ {obj}, GS},
        (* Construct xSymmetry object apart from generating set *)
        sym = Fold[joinSymmetries, emptySymmetry[1], xSymmetryOf[#, opts]& /@ xTensorTimes[obj]];

        (* Number of slots in the expression *)
        nsTotal = Length @ sym[[3]];

        (* combine both the symmetries of the objects themselves with the symmetries obtained by commutation. *)
        GS = Join[Last @ sym, commutingCycles[nsTotal, nsTotal / nObj]];

        (* New Symmetry object *)
        ReplacePart[sym, 4 -> GS]
    ]
xSymmetryOf[term_, opts___] := xSymmetryOf[xSort[term, opts], opts]

    (* We need to combine both the symmetries of the objects themselves and the symmetries obtained by commutation.
       There are nsTotal indices, with tensors having ns indices (hence ns must be a divisor of nsTotal) *)
    commutingCycles[ns_Integer,      ns_Integer] := GenSet[]
    commutingCycles[nsTotal_Integer, ns_Integer] :=
        Join[
            commutingCycles[nsTotal - ns, ns],
            GenSet[{Cycles @ Transpose[{Range[nsTotal - 2 ns + 1, nsTotal - ns], Range[nsTotal - ns + 1, nsTotal]}],+1}]
        ]

    (* joins two xSymmetry objects.
       Note that slots of the first Symmetry are kept and slots of the second are shifted n1 places.
       The resulting second argument of xSymmetry has head xTTimes. *)
    joinSymmetries[xSymmetry[n1_, expr1_, rules1_, GS1_], xSymmetry[n2_, expr2_, rules2_, GS2_]] :=
        xSymmetry[
            n1 + n2,
            xTTimes[expr1, displaceSlots[expr2, n1]],
            Join[rules1,   displaceSlots[rules2, n1]],
            Join[GS1,      displaceSlots[GS2, n1]]
        ]

(*************************** ToCanonical ****************************)

(* ToCanonical[expr] gives a canonical reorganization of the indices of expr
   according to the symmetries of tensors and positions of dummies and repeated indices. *)
Options[ToCanonical] = {Verbose -> False}

(* 1. ToCanonical on atoms: Identity *)
ToCanonical[x:(_Symbol | _String | _Integer | _Rational | _Real | _Complex), ___] := x

(* 2. ToCanonical is threaded over lists and Plus exprs. Do not share dummies first *)
ToCanonical[lst_List,  opts___] := ToCanonical[#, opts]& /@ lst
ToCanonical[expr_Plus, opts___] := ToCanonical[#, opts]& /@ expr

(* 3. ToCanonical on rules *)
ToCanonical[expr_Rule,        ___] := expr
ToCanonical[expr_RuleDelayed, ___] := expr

(* 4. No Special simple cases: need to check in flattenObject *)

(* 5. ToCanonical on unsorted expressions: apply xSort and toCanonicalObject.
   xSort (via flattenObject) returns expressions with head xObject, xTensorTimes, xNoIndex, xCommutingObjects, and errObject.
   We must give definitions for all possible cases: *)
ToCanonical[term_, opts___] := (
        With[ {cOptL = FilterRules[{opts}, CovDs]},  (* check covariant-derivative option *)
            If [cOptL =!= {} && !AllTrue[CovDs /. cOptL, IndexedOperatorQ],
                Message[Msg::err, "not defined operator(s)", CovDs /. cOptL, "", ""]; Return[term]
            ]
        ];

        With[ {rcExpr = Dum[term, opts]},
            If [Head[rcExpr] === Plus,
                ToCanonical[rcExpr, opts],
            (* else *)
                Module[ {ordTerm, oTerm},
                    {ordTerm, oTerm} = splitTerm[rcExpr, FilterRules[{opts}, HeadQs]];
                    If [oTerm === 1, Return[ordTerm]];

                    (* check indices *)
                    If [duplicatedIndicesQ[indicesOf[oTerm, {HeadQs -> {IndexedObjectQ}}]], Return[ordTerm * ErrorT[oTerm]]];

                    ordTerm * toCanonicalObject[xSort[oTerm, opts], opts]
                ]
            ]
        ]
    )
ToCanonical[___] := Message[ToCanonical::usage]

(* for sums: *)
toCanonicalObject[expr_Plus,       opts___] := toCanonicalObject[#, opts]& /@ expr
toCanonicalObject[x_Integer expr_, opts___] := x * toCanonicalObject[expr, opts]
toCanonicalObject[0,               ___]     := 0

(* for products with scalars: *)
(* Recursively canonicalize separately the xNoIndex expressions *)
toCanonicalObject[xTensorTimes[],                             ___]     := 1
toCanonicalObject[xTensorTimes[pre___, s1_xNoIndex, post___], opts___] := toCanonicalObject[s1, opts] * toCanonicalObject[xTensorTimes[pre, post], opts]

(* for scalars without indices *)
toCanonicalObject[xNoIndex[xObject[obj_, _, {_, _, _, {}}]], ___] := obj
toCanonicalObject[xNoIndex[obj_],                            ___] := obj

(* for errObject and $flattenOTHER *)
toCanonicalObject[errObject[err_],                                      ___] := err  (* ErrorT[_][___] *)
toCanonicalObject[$flattenOTHER[other_],                                ___] := other
toCanonicalObject[xTensorTimes[pre___, errObject[err_],       post___], opts___] := err   * toCanonicalObject[xTensorTimes[pre, post], opts]
toCanonicalObject[xTensorTimes[pre___, $flattenOTHER[other_], post___], opts___] := other * toCanonicalObject[xTensorTimes[pre, post], opts]

toCanonicalObject[expr_xObject,      opts___] := toCanonicalObject[xTensorTimes[expr], opts]
toCanonicalObject[expr_xTensorTimes, opts___] := (* We assume here that the 'expr' has been syntax-checked. *)
    Module[{sym = xSymmetryOf[expr, opts], verb, indices, dummies, mStateL, dumSets, newIndices},
        verb = Verbose /. {opts} /. Options[ToCanonical];
        If [verb,
            Print["***********************************************************"];
            Print["ToCanonical:: expr: ", expr];
            Print["ToCanonical:: sym: ", sym]
        ];

        (* 0. Indices. Use sym (but not expr) to ensure the right ordering of indices *)
        indices = List @@ (Last /@ sym[[3]]);
        If [verb, Print["ToCanonical:: indices: ", indices]];
        dummies = Sort[xDummyIndices[expr]];

        (* 1. Group theory *)
(***** Customizing xTensor 1.1.1 *****)
        (* Separate dummies according to the existing kinds and metric states *)
        If [verb, Print["ToCanonicalOne:: dummies: ", dummies]];

        (* metric states of indices *)
        mStateL = metricStatesOf[expr];
        If [verb, Print["ToCanonicalOne:: metric states: ", mStateL]];

        dumSets = Select[makeDummySet[Select[dummies, KindIndexQ[#]], #, indices, mStateL]& /@ definedKindList, (# =!= {})&];
        dumSets = Flatten[dumSets, 1];
(***********************************)
        If [verb, Print["ToCanonicalOne:: dummySets_1: ", dumSets]];

        newIndices = toCanonicalOne[indices, dumSets, sym[[4]], opts];
        If [verb, Print["ToCanonical:: newIndices: ", newIndices]];

        (* 2. Compute result from newIndices *)
        Which[
            newIndices === {0, indices}, 0,
            newIndices === {1, indices}, xUnSort[expr],
            True,                        reconstruct[sym, newIndices]
        ]
    ]
toCanonicalObject[expr_, ___] := (Message[Msg::warn, "toCanonicalObject:", "not properly processed,", expr, ""]; expr)

    (* construct a DummySet: Customizing xTensor 1.1.1 *)
    makeDummySet[{},      _,      _,      _]       := {}
    makeDummySet[_,       _,      _,      {}]      := Message[Msg::err, "makeDummySet[]: not properly processed,", "", "", ""]
    makeDummySet[dummyL_, kind_, indexL_, mStateL_] :=
        Module[ {dSet, zeroL},
            (* construct a DummySet *)
            dSet = DummySet[
                kind,
                dummyL,
                If [MetricSpaceQ[kind], metricSymmetry[kind],
                (* else *)              0]
            ];

            (* construct dummies having moveFlag === False *)
            zeroL = Pick[dummyL, moveQpair[dummyL, indexL, mStateL], False];

            (* adjust the metric state of dummy sets to fix xTensor 1.1.1 *)
            If [zeroL === {},
                {dSet},
            (* else *)
                If [zeroL === dummyL, {DummySet[dSet[[1]], zeroL, 0]},
                (* else *)            {DummySet[dSet[[1]], zeroL, 0], DummySet[dSet[[1]], Complement[dummyL, zeroL], dSet[[3]]]}]
            ]
        ]

        moveQpair[upDummyL_, aIndexL_, mStateL_] :=
            With[ {posL = {Position[aIndexL, FlipIndex @ #], Position[aIndexL, #]}& /@ upDummyL}, (* find (dn,up)-positions of dummies in the actual configuration *)
                (* get move-flags for dummies using the informations obtained by metricStatesOf *)
                moveFlag[First @ Extract[mStateL, #[[1]]], First @ Extract[mStateL, #[[2]]]]& /@ posL
            ]

            moveFlag[{_, Null, _}, _]            := False   (* no metric *)
            moveFlag[_,            {_, Null, _}] := False
            moveFlag[{_, _,    0}, _]            := False   (* don't move *)
            moveFlag[_,            {_, _,    0}] := False
            moveFlag[{_, _,    _}, {_, _,    _}] := True    (* otherwise: can move, e.g., pd_a T_p^p or B^p cd_a A_p *)

    xDummyIndices[x_] := First @ xDummyIndices1[x];

        xDummyIndices1[xObject[_, _, {_, frees_, dummies_, _}]] := {dummies, frees}
        xDummyIndices1[xNoIndex[_]]                             := {{}, {}}
        xDummyIndices1[expr_xCommutingObjects]                  := xJoinDummies @ Transpose[xDummyIndices1 /@ (List @@ expr)]
        xDummyIndices1[expr_xTensorTimes]                       := xJoinDummies @ Transpose[xDummyIndices1 /@ (List @@ expr)]

            xJoinDummies[{dummies_, frees_}] := {Union[ToUpIndex /@ Join[Join @@ dummies, takePairs[Join @@ frees]]], Join @@ frees}
            xJoinDummies[{}]                 := {{}, {}}

    reconstruct[xSymmetry[n_, smt_, slotRules_, _], {sign_, perm_List}] :=
        sign smt /. Inner[Rule, xSlot /@ List @@ Range[n], perm, List] /. {xTTimes -> Times, xNoIndex -> Times}

(* canonicalization of a set of indices *)
toCanonicalOne[indices_List, dumSets_List, syms_, opts___] :=
    Module[{verb, contL, sortedIdxs, repes, perm, dSets = dumSets, order = Length[indices], frees},
        verb = Verbose /. {opts} /. Options[ToCanonical];

        (* Actual configuration *)
        If [verb, Print["ToCanonicalOne:: Actual configuration: ", indices]];

(***** Customizing xTensor 1.1.3 (2019.01.24) *****)
        (* Fixing a bug in mTensor:
                A[ua, lb] BD[lc, CD[la, ub, f[]]] => -A[la, ub] BD[lc, CD[ua, lb, f[]]]
           In xTensor, using ToCanonical on the expr with metric-incompatible derivatives is DANGEROUS!
                A[ua, lb] BD[lc, CD[la, ub, f[]]]      => 0    <-- BUG
                A[ua, lb] BD[lc, CD[la, ub, S[ld,le]]] => ...  <-- "Detected metric-incompatible derivatives {PD}"
        *)
        contL = Flatten[#[[2]]& /@ Select[dumSets, (#[[3]] == 0)&]];  (* contracted indices with metricQ = 0 *)
        If [verb, Print["ToCanonicalOne:: non-moveQ contracted indices: ", contL]];

        (* Standard configuration *)
        sortedIdxs = sortIndicesProper[indices, Flatten[{FlipIndex[#], #}& /@ contL]];
(**************************************************)
        If [verb, Print["ToCanonicalOne:: Standard configuration: ", sortedIdxs]];

        (* Look for repeated component indices *)
        repes = Union @ Select[indices, ComponentIndexQ];
        repes = List @@ Map[RepeatedSet, Flatten[indexPosition[sortedIdxs, #]]& /@ repes];
        If [verb, Print["ToCanonicalOne:: Repeated indices: ", repes]];

        (* Permutation to be canonicalized *)
        perm = PermFromTo[sortedIdxs, indices];
        If [verb, Print["ToCanonicalOne:: Permutation to be canonicalized: ", perm]];

        (* Positions of dummies. *)
        dSets = dSets /. DummySet[kind_, dums_, metricQ_] :> DummySet[kind,
                                                                      {
                                                                         indexPosition[sortedIdxs, #][[1, 1]],
                                                                         indexPosition[sortedIdxs, FlipIndex @ #][[1, 1]]
                                                                      }& /@ dums,
                                                                      metricQ];
        If [verb, Print["ToCanonicalOne:: dummySets_2: ", dSets]];

        (* Positions of free (here all non-dummies or non-repeated) indices *)
        frees = Complement[Range[order], posits[dSets], posits[repes]];
        If [verb, Print["ToCanonicalOne:: Free indices: ", frees]];

        (* !!!!!!!!!!!!!!!! Invert to meet Renato's notation !!!!!!!!!!!!!!!! *)
        perm = InversePerm[perm];

        (* Canonicalization *)
        If [verb,
            Print["ToCanonicalOne:: calling: ", "CanonicalPerm[", perm, ",", order, ",", syms, ",", frees, ",", Join[dSets, repes], ",", {opts}, "]"]
        ];

        perm = CanonicalPerm[perm, order, syms, frees, Join[dSets, repes], opts];
        If [verb, Print["ToCanonicalOne:: Canonical permutation: ", perm]];

        (* !!!!!!!!!!!!!!!! Invert back to our notation !!!!!!!!!!!!!!!! *)
        perm = If [perm === 0, 0, InversePerm[perm]];

        (* Final indices: {sign, indexlist} *)
        If [perm === 0, {0, indices},
        (* else *)      {perm[[2]], PermuteList[sortedIdxs, perm]}]
    ]

    indexPosition[lst_, index_] := Position[lst, Verbatim[index], {1}]

    posits[lst_List]                   := Apply[Join, posits /@ lst]
    posits[DummySet[_, {pairs___}, _]] := Join[pairs]
    posits[RepeatedSet[lst_]]          := lst

    (* sort indices with ignoring non-moveQ contracted indices *)
    sortIndicesProper[indexL_, contL_] :=
        Module[ {sortedL = IndexSort @ Select[indexL, !MemberQ[contL, #]&], posL},
            posL = Flatten @ Position[If [MemberQ[contL, #], #, $FREE[#]]& /@ indexL, _$FREE];  (* positions of free (or moveQ-contracted) indices *)
            ReplacePart[indexL, Thread @ Rule[posL, sortedL]]
        ]

(********************************************************************)

End[ ] (* end the private context *)

EndPackage[ ]  (* end the package context *)
