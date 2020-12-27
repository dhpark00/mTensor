(* :Title: Tsimplify.m *)
(* :Context: mTensor` *)
(* :Author: Dal-Ho Park *)
(* :Summary: Simplification of Indexed Expressions *)
(* :Package Version: 2020.12 *)
(* :Mathematica Version: 10.4 *)

BeginPackage["mTensor`", {"mTensor`xPermML`"}]
(********************************************************************)

Begin["`Private`"]

(************************ DnUpPair/UpDnPair *************************)

(* pairs to dn-up/up-dn if possible *)
SetAttributes[DnUpPair, HoldAll]
DnUpPair[expr_Plus, args___]     := DnUpPair[#, args]& /@ expr
DnUpPair[expr_,     opts___Rule] := pairDrv[DnUpPair, expr, opts]
DnUpPair[___]                    := Message[DnUpPair::usage]

SetAttributes[UpDnPair, HoldAll]
UpDnPair[expr_Plus, args___]     := UpDnPair[#, args]& /@ expr
UpDnPair[expr_,     opts___Rule] := pairDrv[UpDnPair, expr, opts]
UpDnPair[___]                    := Message[UpDnPair::usage]

    pairDrv[cmd_, expr_, opts___Rule] :=
        With[ {cOptL = FilterRules[{opts}, CovDs]},
            (* check covariant-derivative option *)
            If [cOptL =!= {} && !AllTrue[CovDs /. cOptL, IndexedOperatorQ],
                Message[Msg::err, "not defined operator(s)", CovDs /. cOptL, "", ""]; Return[expr]
            ];

            With[ {rcExpr = expandObject[expr, opts]},
                If [Head[rcExpr] === Plus,
                    cmd[rcExpr, opts],
                (* else *)
                    forEachTerm[rcExpr, dnupTerm, FilterRules[{opts}, HeadQs], cOptL, If[cmd === DnUpPair, True, False]]
                ]
            ]
        ]

        dnupTerm[term_, hOptL_List, cOptL_List, bDnUp_] :=
            Module[ {ordTerm, oTerm, rcL, cntMark, sign = 1},
                {ordTerm, oTerm} = splitTerm[term, hOptL];

                (* check indices: for markPairs *)
                If [duplicatedIndicesQ[indicesOf[oTerm, {HeadQs -> {IndexedObjectQ}}], True], Return[ordTerm * ErrorT[oTerm]]];

                oTerm = resetDummiesTerm[oTerm, {}, hOptL];  (* prepare for markPairs *)
                If [Head[oTerm] === Times, rcL = markPairs[List @@ oTerm, hOptL, cOptL],
                (* else *)                 rcL = markPairs[List @  oTerm, hOptL, cOptL]];

                (* count dn-up/up-dn pairs which will be up-dn/dn-up. *)
                cntMark = If [bDnUp, $upup, $dndn];
                sign = Times @@ (
                    If [MetricSpaceQ[#] && metricSymmetry[#] === -1,
                        (-1)^(Count[rcL /. {cntMark[_][#][a_] :> $forPairCNT[#][a]}, $forPairCNT[#][_], Infinity] / 2),
                    (* else *)
                        +1
                    ]& /@ definedKindList);

                (* dn-up/up-dn with the multiplication mSym^nUpDn/mSym^nDnUp *)
                If [bDnUp,
                    ordTerm * sign * (Times @@ rcL /. {$dndn[_][_][a_] :> a,            $upup[_][_][a_] :> FlipIndex[a], $dnup[_][_][a_] :> a, $updn[_][_][a_] :> a}),
                (* else *)
                    ordTerm * sign * (Times @@ rcL /. {$dndn[_][_][a_] :> FlipIndex[a], $upup[_][_][a_] :> a,            $dnup[_][_][a_] :> a, $updn[_][_][a_] :> a})
                ]
            ]

(* mark pairs of a reset-dummied term, if moveQ:
      if  moveQ and (dn,up) --> $dndn[uniqSym][kind][idx]
      if  moveQ and (up,dn) --> $upup[uniqSym][kind][idx]
      if !moveQ and (dn,up) --> $dnup[uniqSym][kind][idx]
      if !moveQ and (up,dn) --> $updn[uniqSym][kind][idx]
 *)
markPairs[tTermL_List, hOptL_List, cOptL_List] :=
    Module[ {pairL, ccOptL, rcL = tTermL, dnPos, upPos, kind, i, uniqSym, xx},
        (* contracted pairs in the format {dn, up} in tTerm *)
        pairL = TakePairs @ findIndices[Times @@ tTermL, Sequence @@ hOptL];
        If [pairL === {}, Return[rcL]];

        For [i = 1, i <= Length[pairL], i++,
            dnPos = First @ Position[tTermL, pairL[[i,1]]]; upPos = First @ Position[tTermL, pairL[[i,2]]];
            kind = indexKind @ pairL[[i,1]];
            If [!kindMatchQ[kind, KindOf[Level[tTermL, 1][[dnPos[[1]]]], pairL[[i,1]]]], Continue[]];

            (* cf: covariantNameQ *)
            ccOptL = {CovDs -> DeleteDuplicates @ Join[
                If [cOptL =!= {}, cOptL[[1,2]], {}],
                If [MetricSpaceQ[kind], getCovDs[GetMetric @ kind], {}]
            ]};

            uniqSym = Unique[xx];
            If [dnPos[[1]] === upPos[[1]],  (* BD[lp, BD[la, T[lb, up]] or T[lp, up] *)
                If [MetricSpaceQ[kind] && moveQobject[tTermL[[dnPos[[1]]]], {dnPos, upPos}, ccOptL],
                    If [OrderedQ[{dnPos, upPos}],  (* if dn-up pair *)
                        rcL = rcL /. {pairL[[i,1]] -> $dndn[uniqSym][kind][pairL[[i,1]]], pairL[[i,2]] -> $dndn[uniqSym][kind][pairL[[i,2]]]},
                    (* else *)
                        rcL = rcL /. {pairL[[i,1]] -> $upup[uniqSym][kind][pairL[[i,1]]], pairL[[i,2]] -> $upup[uniqSym][kind][pairL[[i,2]]]}
                    ],
                (* else *)
                    If [OrderedQ[{dnPos, upPos}],
                        rcL = rcL /. {pairL[[i,1]] -> $dnup[uniqSym][kind][pairL[[i,1]]], pairL[[i,2]] -> $dnup[uniqSym][kind][pairL[[i,2]]]},
                    (* else *)
                        rcL = rcL /. {pairL[[i,1]] -> $updn[uniqSym][kind][pairL[[i,1]]], pairL[[i,2]] -> $updn[uniqSym][kind][pairL[[i,2]]]}
                    ]
                ],
            (* else *)
                If [MetricSpaceQ[kind] && moveQterm[tTermL[[ dnPos[[1]] ]], dnPos, ccOptL]  \
                                       && moveQterm[tTermL[[ upPos[[1]] ]], upPos, ccOptL],
                    If [dnPos[[1]] < upPos[[1]],  (* if dn-up pair *)
                        rcL = rcL /. {pairL[[i,1]] -> $dndn[uniqSym][kind][pairL[[i,1]]], pairL[[i,2]] -> $dndn[uniqSym][kind][pairL[[i,2]]]},
                    (* else *)
                        rcL = rcL /. {pairL[[i,1]] -> $upup[uniqSym][kind][pairL[[i,1]]], pairL[[i,2]] -> $upup[uniqSym][kind][pairL[[i,2]]]}
                    ],
                (* else *)
                    If [dnPos[[1]] < upPos[[1]],  (* if dn-up pair *)
                        rcL = rcL /. {pairL[[i,1]] -> $dnup[uniqSym][kind][pairL[[i,1]]], pairL[[i,2]] -> $dnup[uniqSym][kind][pairL[[i,2]]]},
                    (* else *)
                        rcL = rcL /. {pairL[[i,1]] -> $updn[uniqSym][kind][pairL[[i,1]]], pairL[[i,2]] -> $updn[uniqSym][kind][pairL[[i,2]]]}
                    ]
                ]
            ]
        ];
        rcL
    ]

    (* for an object *)
    moveQobject[(tName_?IndexedOperandQ)[___],      {_,        _},     _List]       := True (* T[up,lp] *)
    moveQobject[(opName_?IndexedOperatorQ)[args__], {dnPos_, upPos_},  ccOptL_List] :=      (* CD[up, T[lp,lb] *)
        Module[ {dnLevel = Length[dnPos], upLevel = Length[upPos]},
            If [dnLevel === Depth[opName[args]] === upLevel, Return[True]];   (* CD[ua, T[lp, up] *)
            If [dnLevel < upLevel, {dnLevel, upLevel} = {upLevel, dnLevel}];  (* swap *)

            (* Find the number of CovD from upLevel - 1 to dnLevel - 2. Are they all in covOpL? *)
            Length[ Position[opName[args], Alternatives @@ (CovDs /. ccOptL), {upLevel - 1, dnLevel - 2}] ] === dnLevel - upLevel
        ]
    moveQobject[___] := False

    (* for a product of objects *)
    moveQterm[(tName_?IndexedOperandQ)[___],      _,    _List]       := True (* aT[lp,lb] * bT[up,lc] *)
    moveQterm[(opName_?IndexedOperatorQ)[args__], pos_, ccOptL_List] :=      (* CD[la, aT[lp,lc]] * bT[up,ud] *)
        Module[ {lev = Length[pos]},
            (* special treatment of BD index for dnupTermList in TsimplifyPatternMatching *)
            If [$BDSPECIALQ === True,
                With[{expr = Level[opName[args], {lev - 2}]},
                    If [Length[expr] === 1, If [Head[expr[[1]]] === BD, Return[False]],
                    (* else *)              If [Head[expr[[2]]] === BD, Return[False]]]
                ]
            ];

            If [lev === 2, Return[True]];

            (* Find the number of CovD from 1 to lev - 2. Are they all in covOpL? *)
            Length[ Position[opName[args], Alternatives @@ (CovDs /. ccOptL), {1, lev - 2}] ] === lev - 2
        ]
    moveQterm[___] := False

(********************** Simplification Rules ************************)

(* \pd_a g^{bc} -> -g^{bd} g^{ce} \pd_a g_{de} for a (anti)symmetric metric *)
BDinvgRule[]        := BDinvgRule[Metricg]
BDinvgRule[metric_] := {
        BD[a_, metric[b_, c_]] :>
            With[ {kind = KindOf @ metric},
                Module[{bDn, bUp, cDn, cUp},
                    {bDn, bUp} = DummyPair[kind];
                    {cDn, cUp} = DummyPair[kind];
                    -metric[b, bUp] * metric[c,cUp] * BD[a, metric[bDn,cDn]
                ]
            ]
        ] /; AllTrue[{b,c}, TensorialIndexQ] && AllTrue[{b,c}, UpIndexQ]
    } /; MetricQ[metric]

KdeltaSumRule[]      := KdeltaSumRule[DefaultKind]
KdeltaSumRule[kind_] := {  (* Kdelta[-1,+1] = metricSymmetry[kind] *)
        Kdelta[a_, b_] :> If [DnIndexQ[a], metricSymmetry[kind], +1] * GetDimension[kind] /; ValidIndexQ[a, kind] && PairIndexQ[a, b]
    }

EpsilonProductRule[]      := EpsilonProductRule[DefaultKind]
EpsilonProductRule[kind_] := {  (* TODO: antisymmetric metric? *)
        (* NB: s in Wald is the number of minus: s = (dim - sig)/2 *)
        GetEpsilon[kind][indices1__] GetEpsilon[kind][indices2__] :>
            (-1)^((GetDimension[kind] - GetSignature[kind])/2) * Length[{indices1}]! * antisymmetrizeKdeltaProduce[{indices1}, {indices2}, kind]  \
            /; ValidIndicesQ[Join[{indices1}, {indices2}], kind] && Length[{indices1}] === Length[{indices2}]
    }

    antisymmetrizeKdeltaProduce[indexL1_, indexL2_, kind_] :=
        Module[{saveKdeltaFlag = flagTable[KdeltaFlag], metric = GetMetric[kind], rc},
            flagTable[KdeltaFlag] = False;   (* Off absorbKdelta *)
            (* anti-symmetrize and then explicitly metric -> Kdelta when updn|dnup *)
            rc = AntisymmetrizeIndices[indexL1, Times @@ Thread[metric[indexL1, indexL2]]] /. metric[a_,b_] /; !upupdndnIndexQ[{a,b}] -> Kdelta[a,b];
            flagTable[KdeltaFlag] = saveKdeltaFlag;
            Absorb[rc, metric] /. KdeltaSumRule[]
        ]

(*************************** TindexSort *****************************)

Options[TindexSort] = {Verbose -> False}
TindexSort[lst_List, opts___Rule] := TindexSort[#, opts]& /@ lst
TindexSort[expr_,    opts___Rule] :=
    Module[{saveHoptL = Options[HeadQs], rc},
        Options[HeadQs] = {HeadQs  -> {ObjectQ}};  (* (A[-1,-1])^2 => 0 *)
        rc = With [{hOptL = FilterRules[{opts}, HeadQs]}, forEachObject[expr, hOptL, indexSortObject]];
        Options[HeadQs] = saveHoptL;
        rc
    ]
TindexSort[expr_,    ___]         := expr
TindexSort[___]                   := Message[TindexSort::usage]

    indexSortObject[obj_] :=
        Module [{sign, objL, xSym, indexL, minSymW},
            {sign, objL} = dnupTermList[{obj}, {}];  (* consider anti-sym metric: oName[ua,...,la] -> {mSym^npairs, oName[la,...,ua]} *)

            xSym = xSymmetryOf[xSort[First @ objL]] /. {Tscalar -> Identity};  (* NB: removed Tscalar marker *)
            indexL = #[[2]]& /@ xSym[[3]];
            If [vanishingObjectQ[xSym, xSym[[4]]] === True, Return[0]];

            minSymW = getMinSymW[xSym[[4]], indexL];
            sign * minSymW[[2]] * (xSym[[2]] /. toSlotRules[0, Permute[indexL, minSymW[[1]]]])
        ]

        getMinSymW[GS_, aIndexL_] :=
            Module[ {allSymL = MakePermGroup[GS], minPos},
                If [allSymL === {}, Return[{Cycles[{{}}], +1}]];

                tmpF[symL_, iL_] := {Permute[aIndexL, symL[[1]]], iL[[1]]};
                minPos = Sort[MapIndexed[tmpF, allSymL], IndexOrderedQ[#1[[1]], #2[[1]]]&] [[1,2]];
                {allSymL[[minPos, 1]], allSymL[[minPos,2]]}  (* {minSym, minW} *)
            ]

        vanishingObjectQ[xSym_, GS_] :=
            Module[ {indexL = #[[2]]& /@ xSym[[3]]},
                If [vanishingBDQ[flattenCDtype[xSym[[2]] /. xSym[[3]]], indexL, GS] === True, Return[True]];

                indexL = toDnIfPossible /@ indexL;  (* to dn non-component indices: F_a^a or F_{11} -> 0 but F_1^1 \neq 0 *)
                Module[ {pairL, idx, sym, len = Length[indexL], posL, i},
                    (* get paired or repeated indices *)
                    pairL = Select[Split @ Sort @ indexL, (Length[#] >= 2)&];

                    For [i = 1, i <= Length[pairL], i++,
                        idx = pairL[[i,1]];
                        If [Head[idx] === List,
                            (* paired indices: F[la,ua] or S[la,ua] *)
                            sym = {Cycles[{Flatten[Position[indexL, idx], 1]}], -idx[[1]]};

                            If [PermMemberQ[sym, len, GS], Return[True]],
                        (* else *)
                            (* repeated indices: R[-1,-2,-2,-2] --> {2,3,4} *)
                            posL = Flatten[Position[indexL, idx], 1];

                            (* {Cycles[{{2,3}}], -1}, {Cycles[{{2,4}}], -1}, {Cycles[{{3,4}}], -1} *)
                            sym = {#, -1}& /@ (Cycles[{#}]& /@ Select[Flatten[Outer[List, posL, posL], 1], (#[[1]] < #[[2]])&]);

                            If [Or @@ (PermMemberQ[#, len, GS]& /@ sym), Return[True]]
                        ]
                    ];
                    False
                ]
            ]
        vanishingObjectQ[___] := False

            (* return {sym of metric, dn-index} if possible *)
            toDnIfPossible[idx_?TensorialIndexQ] :=
                With[ {kind = indexKind[idx]},
                    If [MetricSpaceQ[kind],  (* ToDn is possible *)
                        With[ {mSym = metricSymmetry[kind]},
                            If [mSym =!= 0,      (* metric has a (anti)symmetry *)
                                If [DnIndexQ[idx],  Return[{mSym, idx}],
                                (* else *)          Return[{mSym, ToDnIndex[idx]}]]
                            ]
                        ]
                    ];
                    idx
                ]
            toDnIfPossible[idx_] := idx

        vanishingBDQ[flatT:{pre___, BD, a_, mid___, BD, b_, post___, T_, {___, c_, ___, d_, ___}}, indexL_, GS_] := (
                If [CoordinateBasisQ[indexKind @ a] && DnIndexQ[a] && DnIndexQ[b] && (PairIndexQ[{a,c}, {b,d}] || PairIndexQ[{a,d}, {b,c}]),
                    Module [{cPos = Position[indexL, c], dPos = Position[indexL, d]},
                        If [PermMemberQ[{Cycles[{Flatten @ {cPos, dPos}}], -1}, Length @ indexL, GS], Return[True]]
                    ]
                ];
                False
            )

        (* CD[a, BD[b, T[indices]]] -> {{CD, a}, {BD, b}, T, {indices}} *)
        flattenCDtype[oName_?IndexedOperandQ[args___]]         := {oName, {args}}
        flattenCDtype[opName_?IndexedOperatorQ[arg_, expr___]] :=
            Switch [getType[opName],
                CD, Join[{opName, arg}, flattenCDtype[expr]],
                LD, flattenCDtype[expr],
                XD, flattenCDtype[arg],
                XP, {}
            ]
        flattenCDtype[___] := {}

(* cf: dnupTerm[term, hOptL, cOptL, bDnUp] *)
dnupTermList[termL_, cOptL_List, toPatternQ_:False] :=
    Block[{$BDSPECIALQ = True},
        Module[ {rcL, sign},
            rcL = markPairs[termL, {}, cOptL];

            (* count up-dn pairs which will be dn-up. *)
            sign = Times @@ (
                If [MetricSpaceQ[#] && metricSymmetry[#] === -1,
                    (-1)^(Count[rcL /. {$upup[_][#][a_] :> $forPairCNT[#][a]}, $forPairCNT[#][_], Infinity] / 2),
                (* else *)
                    +1
                ]& /@ definedKindList);

            (* dn-up with the multiplication mSym^nUpDn, and clear markPairs symbols `$xxxx` *)
            If [toPatternQ === True,
                {sign, rcL /.{$dndn[s_][_][a_] :> Pattern[Evaluate[s], Blank[]],
                              $upup[s_][_][a_] :> Pattern[Evaluate[s], Blank[]],
                              $dnup[s_][_][a_] :> Pattern[Evaluate[s], Blank[$dnup]],
                              $updn[s_][_][a_] :> Pattern[Evaluate[s], Blank[$updn]]}},
            (* else *)
                {sign, rcL /. {$dndn[_][_][a_] :> a, $upup[_][_][a_] :> FlipIndex[a], $dnup[_][_][a_] :> a, $updn[_][_][a_] :> a}}
            ]
        ]
    ]

(**************************** Tsimplify *****************************)

Options[Tsimplify] = {Verbose -> False}
Tsimplify[lst_List, opts___Rule] := Tsimplify[#, opts]& /@ lst
Tsimplify[expr_,    opts___Rule] :=
    Module[ {verb, hOptL = FilterRules[{opts}, HeadQs], cOptL = FilterRules[{opts}, CovDs]},
        (* check covariant-derivative option *)
        If [cOptL =!= {} && !AllTrue[CovDs /. cOptL, IndexedOperatorQ],
            Message[Msg::err, "not defined operator(s)", CovDs /. cOptL, "", ""]; Return[expr]
        ];

        verb = Verbose /. {opts} /. Options[Tsimplify];
        If [verb,
            Print["***********************************************************"];
            Print["Tsimplify:: expr: ", expr]
        ];

        Block[ {$AssumSymL = {}}, tSimplifyAux[expr, hOptL, cOptL, verb] ]
    ]
Tsimplify[___] := Message[Tsimplify::usage]

    tSimplifyAux[expr_, hOptL_, cOptL_, verb_] :=
        With[ {rcExpr = forEachTerm[expandObject[expr], tReduceTerm, hOptL, cOptL, verb]},
            If [verb && expr =!= rcExpr, Print["After tReduceTerm, expr: ", rcExpr]];
            rcExpr
        ]

tReduceTerm[aTerm_, hOptL_List, cOptL_List, verb_] :=
    Module[{ordTerm, oTerm},
        {ordTerm, oTerm} = splitTerm[aTerm, hOptL];
        If [oTerm === 1, Return[ordTerm]];

        tReduceTermProcess[xSort[oTerm, Sequence @@ cOptL], ordTerm, oTerm, cOptL, verb]
    ]

(* for products with scalars: *)
tReduceTermProcess[xTensorTimes[],                             ordTerm_, ___]     := ordTerm
tReduceTermProcess[xTensorTimes[pre___, s1_xNoIndex, post___], ordTerm_, opts___] := tReduceTermProcess[s1, 1, opts]  \
                                                                                     * tReduceTermProcess[xTensorTimes[pre, post], ordTerm, opts]

(* for scalars without indices *)
tReduceTermProcess[xNoIndex[$flattenOTHER[other_]],           ordTerm_, ___] := ordTerm * other
tReduceTermProcess[xNoIndex[xObject[obj_, _, {_, _, _, {}}]], ordTerm_, ___] := ordTerm * obj

tReduceTermProcess[flatTerm_, ordTerm_, oTerm_, cOptL_List, verb_] :=
    Module[{mStateL, xSym, oTermL, indexL, markedTermL, name, sign, rc, sortedFreeL, i},
        mStateL = metricStatesOf[flatTerm];
        xSym = xSymmetryOf[flatTerm, Sequence @@ cOptL];  (* for sorting oTerm *)
        If [verb,
            Print["flatTerm: ", flatTerm];
            Print["xSym: ", xSym]
        ];

        oTermL = toList[xSym[[2]] /. xSym[[3]]];
        If [!FreeQ[xSym[[2]], _errObject], Return[ordTerm * Times @@ oTermL]];
        If [verb, Print["oTermL: ", oTermL]];

        (* only for symmetric metrics *)
        indexL = #[[2]]& /@ xSym[[3]];
        If [!AllTrue[Union[indexKind /@ ToDnIndex /@ (takePairs @ indexL)], (MetricSpaceQ[#] && metricSymmetry[#] === +1)&],
            Message[Msg::err, "There is non-symmetric metric when contracting indices.", "", "", ""]; Return[ordTerm * oTerm]
        ];

        (* reduce symmetries due to $dnup/$updn indices *)
        markedTermL = markPairs[oTermL, {}, cOptL];
        xSym = ReplacePart[xSym, 4 -> reduceSymByMark[xSym[[4]], markedTermL, indexL, cOptL]];
        If [verb, Print["After reducing symmetries, xSym[[4]]: ", xSym[[4]]]];

Off[Symbol::symname];  (* when flattenObject returns $flattenOTHER *)
        name = SymbolJoin[SymbolJoin[#[[2]]]& /@ ((flattenObject[#, cOptL]& /@ oTermL) /. $flattenOTHER[obj_] :> {1, obj})];
On[Symbol::symname];
        prepareSymbolicTensor[name, indexL, xSym[[4]]];
        If [verb,
            Print["After preparing SymbolicTensors"];
            Print["    Assumptions: ", TableForm @ $AssumSymL];
            Print["    indices: ", indexL]
        ];

        {sign, rc, sortedFreeL} = doTensorReduce[name, xSym, indexL, verb];
        If [rc === 0, Return[0]];
        If [sortedFreeL === Null, Return[ordTerm * oTerm]];  (* internal error *)

        (* interpret TensorContract *)
        {indexL, rc} = postTensorContract[rc, mStateL, indexL, sign, verb];

        (* interpret TensorTranspose *)
        sortedFreeL = postTensorTranspose[rc, sortedFreeL, sign, verb];
        If [sortedFreeL =!= {},
            For [i = 1, i <= Length[indexL], i++,
                If [indexL[[i]] === 0, indexL[[i]] = sortedFreeL[[1]]; sortedFreeL = Drop[sortedFreeL, 1]];
            ]
        ];

        sign * ordTerm * Times @@ (toList[xSym[[2]]] /. toSlotRules[0, indexL])
    ]

    (* If not $upup/$dndn, reduce permutation symmetries. E.g.
           A[la,lb] BD[lc,S[ua,ub]] === 0 because sym[A] = -{1,2} and sym[S] = +{1,2}
           A[la,ub] BD[lc,S[ua,lb]] =!= 0 because sym[A] =  {} and sym[S] = {}  <== $dnup,$updn and !upupdndn[{la,ub}] *)
    reduceSymByMark[GS_, markedTermL_, indexL_, cOptL_] :=
        Module[{markedIndexL, markedIndexLOperand, posL, gs = GS, cycL, i, j},
            markedIndexL        = Join @@ (allIndicesObject     /@ markedTermL);
            markedIndexLOperand = Join @@ (indicesOperandMarked /@ markedTermL);
            posL = Flatten @ (Position[markedIndexL, #]& /@ markedIndexLOperand);
            For [i = 1, i <= Length[posL], ++i,
                For [j = 1, j <= Length[gs], ++j,
                    cycL = gs[[j,1,1]];
                    (* if a sym includes markedIdx, and the indices in the sym is not upupdndn, drop the sym in GS *)
                    If [AnyTrue[cycL, MemberQ[#, posL[[i]]]&] && !upupdndnIndexQ[indexL[[ cycL[[ Position[cycL, posL[[i]]][[1,1]] ]] ]]],
                        gs = Drop[gs, {j}]; j--
                    ]
                ]
            ];
            gs
        ]

        (* get $updn/$dnup indices in operands *)
        indicesOperandMarked[oName_?IndexedOperandQ[indices__]]       := {indices}[[ Flatten[Position[{indices}, _$updn[_][_] | _$dnup[_][_]], 1] ]];
        indicesOperandMarked[opName_?IndexedOperatorQ[arg_, expr___]] :=
            Switch [getType[opName],
                CD, indicesOperandMarked[expr],
                LD, indicesOperandMarked[expr],
                XD, indicesOperandMarked[arg],  (* expr === Null *)
                XP, Flatten @ (indicesOperandMarked /@ {arg, expr})
            ]
        indicesOperandMarked[expr_] := {}

    prepareSymbolicTensor[name_, idxL_, GS_] :=  (* symmetries for TensorReduce *)
        With[ {kindL = indexKindProper /@ idxL},
            If [!MemberQ[#[[1]]& /@ $AssumSymL, name],
                AppendTo[$AssumSymL, Element[name, Arrays[kindL, List @@ GS]]]
            ]
        ]

    doTensorReduce[name_, xSym_, idxL_, verb_] :=
        Module[ {indexL = idxL, pairL, repeatL, uniqueL = {}, sortedIndexL, rc, contL = {}, sign, i, j},
            (* contracted tensorial indices *)
            pairL = TakePairs @ indexL;
            If [verb, Print["In doTensorReduce, contracted pairs: ", pairL]];

            (* repeated component indices *)
            repeatL = Union @ Select[indexL, ComponentIndexQ];
            repeatL = Select[Flatten /@ (Position[indexL, #]& /@ repeatL), (Length[#] =!= 1)&];
            If [verb && repeatL =!= {}, Print["positions of repeated indices: ", repeatL]];

            (* If repeated anti-sym indices *)
            If [repeatedIndicesZeroQ[xSym[[4]], xSym[[1]], repeatL], Return[{1, 0, indexL}]];

            (* repeated indices -> temporary unique indices *)
            For [i = 1, i <= Length[repeatL], i++,
                AppendTo[uniqueL, Unique["zz" <> ToString[#]]& /@ repeatL[[i]]];
                For [j = 1, j <= Length[repeatL[[i]]], j++,
                    indexL = ReplacePart[indexL, repeatL[[i,j]] -> $UNIQUE[ uniqueL[[i,j]][indexL[[ repeatL[[i,j]] ]]] ]]
                ]
            ];
            uniqueL = Cases[indexL, $UNIQUE[a_] -> a];
            indexL = indexL /. $UNIQUE -> Identity;
            If [verb && uniqueL =!= {}, Print["unique repeated indices: ", uniqueL]];

            (* sorted free-indices *)
            sortedIndexL = sortIndicesProper[indexL, Flatten @ pairL];
            If [verb,
                Print["In doTensorReduce, after sortIndicesProper"];
                Print["    original indices: ", indexL];
                Print["    sorted indices: ", sortedIndexL]
            ];

            (* prepare TensorTranspose *)
            rc = TensorTranspose[name, indexL /. MapIndexed[Rule[#1, First @ #2]&, sortedIndexL]];
            If [verb, Print["Pre-processing TensorTranspose: ", rc]];

            (* prepare TensorContract *)
            AppendTo[contL, Flatten @ {Position[indexL, #[[1]]], Position[indexL, #[[2]]]}]& /@ pairL;
            rc = TensorContract[rc, contL];
            If [verb, Print["Pre-processing TensorContract: ", rc]];

            (* perform TensorReduce *)
            If [verb, Print["Calling TensorReduce..."]];
            rc = TensorReduce[rc, Assumptions -> $AssumSymL];
            If [verb, Print["In doTensorReduce, after TensorReduce: ", rc]];
            If [rc === 0, Return[{1, 0, Null}]];

            (* pick up a sign *)
            sign = signTerm[rc]; rc = sign * rc;

            (* restore the repeated indices from the uniqueL *)
            sortedIndexL = dropPairs @ sortedIndexL;
            If [uniqueL =!= {},
                (sortedIndexL = sortedIndexL /. # -> #[[1]])& /@ uniqueL;
                If [verb, Print["After restoring the repeated indices, the sorted free-indices: ", sortedIndexL]]
            ];

            {sign, rc, sortedIndexL}
        ]

        repeatedIndicesZeroQ[GS_GenSet, len_Integer, repeatL_] :=
            With[ {sym = {Cycles[{#}], -1}& /@ Flatten[Partition[Sort @ #, 2, 1]& /@ repeatL, 1]},
                Or @@ (PermMemberQ[#, len, GS]& /@ sym)
            ]

    postTensorContract[rc_, mStateL_, indexL_, sign_, verb_] :=
        Module[ {idxL, nIndex = Length[indexL], pairL, contL, dumpairL, moveQ, i},
            idxL = ConstantArray[0, nIndex];
            pairL = takePairsProper[indexL];

            If [verb, Print["metric states: ", mStateL]];

            contL = Cases[{rc}, TensorContract[_, cts_]:> cts, Infinity];
            If [contL =!= {},
                For [i = 1, i <= Length[contL[[1]]], ++i,
                    dumpairL = DummyPair @ indexKind @ pairL[[i,1]];  (* fresh dummy pair *)
                    moveQ = AllTrue[(#[[3]]& /@ mStateL)[[ contL[[1,i]] ]], (# === +1)&];
                    (* If moveQ, {dn, up}        : A[la,ub] CD[lc, S[ua,lb]] => A[lp,lq] CD[lc, S[up,uq]].
                       Otherwise, original dn/up : A[la,ub] BD[lc, S[ua,lb]] => A[lp,uq] BD[lc, S[up,lq]] *)
                    idxL[[ contL[[1,i]] ]] = If [moveQ || DnIndexQ[pairL[[i,1]]], dumpairL, dumpairL[[{2,1}]]]
                ]
            ];
            If [verb,
                Print["In postTensorContract, idxL: ", idxL];
                If [contL =!= {}, Print["After postTensorContract: ", sign * rc /. TensorContract[arg_, _] :> arg]]
            ];

            {idxL, rc /. TensorContract[arg_, _] :> arg}
        ]

    postTensorTranspose[rc_, sortedIndexL_, sign_, verb_] :=
        Module[ {transL, sortedL = sortedIndexL},
            transL = Cases[{rc}, TensorTranspose[_, imag_]:> imag, Infinity];
            If [transL =!= {}, sortedL = PermuteList[sortedL, InversePerm @ (Imag @@ transL[[1]])]];

            If [verb,
                Print["In postTensorTranspose, free-indices: ", sortedL];
                If [transL =!= {}, Print["After postTensorTranspose: ", sign * rc /. TensorTranspose[arg_, _]:> arg]];
            ];

            sortedL
        ]

(* all indices for a 'xSorted' term *)
allIndicesObject[oName_?IndexedOperandQ[indices__]]       := {indices}
allIndicesObject[opName_?IndexedOperatorQ[arg_, expr___]] :=
    Switch [getType[opName],
        CD, Join[{arg}, allIndicesObject[expr]],
        LD, allIndicesObject[expr],
        XD, allIndicesObject[arg],  (* expr === Null *)
        XP, Flatten @ Map[allIndicesObject&, {arg, expr}]
    ]
allIndicesObject[expr_] := {}

toList[term_xTTimes] := List @@ term
toList[term_Times]   := List @@ term
toList[other_]       := List @  other

(********************* TsimplifyPatternMatching *********************)
(*
    Inefficient when the perm symmetry is large. E.g. RiemannR[....] RiemannR[....] RiemannR[....] takes 30sec!
*)
Options[TsimplifyPatternMatching] = {Verbose -> False}
TsimplifyPatternMatching[lst_List, opts___Rule] := TsimplifyPatternMatching[#, opts]& /@ lst
TsimplifyPatternMatching[expr_,    opts___Rule] :=
    Module[ {deltaQ = flagTable[KdeltaFlag], cOptL = FilterRules[{opts}, CovDs], verb, rc},
        Off[KdeltaFlag];  (* Off automatically absorbing Kdelta in TsimplifyPatternMatching *)

        (* check covariant-derivative option *)
        If [cOptL =!= {} && !AllTrue[CovDs /. cOptL, IndexedOperatorQ],
            Message[Msg::err, "not defined operator(s)", CovDs /. cOptL, "", ""]; Return[expr]
        ];

        verb = Verbose /. {opts} /. Options[TsimplifyPatternMatching];
        If [verb,
            Print["***********************************************************"];
            Print["TsimplifyPatternMatching:: expr: ", expr]
        ];

        rc = tSimplifyPatternMatching[ResetDummies[expr, opts], FilterRules[{opts}, HeadQs], cOptL, verb];

        If [deltaQ === True, On[KdeltaFlag]];  (* restore KdeltaFlag *)
        rc  (* use Absorb[expr, metric] to absorb metric[la, ua] *)
    ]
TsimplifyPatternMatching[expr_, ___] := expr

    tSimplifyPatternMatching[aPlus_Plus, hOptL_List, cOptL_List, verb_] :=
        Module[{plusL, nLen, rc, rcW, i, j,
                 ordTerm1, oTermL1, xSym1, idxL1, idxPairDnL1, allSymL1, ordTerm2, oTermL2, xSym2, idxL2, idxPairDnL2, allSymL2},
            plusL = List @@ aPlus;  (* for modifying aPlus *)

            (* For each term, split into ordTerm and oTerm, and then drop vanishing objects *)
            plusL = Map[simplifyTerm[#, hOptL, cOptL, verb]&, plusL];
            plusL = Select[plusL, (#[[1]] =!= 0)&];  (* plusL == { {ordTerm, oTermL}, ... } *)

            nLen = Length[plusL];
            Switch [nLen,
                0,  0,
                1,  plusL[[1,1]] * (Times @@ plusL[[1,2]]),
                _,
                    If [verb, Print["plusL: ", plusL]];

                    rc = 0;
                    For [i = 1, i <= nLen, i++,
                        (* compare i-th and j-th, where i < j. If i == nLen, do nothing *)
                        {ordTerm2, oTermL2, xSym2, idxL2, idxPairDnL2, allSymL2} = plusL[[i]];

                        If [i < nLen,
                            For [j = i + 1, j <= nLen, j++,
                                {ordTerm1, oTermL1, xSym1, idxL1, idxPairDnL1, allSymL1} = plusL[[j]];

                                If [verb,
                                    Print["termL1: ", oTermL1]; Print["termL2: ", oTermL2];
                                    Print["xSym2: ", xSym2]; Print["idxL2: ", idxL2]; Print["allSymL2: ", allSymL2]
                                ];

                                (* compare pair-downed oTerm with patTerm *)
                                rcW = matchTerm[oTermL1, idxPairDnL1, oTermL2, toList[xSym2[[2]]], idxL2, allSymL2, cOptL, verb];

                                If [rcW =!= 0,                                   (* if equal *)
                                    ordTerm2 += ordTerm1 * rcW;                  (* combine *)
                                    plusL = Drop[plusL, {j}]; j -= 1; nLen -= 1  (* update *)
                                ]
                            ]
                        ];
                        rc += Times @@ {ordTerm2, Times @@ oTermL2}
                    ];
                    rc
            ]
        ]
    tSimplifyPatternMatching[term_, hOptL_List, cOptL_List, verb_] :=  (* for non-Plus term *)
        With[ {rcExpr = expandObject[term]},
            If [Head[rcExpr] === Plus,
                tSimplifyPatternMatching[rcExpr, hOptL, cOptL, verb],
            (* else *)
                With[{rcL = simplifyTerm[rcExpr, hOptL, cOptL, verb]},
                    rcL[[1]] * (Times @@ rcL[[2]])
                ]
            ]
        ]
    tSimplifyPatternMatching[expr_, ___] := expr

        simplifyTerm[term_, hOptL_List, cOptL_List, verb_] :=
        (* split into ordTerm and oTerm, and then check if the objects vanish *)
            Module[ {ordTerm, oTerm, xSym, sign, oTermL, idxL, idxPairDnL, allSymL},
                {ordTerm, oTerm} = splitTerm[term, hOptL];
                If [oTerm === 1, Return[{ordTerm, {oTerm}}]];

                (* DnUpPair for symmetric/anti-symmetric contractions *)
                xSym = xSymmetryOf[xSort[oTerm, Sequence @@ cOptL], Sequence @@ cOptL];   (* for sorting oTerm *)
                {sign, oTermL} = dnupTermList[toList[xSym[[2]] /. xSym[[3]]], cOptL];
                ordTerm = sign*ordTerm;

                xSym = xSymmetryOf[xSort[oTermL, Sequence @@ cOptL], Sequence @@ cOptL];  (* re-calc xSym after the dnupTermList *)
                If [verb, Print["xSym: ", xSym]];

                oTermL = toList[xSym[[2]] /. xSym[[3]]];
                If [verb, Print["oTermL: ", oTermL]];

                idxL = Join @@ allIndicesObject /@ oTermL;
                idxPairDnL = Join @@ allIndicesObject /@ pairsToDn[oTermL, cOptL];
                If [verb, Print["idxL: ", idxL]; Print["idxPairDnL: ", idxPairDnL]];

                (* NB: crucial factor when (inefficiently) simplifying terms with large symmetries *)
                allSymL = DeleteCases[MakePermGroup[xSym[[4]]], {Cycles[{}],1}];

                If [verb,
                    If [Length[allSymL] > 100, Print["allSymL: len = ", Length[allSymL]],
                    (* else *)                 Print["allSymL: len = ", Length[allSymL], ", ", allSymL]]
                ];

                If [vanishingQ[toList[xSym[[2]]], idxL, idxPairDnL, allSymL, cOptL, verb],
                    Return[{0, oTermL}],
                (* else *)
                    Return[{ordTerm, oTermL, xSym, idxL, idxPairDnL, allSymL}]
                ]
            ]

            vanishingQ[xSymPart2L_, idxL_, idxPairDnL_, allSymL_, cOptL_, verb_] :=
                Module[{sign, termL, patL, i},
                    For [i = 1, i <= Length[allSymL], ++i,
                        (* apply the perm symmetry, and then DnUpPair again *)
                        {sign, termL} = dnupAndPairsToPattern[xSymPart2L /. toSlotRules[0, Permute[idxL, allSymL[[i,1]]]], cOptL];

                        patL = Join @@ allIndicesObject /@ termL;
                        If [MatchQ[idxPairDnL, patL] && sign*allSymL[[i,2]] === -1,
                            If [verb, Print["Matched! sym = ", allSymL[[i]]]];
                            Return[True]
                        ]
                    ];
                    False
                ]

        (* match two terms. return 0 for different terms, +1/-1 for matching terms *)
        matchTerm[termL1_, _,            termL1_, _,            _,      _,         _,      _]     := +1
        matchTerm[termL1_, idxPairDnL1_, termL2_, xSym2Part2L_, idxL2_, allSymL2_, cOptL_, verb_] :=
            Module[{name1, name2, patL2, sign, termL, i},
                name1 = nameTerm[termL1]; name2 = nameTerm[termL2];
                If [verb, Print["name1: ", name1]; Print["name2: ", name2]];
                If [name1 =!= name2, Return[0]];  (* if different opNames + oNames + free-indices *)

                patL2 = Join @@ allIndicesObject /@ pairsToPattern[termL2, cOptL];
                If [verb, Print["patL2: ", patL2]];

                If [MatchQ[idxPairDnL1, patL2],
                    Return[1],
                (* else *)
                    For [i = 1, i <= Length[allSymL2], ++i,
                        (* apply the perm symmetry, and then DnUpPair again *)
                        {sign, termL} = dnupAndPairsToPattern[xSym2Part2L /. toSlotRules[0, Permute[idxL2, allSymL2[[i,1]]]], cOptL];

                        patL2 = Join @@ allIndicesObject /@ termL;
                        If [MatchQ[idxPairDnL1, patL2],
                            If [verb, Print["Matched! sym = ", allSymL2[[i]]]];
                            Return[sign * allSymL2[[i,2]]]
                        ]
                    ];
                    Return[0]
                ]
            ]

            (* return {{op+obj}, free-indices} from a term *)
            nameTerm[tTermL_List] := {Sort[Map[nameObject, tTermL]], Sort[findFreeIndices[Times @@ tTermL]]}

                nameObject[oName_?IndexedObjectQ[args___]] := flattenObject[oName[args], {}][[2]]
                nameObject[other_]                         := {other}

        (* dnupTermList and then pairsToPattern *)
        dnupAndPairsToPattern[termL_, cOptL_List] := dnupTermList[termL, cOptL, True]

        (* dummy pairs to down indices in a tensor product: T[la,ua] -> T[la, la] *)
        pairsToDn[tTermL_List, cOptL_List] :=
            Block[{$BDSPECIALQ = True},
                markPairs[tTermL, {}, cOptL] /. {$dndn[_][_][a_] :> $dndn[ToDnIndex[a]],  (* wrap $dndn to prevent automatic conversion of g^{ab} --> Kdelta^a_b *)
                                                 $upup[_][_][a_] :> $dndn[ToDnIndex[a]],
                                                 $dnup[_][_][a_] :> $dnup[ToDnIndex[a]],
                                                 $updn[_][_][a_] :> $updn[ToDnIndex[a]]}
            ]

        (* dummy-pairs to pattern variables in a tensor product: T[la,ua] -> T[la_, la_] *)
        pairsToPattern[tTermL_, cOptL_List] :=
            Block[{$BDSPECIALQ = True},
                markPairs[tTermL, {}, cOptL] /. {$dndn[s_][_][a_] :> Pattern[Evaluate[s], Blank[]],
                                                 $upup[s_][_][a_] :> Pattern[Evaluate[s], Blank[]],
                                                 $dnup[s_][_][a_] :> Pattern[Evaluate[s], Blank[$dnup]],
                                                 $updn[s_][_][a_] :> Pattern[Evaluate[s], Blank[$updn]]}
            ]

(********************************************************************)

End[ ] (* end the private context *)

EndPackage[ ]  (* end the package context *)
