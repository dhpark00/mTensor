(* :Author: Dal-Ho Park *)
(* :Summary: IndexNotation for manipulating indexed objects in Mathematica *)
(* :Package Version: 2020.12 *)
(* :Mathematica Version: 10.4 *)

(********************************************************************)
BeginPackage["mTensor`", {"mTensor`xPermML`"}]

(********************************************************************)
Begin["`Private`"]

If [System`$VersionNumber < 10.4, Throw @ Message[General::err, "Version >= 10.4 is required!"]]

(*************************** 0. Utilities ***************************)

FreePatternQ[expr_] := FreeQ[expr, xSlot|Slot|Pattern|PatternSequence|Blank|BlankSequence|BlankNullSequence|Condition|PatternTest|Repeated|RepeatedNull]

PositiveIntegerQ[n_Integer] := Positive[n]
PositiveIntegerQ[___]       := False

SymbolJoin[symbL_List] := Symbol @ StringJoin[ToString /@ symbL]
SymbolJoin[symbs__]    := SymbolJoin[{symbs}]

(* True if 'name' satisfies the options given by optL *)
allQoptions[HeadQs] [name_, optL_List] := And @@ (#[name]& /@ (HeadQs  /. optL /. Options[HeadQs]))
allQoptions[IndexQs][name_, optL_List] := And @@ (#[name]& /@ (IndexQs /. optL /. Options[IndexQs]))

(* visit each term in 'expr' and then act 'f' on them with arguments 'args' *)
forEachTerm[expr_Plus,  f_, args___] := forEachTerm[#, f, args]& /@ expr
forEachTerm[expr_Equal, f_, args___] := forEachTerm[#, f, args]& /@ expr
forEachTerm[expr_,      f_, args___] := f[expr, args]

(* get sign from a term *)
signTerm[-term_] := -1
signTerm[_]      := +1

(***************************** 1. Indices ***************************)
(*****
    IndexType
        |- Symbol  - RegularType
        |- String  - (Internal) DummyType
        |- Integer - ComponentType

            ComponentType
                Input:  Component_Integer : ...,-2,-1,1,2,...
                Output: Component_Integer : 1,2,...

    IndexKind
        Latin   : la,  ua,..., lo, uo, lp, up,..., lz, uz
        Greek   : l\[alpha], u\[alpha], ..., l\[mu], u\[mu],..., l\[xi], u\[xi],..., l\[Omega], u\[Omega]
        Capital : lA, uA,..., lO, uO, lP, uP,..., lZ, uZ

        Bar : lba, uba,..., lbo, ubo, lbp, ubp,..., lbz, ubz
        Dot : lda, uda,..., ldo, udo, ldp, udp,..., ldz, udz
        Hat : lha, uha,..., lho, uho, lhp, uhp,..., lhz, uhz

    allIndexCharacters[kind] = {...}
    dummyPreCharacter[kind]  = one of {"$", "%", "!", "@", "#", "&", ...}
    dummyState[kind]         = counters for getting unique dummy index
    indicesNumState[kind]    = counters for AddIndices

    indexKind[l <> a] ^= kind
    indexKind[u <> a] ^= kind

    DnIndexQ[l <> a] ^= True
    UpIndexQ[u <> a] ^= True
 *****)

(********** Basic Functions for Indices **********)

(*** index dn/up ***)
DnIndexQ[a_Integer] := a < 0
DnIndexQ[a_Symbol]  := DnIndexQ[ToString @ a]      (* for a general symbol *)
DnIndexQ[a_String]  := StringMatchQ[a, "l" ~~ __]
DnIndexQ[___]       := False

UpIndexQ[a_Integer] := a > 0
UpIndexQ[a_Symbol]  := UpIndexQ[ToString @ a]      (* for a general symbol *)
UpIndexQ[a_String]  := StringMatchQ[a, "u" ~~ __]
UpIndexQ[___]       := False

(*** index types ***)
ComponentIndexQ[0]         := False
ComponentIndexQ[a_Integer] := True
ComponentIndexQ[___]       := False

DummyIndexQ[a_String] := True   (* is an internally-generated dummy index? *)
DummyIndexQ[___]      := False

RegularIndexQ[a_Symbol] := True
RegularIndexQ[___]      := False

(********** Index Kinds **********)

DefineKind[symbL:{__Symbol},  kind_Symbol] := DefineKind[ToString /@ symbL, kind]
DefineKind[charL:{___String}, kind_Symbol] := (
        If [!checkIndexCharacters[charL], Return[]];
        If [!checkName[kind], Return[]];
        If [MemberQ[definedKindList, kind], Message[Msg::err, kind, "is already defined. Do RemoveKind[", kind, "] first."]; Return[]];
        If [Length[dummyPreListPrepared] < 1, Message[Msg::err, "Too many kinds are defined.", "", "", ""]; Return[]];

        dummyPreCharacter[kind] = First @ dummyPreListPrepared;
        dummyPreListPrepared    = Rest  @ dummyPreListPrepared;  (* update *)

        AppendTo[definedKindList, kind];
        AppendTo[dummyPreList,    dummyPreCharacter[kind]];

        dummyState[kind]      = 1;  (* counters for getting unique dummy indices when calling Dummy and DummyPair *)
        indicesNumState[kind] = 0;  (* for AddIndices *)

        setIndices[charL, kind];

        (* for Tensor.m *)
        If [kind =!= Zero,
            (* define Epsilon, Structuref, and Torsion associated with the kind *)
            If [kind =!= DefaultKind,
                defineOperand[SymbolJoin[Epsilon, kind], "\[Epsilon][" <> ToString[kind] <> "]", "*-",   {kind}, {-1}];
                defineOperand[SymbolJoin[Torsion, kind], "t["          <> ToString[kind] <> "]", "-bac", {kind}, {-1, -1, +1}];
                GetEpsilon[kind]    = SymbolJoin[Epsilon, kind];
                GetStructuref[kind] = SymbolJoin[Structuref, kind];
                GetTorsion[kind]    = SymbolJoin[Torsion, kind],
            (* else *)
                defineOperand[Epsilon, "\[Epsilon]", "*-",   {kind}, {-1}];
                defineOperand[Torsion, "t",          "-bac", {kind}, {-1, -1, +1}];
                GetEpsilon[kind]    = Epsilon;
                GetStructuref[kind] = Structuref;
                GetTorsion[kind]    = Torsion
            ],
        (* else *)
            GetEpsilon[kind]    = Null;
            GetStructuref[kind] = Null;
            GetTorsion[kind]    = Null
        ];

        getDerOps[kind]        = {};

        MetricSpaceQ[kind]     = False;
        GetMetric[kind]        = Null;

        CoordinateBasisQ[kind] = False;
        If [!MemberQ[{Zero, Latin}, kind], Off[CoordinateBasisFlag[kind]]];
    )

(* is a index in kind? *)
KindIndexQ[kind_?checkIndexKind] := (indexKind[#] === kind&)

RemoveKind[Zero]        := ( Message[Msg::err, "Cannot remove the Zero kind.", "", "", ""]; )
RemoveKind[Latin]       := ( Message[Msg::err, "Cannot remove the Latin kind.", "", "", ""]; )
RemoveKind[kind_Symbol] := (
        If [kind === DefaultKind, Message[Msg::err, kind, "is DefaultKind which cannot be removed.", "", ""]; Return[]];

        Module[{pos},
            If [!checkIndexKind[kind, True], Return[]];

            (* remove Epsilon, Structuref and Torsion associated with the kind *)
            GetEpsilon[kind]    = Null;
            GetStructuref[kind] = Null;
            GetTorsion[kind]    = Null;
            removeObject[SymbolJoin[Epsilon, kind]];
            removeObject[SymbolJoin[Structuref, kind]];
            removeObject[SymbolJoin[Torsion, kind]];

            getDerOps[kind]        = .;
            MetricSpaceQ[kind]     = .;
            CoordinateBasisQ[kind] = .;

            setIndices[{}, kind];

            dummyState[kind]      = .;
            indicesNumState[kind] = .;

            pos = Flatten @ Position[definedKindList, kind];
            definedKindList = Delete[definedKindList, pos];
            dummyPreList    = Delete[dummyPreList, pos];

            AppendTo[dummyPreListPrepared, dummyPreCharacter[kind]];
            dummyPreCharacter[kind] = .;

            If [kind =!= Dot, Remove[kind]];
        ]
    )

checkIndexCharacters[charL_List]            := checkIndexCharacters[charL, definedKindList]
checkIndexCharacters[charL_List, kindList_] :=
    If [IntersectingQ[Flatten @ Join[allIndexCharacters /@ kindList], charL],
        Message[Msg::err, charL, "includes characters already defined as indices.", "", ""]; False,
    (* else *)
        True
    ]

checkIndexKind[kindL_List, withMsg_:False] := And @@ (checkIndexKind[#, withMsg]& /@ kindL)
checkIndexKind[kind_,      withMsg_:False] := (* for an arbitrary non-list input *)
    If [!MemberQ[definedKindList, kind], If [withMsg, Message[General::invalid, kind, "indexKind"]]; False,
    (* else *)                    True]

checkName[oName_] := (
        If [MemberQ[reservedNameList, oName], Message[Msg::err, oName, "is reserved.", "", ""]; Return[False]];
        If [MemberQ[Flatten @ ShowIndices[All], oName], Message[Msg::err, oName, "is used as an index name!", "", ""]; Return[False]];
        True
    )

(********** SetIndices, AddIndices, and ShowIndices **********)

SetIndices[symbL:{___Symbol}, Zero]       := ( Message[Msg::err, "Zero's indices are fixed.", "", "", ""]; )
SetIndices[symbL:{___Symbol}]             := SetIndices[symbL, DefaultKind]
SetIndices[{},               kind_Symbol] := setIndices[{}, kind]
SetIndices[symbL:{__Symbol}, kind_Symbol] := SetIndices[ToString /@ symbL, kind]
SetIndices[charL:{__String}]              := SetIndices[charL, DefaultKind]
SetIndices[charL:{__String}, kind_Symbol] := ( If [checkIndexCharactersKind[charL, kind], setIndices[charL, kind]]; )
SetIndices[__]                             := Message[SetIndices::usage]

    (* check with definedKindList except kind *)
    checkIndexCharactersKind[charL_, kind_] := checkIndexCharacters[charL, DeleteCases[definedKindList, kind]]

setIndices[charL:{___String}, kind_Symbol, setQ_:True] :=
    Module [{lsymL, usymL},
        If [!checkIndexKind[kind, True], Return[]];
        (* Unprotect and TagUnset previously introduced index symbols *)
        If [setQ && Head[allIndexCharacters[kind]] === List && allIndexCharacters[kind] =!= {},  (* guard re-set *)
            lsymL = Symbol /@ (("Global`l"  <> #)& /@ allIndexCharacters[kind]);
            Unprotect @@ lsymL; (#/: DnIndexQ[#] = .)& /@ lsymL;

            usymL = Symbol /@ (("Global`u"  <> #)& /@ allIndexCharacters[kind]);
            Unprotect @@ usymL; (#/: UpIndexQ[#] = .)& /@ usymL;

            (#/: indexKind[#] = .)& /@ Join[lsymL, usymL];
        ];

        (* WARNING: THE SYMBOLS having the form l* and u* are all CLEARED! *)
        (* Clear index symbols. NB: Clear in String form to suppress evaluating *)
        Clear /@ (("Global`l" <> #)& /@ charL); Clear /@ (("Global`u" <> #)& /@ charL);

        (* TagSet to index symbols *)
        lsymL = Symbol /@ (("Global`l" <> #)& /@ charL); (#/: DnIndexQ[#] = True)& /@ lsymL;
        usymL = Symbol /@ (("Global`u" <> #)& /@ charL); (#/: UpIndexQ[#] = True)& /@ usymL;

        (#/: indexKind[#] = kind)& /@ Join[lsymL, usymL];

        (* Protect index symbols *)
        Protect @@ lsymL; Protect @@ usymL;

        If [setQ || allIndexCharacters[kind] === {},
            allIndexCharacters[kind] = charL,
        (* else *)  (* AddIndices *)
            allIndexCharacters[kind] = Join[allIndexCharacters[kind], charL]
        ];
    ]

AddIndices[arg_]                              := AddIndices[arg, DefaultKind]
AddIndices[symbL:{__Symbol},     kind_Symbol] := AddIndices[ToString /@ symbL, kind]
AddIndices[charL:{__String},     kind_Symbol] := ( If [checkIndexCharacters[charL], setIndices[charL, kind, False]]; )
AddIndices[num_Integer?Positive, kind_Symbol] := (
        If [!checkIndexKind[kind, True], Return[]];
        If [allIndexCharacters[kind] === {}, Message[Msg::err, "Use SetIndices[charL,", kind, "", ""]; Return[]];

        Do[addIndexTo[kind], num];
    )
AddIndices[___] := Message[AddIndices::usage]

    addIndexTo[kind_] :=
        Module[ {index, lsym, usym},
            (* +1 for generating an unique index, e.g., "a1"  --> "a2" *)
            index = StringJoin[First @ allIndexCharacters[kind], ToString @ (indicesNumState[kind] + 1)];
            If [!checkIndexCharacters[{index}], Return[]];
            indicesNumState[kind]++;

            (* update allIndexCharacters *)
            allIndexCharacters[kind] = Append[allIndexCharacters[kind], index];

            (* See SetIndices. WARNING: THE SYMBOLS having the form l* and u* are all CLEARED! *)
            (* Clear index symbols. NB: Clear in String form to suppress evaluating *)
            lsym = "Global`l" <> index; Clear[lsym];
            usym = "Global`u" <> index; Clear[usym];

            lsym = Symbol["Global`l" <> index]; (#/: DnIndexQ[#] = True)& /@ {lsym};
            usym = Symbol["Global`u" <> index]; (#/: UpIndexQ[#] = True)& /@ {usym};

            (#/: indexKind[#] = kind)& /@ {lsym, usym};
            Protect @@ {lsym, usym};
        ]
AddIndices[__] := Message[AddIndices::usage]

(* get all regular indices in String form *)
ShowIndices[]            := ShowIndices[DefaultKind]
ShowIndices[All]         := Join[ShowIndices /@ definedKindList]
ShowIndices[kind_Symbol] := (
        If [!checkIndexKind[kind], Return[{}]];
        Flatten[{SymbolJoin["l", #]& /@ allIndexCharacters[kind], SymbolJoin["u", #]& /@ allIndexCharacters[kind]}]
    ) /; MemberQ[definedKindList, kind]
ShowIndices[__] := Message[ShowIndices::usage]

(* return a kind from an index.
   NB: This function fully checks the format of an index. return errorIndex for an illegal index *)
indexKind[0]         := errorIndex
indexKind[a_Integer] := ComponentIndexQ
(* indexKind[a_Symbol] : See SetIndices and AddIndices *)
indexKind["l0"]      := Zero
indexKind["u0"]      := Zero
indexKind[a_String]  :=
    Module[{pos},
        If [IntegerQ[ToExpression @ StringDrop[a, 2]],  (* dummy index *)
            pos = Flatten @ Position[dummyPreList, StringTake[a, {2}]];
            If [pos =!= {}, definedKindList[[First @ pos]],
            (* else *)      errorIndex],
        (* else *)
            errorIndex
        ]
    ] /; DnIndexQ[a] || UpIndexQ[a]
indexKind[a_Symbol]        := indexKind[a, DefaultKind]  (* for the kind of symbols in coordinate systems *)
indexKind[a_Symbol, kind_] :=
    If [MemberQ[tCoordinates[kind], a],
        kind,
    (* else *)
        errorIndex
    ] /; VectorQ[tCoordinates[kind]]
indexKind[___] := errorIndex

(********** Utils for Indices **********)

(* gives an unique down dummy *)
Dummy[]      := Dummy[DefaultKind]
Dummy[kind_] :=	("l" <> dummyPreCharacter[kind] <> ToString[dummyState[kind]++]) /; MemberQ[definedKindList, kind]
Dummy[__]    := (Message[Dummy::usage]; "")

(* gives an unique-down dummy-pair in the form: {dn,up} *)
DummyPair[]      := DummyPair[DefaultKind]
DummyPair[kind_] :=	With[ {str = dummyPreCharacter[kind] <> ToString[dummyState[kind]++]},	{"l" <> str, "u" <> str} ] /; MemberQ[definedKindList, kind]
DummyPair[__]    := (Message[DummyPair::usage]; {"", ""})

FlipIndex[a_Integer]         := -a
FlipIndex[a_Symbol]          := Symbol[ FlipIndex[ToString @ a] ]
FlipIndex[a_String?DnIndexQ] := StringReplacePart[a, "u", {1,1}]
FlipIndex[a_String?UpIndexQ] := StringReplacePart[a, "l", {1,1}]
FlipIndex[a_]                := a

IndexOrderedQ[idxL1_?VectorQ, idxL2_?VectorQ, dummyQ_:True] :=  (* rule1 *) (* NB: Keep rule's declaration order *)
    Module[ {len1 = Length[idxL1], len2 = Length[idxL2], i},
        If [len1 =!= len2,
            len1 < len2,
        (* else *)
            i = 1;
            While [i <= len1,
                If[idxL1[[i]] =!= idxL2[[i]], Return[IndexOrderedQ[{idxL1[[i]], idxL2[[i]]}, dummyQ]]];
                i++
            ];
            True
        ]
    ]
IndexOrderedQ[idxL_ ?VectorQ, dummyQ_:True] := idxL === IndexSort[idxL, dummyQ]  (* rule2 *)

(* sorts indices according to four priorities: indexType < free/dummy < lexicographic < dn/up
   If dummyQ == False, neglect the free/dummy priorities. *)
IndexSort[{}, ___]                   := {}
IndexSort[{a_}, ___]                 := {a}
IndexSort[indexL_List, dummyQ_:True] :=
    With[ {dummyIndexSort = If[dummyQ, takePairs[indexL], {}], lexIndexSort = Union[ToUpIndex /@ indexL]},
        Last /@
            Sort[
                {
                    typeIndexSort[#],                           (* Index Type and Kind *)
                    MemberQ[dummyIndexSort, #],                 (* Free/Dummy *)
                    Position[lexIndexSort, ToUpIndex[#], {1}],  (* Lexicographic *)
                    UpIndexQ[#],                                (* Dn/Up *)
                    #
                }& /@ indexL
            ]
    ]

    typeIndexSort[a_Symbol] :=    (* Regular *)
        With[ {kind = indexKind[a]},
            If [kind === errorIndex,
                1.0,
            (* else *)
                1.0 + 0.1 * (First @ Flatten @ Position[definedKindList, kind])
            ]
        ]
    typeIndexSort[a_String] :=    (* Dummy *)
        With[ {kind = indexKind[a]},
            If [kind === errorIndex,
                3.0,
            (* else *)
                3.0 + 0.1 * (First @ Flatten @ Position[definedKindList, kind])
            ]
        ]
    typeIndexSort[_Integer] := 7  (* ComponentIndexQ *)

PairIndexQ[a_Integer,         _]         := False
PairIndexQ[_,                 a_Integer] := False
PairIndexQ[a_Symbol,          b_Symbol]  := strPairQ[ToString @ a, ToString @ b]
PairIndexQ[a_String,          b_String]  := strPairQ[a, b]
PairIndexQ[pairs:({_, _}..)]             := And @@ (PairIndexQ[#[[1]], #[[2]]]& /@ {pairs})
PairIndexQ[___]                          := False

    strPairQ[a_String, b_String] :=
        If [KindIndexQ[Zero][a] =!= True && StringDrop[a, 1] === StringDrop[b, 1],
            True,
        (* else *)
            False
        ] /; (DnIndexQ[a] && UpIndexQ[b]) || (UpIndexQ[a] && DnIndexQ[b])
    strPairQ[_, _] := False

(* gives contracted pairs in the form: {{dn,up},..}. *)
TakePairs[indexL_?VectorQ, iOpts___Rule] :=  (* {ub, la, lc, ud, lb, ua} => {{lb,ub}, {la,ua}} *)
    With[ {idxL = Select[indexL, allQoptions[IndexQs][#, {iOpts}]&]},
        {#, ToUpIndex[#]}& /@ Union[ToDnIndex /@ takePairs[idxL]]
   ]
TakePairs[___] := (Message[TakePairs::usage]; {})

(* is a non-component index? NB: syntax-checked via indexKind *)
TensorialIndexQ[a_]  := Not @ MemberQ[{errorIndex, ComponentIndexQ}, indexKind[a]]
TensorialIndexQ[___] := False

(* up -> dn *)
ToDnIndex[a_?UpIndexQ] := FlipIndex[a]
ToDnIndex[a_]          := a  (* if not UpIndexQ *)

(* dn -> up *)
ToUpIndex[a_?DnIndexQ] := FlipIndex[a]
ToUpIndex[a_]          := a  (* if not DnIndexQ *)

(* dn => -1, up => +1 *)
dnupState[idx_] := If [UpIndexQ[idx], +1, -1]

(* take free-tensorial indices. *)
takeFrees[indexL_List] := dropPairs @ Select[indexL, TensorialIndexQ]

(* drop or take not-sorted pairs from the indices *)
dropPairs[indexL_List] := Select[indexL, !inPairQ[indexL, #]&]
takePairs[indexL_List] := DeleteDuplicates @ Select[indexL, inPairQ[indexL, #]&]  (* {ub, la, lc, ud, lb, ua} => {ub,la, lb, ua}} *)
takePairsProper[indexL_List] :=                                                   (* {ub, la, lc, ud, lb, ua} => {{ub,lb}, {la,ua}} *)
    Module[{pairL, tmpL, i},
        pairL = takePairs[indexL]; tmpL = {};
        Do [
            If [inPairQ[Drop[pairL, i], pairL[[i]]], AppendTo[tmpL, pairL[[i]]]],
            {i, Length[pairL]}
        ];
        {#, FlipIndex[#]}& /@ tmpL
    ]

    inPairQ[indexL_, a_] :=
        With[ {fa = FlipIndex[a]},
            KindIndexQ[Zero][a] =!= True && TensorialIndexQ[a] && (fa =!= a && MemberQ[indexL, fa])  (* NB: When 'a' is NOT an index, FlipIndex[a] == a. *)
        ]

(* are all dn or all up? *)
upupdndnIndexQ[aIndexL_List] := SameQ @ (Sequence @@ Map[UpIndexQ, aIndexL])

(********** Check Indices **********)

(* check consistency of an index (and each of aIndexL) with the indexKind *)
ValidIndexQ[aIndex_]                               := ValidIndexQ[aIndex, DefaultKind, False]
ValidIndexQ[aIndexL_List,   kind_, withMsg_:False] := AllTrue[aIndexL, ValidIndexQ[#, kind, withMsg]&]
ValidIndexQ[0,              _,     withMsg_:False] := ( If [withMsg, Message[General::invalid, 0, "component index"]]; False )
ValidIndexQ[aIndex_Integer, kind_, withMsg_:False] :=
    With[ {nDim = GetDimension[kind]},
        If [PositiveIntegerQ[nDim] && Abs[aIndex] > nDim,
            If [withMsg, Message[Msg::err, "The absolute value of a component index", aIndex, "is larger than the dimension", nDim]]; False,
        (* else *)
            True
        ]
    ]
ValidIndexQ[aIndex_, kind_, withMsg_:False] :=
    If [!compatibleKindQ[aIndex, kind], If [withMsg, Message[General::invalid, aIndex, "index"]]; False,
    (* else *)                          True]

    (* NB: Component indices are compatible with all-kind of indices *)
    compatibleKindQ[aIndex_, ComponentIndexQ] := compatibleKindQ[aIndex, All]
    compatibleKindQ[aIndex_, All]             := indexKind[aIndex] =!= errorIndex
    compatibleKindQ[aIndex_, kind_Symbol]     := indexKind[aIndex] =!= errorIndex && MemberQ[{kind, ComponentIndexQ}, indexKind @ aIndex]
    compatibleKindQ[___]                      := False

(* check mutual-validity of indices. return False with a corresponding message when withMsg == True. *)
ValidIndicesQ[indexL_List]                        := ValidIndicesQ[indexL, DefaultKind, False]
ValidIndicesQ[indexL_List, kind_, withMsg_:False] := (
        If[!ValidIndexQ[indexL, kind, withMsg], Return[False]];
        !duplicatedIndicesQ[indexL, withMsg]
    )

(* are the tensorial indices duplicated? *)
duplicatedIndicesQ[indexL_List, withMsg_:False] :=
    With[ {idxL = Select[indexL, TensorialIndexQ]},
        If [Length[DeleteDuplicates[idxL]] =!= Length[idxL], If [withMsg, Message[Msg::err, "duplicated indices:", idxL, "", ""]]; True,
        (* else *)                                           False]
    ]

(******************** 2. Defining IndexedObject *********************)
(*****
    ObjectQ |- IndexedObjectQ |- IndexedOperatorQ
            |                 |- IndexedOperandQ  |- IndexedTensorQ
            |                                     |- IndexedFormQ
            |                                     |- ...
            |
            |- ScalarFunctionQ

        Tensors:

			IndexedObjectQ[oName]  ^= True
			IndexedOperandQ[oName] ^= True

			getType  [oName] ^= IndexedTensorQ
			getPrtStr[oName] ^= prtStr
			getKindL [oName] ^= kindL
			getDnupL [oName] ^= dnupL
			GetRank  [oName] ^= nRank
			getGenSet[oName] ^= GenSet

                kindL = |- {kind}     for zero, one, or arbitrary rank tensors with all the 'same' kind
                        |- {kind,...} for fixed rank tensors with various kinds

                    kind = one of (Or @@ definedKindList)

                dnupL = |- {}         for zero rank tensors
                        |- {dnup}     for one, or arbitrary rank tensors with all the 'same' dnup
                        |- {dnup,...} for fixed rank tensors with different dnups

                    dnup = -1 of +1

            oName[indices]

                number of indices === nRank or arbitrary

        Diff. Forms:

			IndexedObjectQ[fName]  ^= True
			IndexedOperandQ[oName] ^= True

			getType  [oName] ^= IndexedFormQ
			getPrtStr[fName] ^= prtStr
			getKindL [fName] ^= kindL
			getDnupL [fName] ^= dnupL
			GetRank  [fName] ^= nRank
			getGenSet[fName] ^= GenSet
			getDegree[fName] ^= formDegree

            fName[indices]

        Indexed Operators:

			indexedObjectQ  [opName] ^= True
			indexedOperatorQ[opName] ^= True

			getType  [opName] ^= opType
			getPrtStr[opName] ^= prtStr
			getKindL [opName] ^= kindL

                opType:
                    CD: opName[index, expr] like the covariant derivative
                    LD: opName[vName, expr] like the Lie derivative
                    XD: opName[expr]        like the exterior derivative
                    XP: opName[expr,...]    like the exterior product

            opName[arg, expr,...]

        ScalarFunctionQ === Tscalar, Power, Log, Sin, ...
 *****)

(********** Indexed ObjectQ *************)

(* remove indexed objects if not reserved *)
RemoveObject[oName_Symbol?IndexedObjectQ] := (
        If [MemberQ[reservedNameList, oName], Message[Msg::err, "Reserved name", oName, "cannot be removed!", ""]; Return[]];
        removeObject[oName];
	)
RemoveObject[nameL:{_Symbol..}] := ( Map[RemoveObject, nameL]; )

removeObject[oName_?IndexedObjectQ] := (
        Unprotect[oName];
        Remove[oName];
    )

(* for removing 'oName[_]' objects. NB: Remove[oName[kind]] dose NOT work *)
clearOperand[oName_, kind_] := (
        oName/: GetRank[oName[kind]] = .;
        oName/: getGenSet[oName[kind]] = .;
        oName/: getKindL[oName[kind]] = .;
        oName/: getDnupL[oName[kind]] = .;
        oName/: getPrtStr[oName[kind]] = .;
        oName/: getType[oName[kind]] = .;
        oName/: IndexedObjectQ[oName[kind]] = .;
        oName/: IndexedOperandQ[oName[kind]] = .;
        oName/: MakeBoxes[oName[kind][],       StandardForm] = .;
        oName/: MakeBoxes[oName[kind][args__], StandardForm] = .;
    )

(* is oName defined? *)
ObjectQ[oName_Symbol] := IndexedObjectQ[oName] || ScalarFunctionQ[oName]
ObjectQ[___]          := False

    (* is oName defined as an indexed object? *)
    IndexedObjectQ[___] := False

        (* is oName defined as an indexed operator? *)
        IndexedOperatorQ[___] := False

        (* IndexedOperandQ *)
        IndexedOperandQ[___] := False

            (* is oName defined as a tensor's name? *)
            IndexedTensorQ[oName_?IndexedOperandQ] := getType[oName] === IndexedTensorQ
            IndexedTensorQ[___]                    := False

    (* Tscalar, Power, Log, Sin, Cos, Tan, ... *)
    ScalarFunctionQ[Plus]     := False  (* Plus and Times are NumericFunction *)
    ScalarFunctionQ[Times]    := False
    ScalarFunctionQ[Tscalar]  := True
    ScalarFunctionQ[f_Symbol] := MemberQ[Attributes[f], NumericFunction]
    ScalarFunctionQ[___]      := False

(********* Defining Tensors ************)

(* zero-rank *)
Tdefine[oName_Symbol]                               := Tdefine[oName[]]
Tdefine[oName_Symbol,   prtStr_String]              := Tdefine[oName[], prtStr]
Tdefine[oName_Symbol,                  kind_Symbol] := Tdefine[oName[], kind]
Tdefine[oName_Symbol,   prtStr_String, kind_Symbol] := Tdefine[oName[], prtStr, kind]

(* finite-rank and no-symmetric, all the same shape *)
Tdefine[oNameL:{(_Symbol)..},                        nRank_Integer?Positive] := ( Tdefine[#, ToString @ #, nRank]& /@ oNameL; )
Tdefine[oNameL:{(_Symbol)..}, prtStrL:{(_String)..}, nRank_Integer?Positive] := Tdefine[oNameL, prtStrL, ToString @ nRank]

Tdefine[oName_Symbol,                nRank_Integer?Positive] := Tdefine[oName, ToString @ oName, ToString @ nRank]
Tdefine[oName_Symbol, prtStr_String, nRank_Integer?Positive] := Tdefine[oName, prtStr,           ToString @ nRank]

Tdefine[oName_Symbol,                nRank_Integer?Positive, kind_Symbol] := Tdefine[oName, ToString @ oName, ToString @ nRank, kind]
Tdefine[oName_Symbol, prtStr_String, nRank_Integer?Positive, kind_Symbol] := Tdefine[oName, prtStr,           ToString @ nRank, kind]

Tdefine[oName_Symbol[shape_Symbol],                nRank_Integer?Positive] := Tdefine[oName[shape], ToString @ oName, ToString @ nRank]
Tdefine[oName_Symbol[shape_Symbol], prtStr_String, nRank_Integer?Positive] := Tdefine[oName[shape], prtStr,           ToString @ nRank]

(* finite-rank|arbitrary-rank and no-symmetric|totally-symmetric|totally-anti-symmetric, all the same shape  *)
Tdefine[oNameL:{(_Symbol)..},                        permS_String] := Tdefine[oNameL, ToString /@ oNameL, permS]
Tdefine[oNameL:{(_Symbol)..}, prtStrL:{(_String)..}, permS_String] := (
        If [Length[oNameL] =!= Length[prtStrL], Message[Msg::err, "incompatible arguments:", oNameL, "and", prtStrL]; Return[]];
        MapThread[Tdefine[#1, #2, permS]&, {oNameL, prtStrL}];
    )

Tdefine[oName_Symbol,                permS_String] := Tdefine[oName, ToString @ oName, permS, DefaultKind]
Tdefine[oName_Symbol, prtStr_String, permS_String] := Tdefine[oName, prtStr,           permS, DefaultKind]

Tdefine[oName_Symbol,                permS_String, kind_Symbol] := Tdefine[oName, ToString @ oName, permS, kind]
Tdefine[oName_Symbol, prtStr_String, permS_String, kind_Symbol] := (
        If [checkName[oName],
            defineOperand[oName, prtStr, permS, {kind}, If [permS === "", {}, {-1}]]
        ];
    )

(* 주의:
    1. 함수 정의에서 패턴 매칭의 순서가 중요함
    2. Tdefine의 첫 번째 인자가 {}이면 oName == List인 경우로 패턴 매칭
    3. 따라서 Tdefine을 정의할 때 첫 번째 인자가 List인 경우를 먼저 정의해야 함
 *)

(* zero-rank *)
Tdefine[oNameL:{(_Symbol[])..}] := ( Tdefine[#, ToString @ Head @ #]& /@ oNameL; )

Tdefine[oName_Symbol[]]                             := Tdefine[oName[], ToString @ oName, DefaultKind]
Tdefine[oName_Symbol[], prtStr_String]              := Tdefine[oName[], prtStr,           DefaultKind]
Tdefine[oName_Symbol[],                kind_Symbol] := Tdefine[oName[], ToString @ oName, kind]
Tdefine[oName_Symbol[], prtStr_String, kind_Symbol] := ( If [checkName[oName], defineOperand[oName, prtStr, "", {kind}, {}]]; )

(* all the same shape *)
Tdefine[oName_Symbol[shape_Symbol],                permS_String] := Tdefine[oName[shape], ToString @ oName, permS] /; permS =!= ""
Tdefine[oName_Symbol[shape_Symbol], prtStr_String, permS_String] := (
        If [checkName[oName],
            defineOperand[oName, prtStr, permS, indexKind /@ {shape}, dnupState /@ {shape}]
        ];
    ) /; permS =!= ""

(* finite-rank and no-symmetric, various shapes *)
Tdefine[oName_Symbol[shapes:((_Symbol)..)]] := Tdefine[oName[shapes], StringJoin @ Take[Alphabet[], Length @ {shapes}]]

(* finite-rank and any symmetric, various shapes *)
Tdefine[oName_Symbol[shapes:((_Symbol)..)],                permS_String] := Tdefine[oName[shapes], ToString @ oName, permS] /; permS =!= ""
Tdefine[oName_Symbol[shapes:((_Symbol)..)], prtStr_String, permS_String] := (
	   If [checkName[oName],
	       defineOperand[oName, prtStr, permS, indexKind /@ {shapes}, dnupState /@ {shapes}]
	   ];
    ) /; permS =!= ""

Tdefine[___] := Message[Tdefine::usage]

(* full permmutation-weights in string format *)
AllPermutations[permS_String] :=
    Module[ {nRank, GS},
        {nRank, GS} = toRankAndGenSet[permS];
        If [GS === "Error", Return[]];  (* errors in permS *)

        If [nRank === -1, Message[Msg::err, "arbitrary rank", "", "", ""]; Return[]];

        toPermWeightStr[MakePermGroup[symToGenSet[GS, nRank]], nRank]
    ]
AllPermutations[___] := Message[AllPermutations::usage]

GStoString[GS_GenSet]              := toPermWeightStr[List @@ GS, mTensor`xPermML`Private`permDeg @ GS]
GStoString[GS_GenSet, len_Integer] := toPermWeightStr[List @@ GS, len]

    toPermWeightStr[{},         nRank_Integer] := StringJoin @@ Alphabet[][[Range[nRank]]]
    toPermWeightStr[permW_List, nRank_Integer] := StringJoin @@ Map[toOnePermWeightStr[#, nRank]&, permW]  (* permW -> permS *)

        toOnePermWeightStr[onePermW_List, nRank_] :=  (* onePermW -> onePermS *)
            With[ {str = StringJoin @@ Map[Alphabet[][[#]]&, PermutationList[onePermW[[1]], nRank]]},
                If [onePermW[[2]] === -1, "-" <> str, "+" <> str]
            ]

defineOperand[oName_, prtStr_String, permS_String, kindL_List, dnupL_List, oType_:IndexedTensorQ] := (
        If [!checkIndexKind[kindL, True], Return[]];

        If [permS === "",  (* scalar *)
            GetRank[oName] ^= 0; getGenSet[oName] ^= GenSet[]; getKindL[oName] ^= kindL; getDnupL[oName] ^= dnupL,
        (* else *)
            Module[ {nRank, GS, modKindL = kindL, modDnupL = dnupL, errnum},
                {nRank, GS} = toRankAndGenSet[permS];
                If [GS === "Error", Return[]];  (* errors in permS *)

				(* For checking the consistency: all the finite-rank indices have the same shape *)
				If [nRank > 1,
				    If [Length[kindL] === 1, modKindL = ConstantArray[First @ kindL, nRank]];
					If [Length[dnupL] === 1, modDnupL = ConstantArray[First @ dnupL, nRank]]
				];

				(* check the consistency *)
				If [nRank =!= -1,  (* finite rank *)
				    If [Length[modKindL] =!= 1,  (* the indices have various shapes *)
                		If [nRank =!= Length[modKindL], Message[Msg::err, "incompatible ranks between ", modKindL, "and", permS]; Return[]];

  						(* The opjects with dnupL == {} are special. Otherwise, Length[modKindL] === Length[modDnupL] *)
                		If [Length[modDnupL] =!= 1 && modDnupL =!= {},
                		    errnum = checkSymKindDnup[GS, nRank, modKindL, modDnupL];
                			If [errnum === -1, Message[Msg::err, "incompatibility between", permS, "and", modKindL]; Return[]];
                			If [errnum === -2, Message[Msg::err, "incompatibility between", permS, "and", modDnupL]; Return[]]
                		]
                	]
				];

				(* After checking the consistency: all the finite-rank indices have the same shape *)
				If [nRank > 1,
					If [Length[DeleteDuplicates @ kindL] === 1, modKindL = Take[kindL,1]];
					If [Length[DeleteDuplicates @ dnupL] === 1, modDnupL = Take[dnupL,1]]
				];

            	GetRank[oName] ^= nRank; getGenSet[oName] ^= GS; getKindL[oName] ^= modKindL; getDnupL[oName] ^= modDnupL;
            ]
        ];

		getPrtStr[oName] ^= prtStr; getType[oName] ^= oType;
		IndexedObjectQ[oName] ^= True; IndexedOperandQ[oName] ^= True;

       	oName/: MakeBoxes[oName[args___], StandardForm] :=
       	    interpretBox[oName[args],
                If [Length[{args}] === 0,
                    prtStr,
                (* else *)
                    Module[ {idxL},
       	                idxL = Transpose[
   	                        With[ {rc = indexCharSpace[#]}, If [indexKind[#] =!= errorIndex && UpIndexQ[#], rc[[{2, 1}]], rc[[{1, 2}]] ] ]& /@ {args}
   	                    ];
       	                SubsuperscriptBox[prtStr, TemplateBox[idxL[[1]], "RowDefault"], TemplateBox[idxL[[2]], "RowDefault"]]
   	                ]
               	]
           	];
	)

defineOperator[opName_Symbol, prtStr_String, opType_Symbol]        := defineOperator[opName, prtStr, opType, DefaultKind]
defineOperator[opName_Symbol, prtStr_String, opType_Symbol, kind_] := (
        If [opType =!= XP,
            opName/: MakeBoxes[opName[arg_, expr___], StandardForm] :=
                interpretBox[opName[arg, expr],
                    Switch [opType,
                        CD, TemplateBox[{If[indexKind[arg] =!= errorIndex && UpIndexQ[arg], SuperscriptBox, SubscriptBox][prtStr, First @ indexCharSpace[arg]],
                                        MakeBoxes[expr, StandardForm]}, "RowDefault"],
                        LD, TemplateBox[{ToBoxes @ Subscript[prtStr, If[IndexedOperandQ[arg], arg[], arg]],
                                        MakeBoxes[expr, StandardForm]}, "RowDefault"],
                        XD, TemplateBox[{StyleBox[prtStr, FontWeight -> "Bold"],
                                        TemplateBox[MakeBoxes[#, StandardForm]& /@ {arg, expr}, "RowDefault"]}, "RowDefault"]
                    ]
                ]
        ];
		IndexedObjectQ[opName] ^= True; IndexedOperatorQ[opName] ^= True;
		getType[opName] ^= opType; getPrtStr[opName] ^= prtStr; getKindL[opName] ^= {kind};
    )

(***** from xTensor *****)
SetAttributes[interpretBox, HoldFirst]
interpretBox[expr_, box_] :=
    InterpretationBox[
        StyleBox[box, AutoSpacing -> False, ShowAutoStyles -> False],
        expr,
        Editable -> False
    ]
(************************)

    checkSymKindDnup[GenSet[], _,      _,      _]      := 0
    checkSymKindDnup[sym_,     nRank_, kindL_, dnupL_] :=
        Module[{GS = symToGenSet[sym, nRank], sameL},
            If [GS === GenSet[], Return[0]];

            sameL = Select[Flatten[Position[kindL, #], 1]& /@ Union[kindL], (Length[#] > 1)&];
            If [And @@ ((Union[Flatten @ Orbits[#, GS, nRank]] =!= Union[#])& /@ sameL), Return[-1]];

            sameL = Select[Flatten[Position[dnupL, #], 1]& /@ Union[dnupL], (Length[#] > 1)&];
            If [And @@ ((Union[Flatten @ Orbits[#, GS, nRank]] =!= Union[#])& /@ sameL), Return[-2]];

            0
        ]

    indexCharSpace[a_Integer] :=  (* ComponentType *)
        With[ {n = Abs[a]},
            If [n > 9,
                If [n > 99, {OverscriptBox[n, "_"], ToBoxes @ Spacer[3 * ONESPACE]},   (* three spaces when n >= 100. *)
                (* else *)  {OverscriptBox[n, "_"], ToBoxes @ Spacer[2 * ONESPACE]}],  (* two spaces, otherwise. *)
            (* else *)
                {n, ToBoxes @ Spacer[ONESPACE]}
            ]
        ]
    indexCharSpace[a_Symbol]  := indexCharSpace[ToString[a]] /; indexKind[a] =!= errorIndex  (* only those introduced by SetIndices[] *)
    indexCharSpace[a_String]  := indexCharSpaceAux[StringDrop[a,1]] /; DnIndexQ[a] || UpIndexQ[a]
    indexCharSpace[arg_]      := indexCharSpaceAux[ToString @ arg]   (* for any others, e.g., la_, ub_ ... *)

        ONESPACE = 5.5

        indexCharSpaceAux[arg_String] :=
            If [StringLength[arg] === 1,
                With[ {str = ToString @ arg}, {str, ToBoxes @ Spacer[StringLength[str] * ONESPACE]} ],
            (* else *)
                Switch [StringTake[arg, {1}],  (* for decorating sub-kind indices *)
                    "b", With [{str = StringDrop[arg, 1]}, {OverscriptBox[str, "_"],            ToBoxes @ Spacer[StringLength[str] * ONESPACE]}],
                    "d", With [{str = StringDrop[arg, 1]}, {OverscriptBox[str, "."],            ToBoxes @ Spacer[StringLength[str] * ONESPACE]}],
                    "h", With [{str = StringDrop[arg, 1]}, {OverscriptBox[str, "^"],            ToBoxes @ Spacer[StringLength[str] * ONESPACE]}],
                    _,                                     {StyleBox[arg, FontColor -> Orange], ToBoxes @ Spacer[StringLength[ToString @ arg] * ONESPACE + 3]}
                ]
            ]

(* symmetry-expr to GenSet *)
symToGenSet["Antisymmetric", len_] := GenSet @@ ({Cycles[{#}],-1}& /@ Partition[Range @ len, 2, 1])
symToGenSet["Symmetric",     len_] := GenSet @@ ({Cycles[{#}],+1}& /@ Partition[Range @ len, 2, 1])
symToGenSet["Nonsymmetric",  len_] := GenSet[]
symToGenSet[GS_GenSet,       len_] := GS

(* permS -> {nRank, GenSet}, {nRank | -1, "Symmetric" | "Antisymmetric" | "Nonsymmetric"}, or {-1, "Error"} *)
toRankAndGenSet[permS_String] :=
    Module[ {strL, nRank, imagL, permL, rc},
        (* drop ' ', '+', '-' *)
        strL = Select[Characters[permS], (StringPosition[" +-", #] === {})&];
        If [strL === {}, Return[ {0, GenSet[]} ] ];  (* zero rank for permS == "" *)

        If [AllTrue[strL, DigitQ] || strL === {"*"},         (* are "num" or "*" *)
            strL = Select[Characters[permS], (# =!= " ")&];  (* get non-space characters from permS *)
            Switch [Last[strL],
                "+", If [First[strL] === "*", nRank = -1, nRank = ToExpression[StringJoin @@ Drop[strL, -1]]]; Return[ {nRank, "Symmetric"} ],
                "-", If [First[strL] === "*", nRank = -1, nRank = ToExpression[StringJoin @@ Drop[strL, -1]]]; Return[ {nRank, "Antisymmetric"} ],
                _,   If [First[strL] === "*", nRank = -1, nRank = ToExpression[StringJoin @@ strL]];           Return[ {nRank, "Nonsymmetric"} ]
            ],
        (* else *)
            (* " abc- bac +cab" -> {"abc", "-", " ", " ", "bac", " ", " ", "+", "cab"} -> {"abc", "-", "bac", "+", "cab"} *)
            strL = Select[StringSplit[permS, {" " -> "", "+" -> "+", "-" -> "-"}], (# =!= "") &];
            If [strL === {}, Return[ {0, GenSet[]} ]];

            (* {"abc", "-", "bac", "+", "cab"} -> {"+", "abc", "-", "bac", "+", "cab"} *)
            If [strL[[1]] =!= "+" && strL[[1]] =!= "-", strL = Join[{"+"}, strL]];

            (* {"+", "abc", "-", "bac", "+", "cab"} -> {{"+", "abc"}, {"-", "bac"}, {"+", "cab"}} -> {"+abc", "-bac", "+cab"} *)
            strL = StringJoin /@ Partition[strL, 2];
            nRank = (StringLength @ strL[[1]]) - 1;

            (* check consistency with the rank *)
            If [AnyTrue[strL, (StringLength[#] =!= nRank + 1)&],
                Message[General::invalid, permS, "perm; it has inconsistent rank"]; Return[ {-1, "Error"} ]  (* errors in permS *)
            ];

            (* {"+abc", "-bac", "+cab"} -> {Imag[{1,2,3}]}, -Imag[{2, 1, 3}], Imag[{3, 1, 2}]} *)
            imagL = stringToImag /@ strL;
            If [MemberQ[imagL, Null], Return[ {-1, "Error"} ] ];  (* errors in permS *)

            (* is the same perm but different weights? *)
            If [Length[imagL] > 1 && Length[imagL] =!= Length[Plus @@ imagL],
                Message[General::invalid, permS, "perm; it has inconsistent weights"]; Return[ {-1, "Error"} ]  (* errors in permS *)
            ];

Off[Arrays::symm0];
            permL = ToCycl /@ imagL;
            rc = Arrays[ConstantArray[nRank, nRank], permL][[3]];
On[Arrays::symm0];
            If [rc === ZeroSymmetric[{}],
                Message[General::invalid, permS, "perm; it has inconsistent weights"]; Return[ {-1, "Error"} ]  (* errors in permS *)
            ];

            {nRank, GenSet @@ DeleteDuplicates[permL]}
        ]
    ]

    (* String -> Imag or Null *)
    stringToImag[permS_String] :=
        Module[ {strL, imagL},
            (* drop ' ', '+', '-' *)
            strL = Select[Characters[permS], (StringPosition[" +-", #] === {})&];
            If [strL === {}, Return[ Imag[] ]];

            (* String -> Imag List *)
            imagL = strL /. MapIndexed[Rule[#1, First @ #2]&, Sort[strL]];  (* {d,s,a} -> {2,3,1} because Sort[{d,s,a}] == {a,d,s} *)
            If [!PermutationListQ[imagL], Message[General::invalid, permS, "perm"]; Return[]];

            If [Select[Characters[permS], (StringPosition[" ", #] === {})&][[1]] === "-",  (* if First[permS] === "-" *)
                If [Signature[imagL] =!= -1, Message[General::invalid, permS, "signed perm"]; Return[]];
                -Imag @@ imagL,
            (* else *)
                +Imag @@ imagL
            ]
        ]

(* returns one of (Or @@ definedKindList) if not component-index *)
indexKindProper[idx_]        := indexKindProper[idx, DefaultKind]
indexKindProper[idx_, kind_] := If [ComponentIndexQ[idx], kind, indexKind[idx]]

(* returns the kind of an IndexedObject according to the second argument 'idx': See markPairs. *)
KindOf[Kdelta[idx1_, idx2_], idx_] := If [MemberQ[{idx1, idx2}, idx], indexKindProper[idx], All]
KindOf[BD[arg_, expr___],    idx_] := If [arg === idx,                indexKindProper[idx], KindOf[expr, idx]]
KindOf[Epsilon[__],       idx_] := DefaultKind
KindOf[Metricg[_, _],     idx_] := DefaultKind
KindOf[Torsion[_, _, _],  idx_] := DefaultKind
KindOf[CD[arg_, expr___], idx_] := DefaultKind
KindOf[oName_?IndexedOperandQ[indices___],      idx_] :=
    With[ {pos = Position[{indices}, idx]},
        If [pos =!= {}, KindOf[oName, First @ Flatten @ pos],
        (* else *)      KindOf[oName]]  (* when not in *)
    ]
KindOf[opName_?IndexedOperatorQ[arg_, expr___], idx_] :=
    Switch [getType[opName],
        CD, If [arg === idx, KindOf[opName, arg], KindOf[expr, idx]],

        (* NB: duplicate code with KindOf[opName_?IndexedOperatorQ, arg_, ___] *)
        LD, KindOf[arg],
        _,  First @ getKindL[opName]
    ]

(* get kind of an object: Kdelta, Metricg, BD, CD, and LD-type are special *)
KindOf[oName_Symbol] := KindOf[oName, 1]
KindOf[Kdelta, idx_, ___]            := With [{kind = indexKindProper[idx, All]}, If [kind =!= errorIndex, kind, All]]
KindOf[BD,     idx_, ___]            := With [{kind = indexKindProper[idx, All]}, If [kind =!= errorIndex, kind, All]]
KindOf[Epsilon, __] := DefaultKind
KindOf[Metricg, __] := DefaultKind
KindOf[Torsion, __] := DefaultKind
KindOf[CD,      __] := DefaultKind
KindOf[oName_?IndexedTensorQ,   pos_Integer?Positive] :=
    With [{kindL = getKindL[oName]},
        If [Length[kindL] > 1, kindL[[Min[pos, GetRank @ oName]]],
        (* else *)             kindL[[1]]]  (* zero-rank or arbitrary rank, or all the same shape *)
    ]
KindOf[oName_?IndexedFormQ,     pos_Integer?Positive] :=  (* TODO: for diff-forms *)
    With [{kindL = getKindL[oName]},
        If [Length[kindL] > 1, kindL[[Min[pos, GetRank @ oName]]],
        (* else *)             kindL[[1]]]  (* zero-rank or arbitrary rank, or all the same shape *)
    ]
KindOf[opName_?IndexedOperatorQ, arg_, ___]           := If [getType[opName] === LD, KindOf[arg], getKindL[opName][[1]]]
KindOf[___] := DefaultKind  (* for protecting illegal use *)

(* get dnup at pos *)
dnupAt[oName_?IndexedOperandQ, pos_Integer?Positive] :=
	With [{dnupL = getDnupL[oName]},
        If [Length[dnupL] > 1, dnupL[[Min[pos, GetRank @ oName]]],
        (* else *)             dnupL[[1]]  (* zero-rank or arbitrary rank, or all the same shape *)
		]
	]

dnupOf[oName_?IndexedOperandQ, aIndexL_List] := dnupAt[oName, #]& /@ Range[Length @ aIndexL]

(* are two kinds compatible with each other? *)
kindMatchQ[All,          _]            := True
kindMatchQ[_,            All]          := True
kindMatchQ[kind1_Symbol, kind2_Symbol] := kind1 === kind2
kindMatchQ[__]                         := False

(********** Index Symmetries **********)

GetSymmetry[oName_?IndexedOperandQ] := getGenSet[oName]

SetSymmetry[oName_Symbol?IndexedOperandQ, permS_String] :=
    Module[ {nRank, GS},
        {nRank, GS} = toRankAndGenSet[permS];

        (* errors in permS *)
        If [GS === "Error", Message[Msg::err, "invalid format: ", permS, "", ""]; Return[]];
        If [nRank =!= GetRank[oName], Message[Msg::err, "incompatible rank: ", nRank, "", ""]; Return[]];

        setSymmetry[oName, GS];
    ]

    setSymmetry[oName_, sym_] := ( getGenSet[oName] ^= sym; )

(* generate GenSet according to the number of indices. NB: Kdelta is anti-symmetric when the metric of the second index is anti-symmetric *)
getGenSetOf[Kdelta[idx1_, idx2_]] :=
    If [metricSymmetry[indexKindProper @ idx2] === -1, GenSet[{Cycles[{{1, 2}}], -1}],
    (* else *)                                         GenSet[{Cycles[{{1, 2}}], +1}]] /; MetricSpaceQ[indexKindProper @ idx2]
getGenSetOf[Kdelta[idx1_, idx2_]] := GenSet[]

getGenSetOf[oName_?IndexedOperandQ[idices___]]   := getGenSetOf[oName, Length @ {idices}]
getGenSetOf[oName_?IndexedOperandQ, len_Integer] :=
    With[ {nRank = GetRank[oName], GS = symToGenSet[getGenSet @ oName, len]},
        If [len =!= nRank,
            If [IndexedFormQ[oName] && len === getDegree[oName] + nRank,  (* p-form as a tennsor *)
                Join[symToGenSet["Antisymmetric", getDegree[oName]],
                     GS /. Cycles[{cycs__}] :> Cycles[{cycs} + getDegree[oName]]],  (* See displaceSlots and xSymmetryOf in xToCanonical.m *)
            (* else *)
                selectSlots[GS, If [nRank === -1, len, Min[len, nRank]]]  (* adjust according to the # of indices *)
            ],
        (* else *)
            GS
        ]
    ]

    selectSlots[GS_GenSet, len_Integer] := Select[selectCycls[#, len]& /@ GS, (#[[1]] =!= Cycles[{}])&]

        selectCycls[{Cycles[cycl_],-1}, len_] := {Cycles[Select[cycl, allSmallerEqual[#, len]&]],-1}
        selectCycls[{Cycles[cycl_],+1}, len_] := {Cycles[Select[cycl, allSmallerEqual[#, len]&]],+1}

            allSmallerEqual[lst_List, len_Integer] := AllTrue[lst, (# <= len)&]

(********** Tscalar/ErrorT **********)

Tscalar/: MakeBoxes[Tscalar[expr_], StandardForm] :=
    interpretBox[Tscalar[expr],
        TemplateBox[{
            StyleBox["(", FontColor -> RGBColor[1, 0, 1]],
            MakeBoxes[expr, StandardForm],
            StyleBox[")", FontColor -> RGBColor[1, 0, 1]]
        }, "RowDefault"]
    ]

ErrorT/: MakeBoxes[ErrorT[oName_][args___], StandardForm] := interpretBox[ErrorT[oName][args], StyleBox[MakeBoxes[oName[args], StandardForm], FontColor -> Red]]
ErrorT/: MakeBoxes[ErrorT[oTerm_],          StandardForm] := interpretBox[ErrorT[oTerm],       StyleBox[MakeBoxes[oTerm,       StandardForm], FontColor -> Red]]

(* rules *)
Tscalar[expr_Plus] := Map[Tscalar, expr] /; FreePatternQ[expr]

Tscalar[1]                                           := 1
Tscalar[pre_. expr_Symbol                    post_.] := expr        * Tscalar[pre post] /; FreePatternQ[{pre, expr, post}]
Tscalar[pre_. c_?constantQ                   post_.] := c           * Tscalar[pre post] /; FreePatternQ[{pre, c, post}]
Tscalar[pre_. sfName_?ScalarFunctionQ[arg__] post_.] := sfName[arg] * Tscalar[pre post] /; FreePatternQ[{pre, arg, post}]

(* True if x is a number or a numeric symbol or a constant symbol. Otherwise False. *)
constantQ[_Integer | _Rational | _Real | _Complex] := True
constantQ[c_]                                      := NumericQ[c] || constantSymbolQ[c]

    constantSymbolQ[s_Symbol] := MemberQ[Attributes[s], Constant]
    constantSymbolQ[s_]       := False

(**************** 3. Operations on Indexed Expressions **************)

(********** findIndices **********)

(* find non-sorted (free-)indices from a term, which are valid within the object's kindness. *)
findIndices    [term_, opts___Rule] := indicesOf[term, {opts}]
findFreeIndices[term_, opts___Rule] :=
    Module[{indexL},
        indexL = indicesOf[term, FilterRules[{opts}, Except @ IndexQs]];  (* find indices without considering IndexQs *)
        indexL = dropPairs @ Select[indexL, TensorialIndexQ];             (* drop pairs from all tensorial indices *)
        Select[indexL, allQoptions[IndexQs][#, {opts}]&]                  (* finally consider IndexQs *)
    ]

(* find aLL kinds of non-sorted (free-)indices from a term *)
findIndicesAll    [term_, opts___Rule] := indicesOf[term, {opts}, True]
findFreeIndicesAll[term_, opts___Rule] := dropPairs @ Select[DeleteDuplicates @ findIndicesAll[term, opts], TensorialIndexQ]

(* return all/compatible indices satisfying optL *)
indicesOf[expr_Plus,          optL_, allQ_:False] := Flatten @ Map[indicesOf[#, optL, allQ]&, List @@ expr]
indicesOf[expr_Equal,         optL_, allQ_:False] := Flatten @ Map[indicesOf[#, optL, allQ]&, List @@ expr]
indicesOf[expr_Times,         optL_, allQ_:False] := Flatten @ Map[indicesOf[#, optL, allQ]&, List @@ expr]
indicesOf[expr:(oName_[___]), optL_, allQ_:False] := indicesOfObject[expr, optL, allQ] /; allQoptions[HeadQs][oName, optL]
indicesOf[___]                                    := {}

    Options[ResetDummies] = {$FormDropIndices -> False}
    indicesOfObject[oName_?IndexedOperandQ[indices__], optL_, allQ_] :=
        Module[ {indexL = Select[{indices}, allQoptions[IndexQs][#, optL]&], newIdxL},
            If [IndexedFormQ[oName] && GetRank[oName] =!= 0 && ($FormDropIndices /. optL /. Options[indicesOfObject]),
                indexL = Drop[indexL, -GetRank[oName]]  (* See dualStarTerm *)
            ];

            If [allQ,
                indexL,
            (* else *)
                With[ {nRank = GetRank[oName]},
                    newIdxL = indexL;
                    If [IndexedTensorQ[oName] && nRank =!= -1 && Length[indexL] =!= nRank, newIdxL = Take[indexL, Min[Length[indexL], nRank]]];
                    (* NB: For IndexedFormQ[oName], returns the indices only in the indexed-form: Omega[lmu, lnu, la, ub] => {la, ub} *)
                    Select[newIdxL, ValidIndexQ[#, KindOf[oName, First @ Flatten @ Position[{indices}, #]]]&]
                ]
            ]
        ]
    indicesOfObject[opName_?IndexedOperatorQ[arg_, expr___], optL_, allQ_] :=
        Module[ {hOptL = FilterRules[optL, HeadQs], modOptL = FilterRules[optL, Except @ HeadQs], kind},
            If [hOptL =!= {},
                hOptL = {HeadQs -> DeleteCases[hOptL[[1,2]], IndexedOperatorQ]};  (* remove IndexedOperatorQ from hOptL *)
                modOptL = Join[modOptL, hOptL]
            ];

            kind = KindOf[opName, arg];
            Switch [getType[opName],
                CD, If [allQ || ValidIndexQ[arg, kind], Join[ Select[{arg}, allQoptions[IndexQs][#, optL]&], indicesOf[expr, modOptL, allQ] ],
                                                        indicesOf[expr, modOptL, allQ]],
                LD, indicesOf[expr, modOptL, allQ],
                XD, indicesOf[arg, modOptL, allQ],  (* expr === Null *)
                XP, Flatten @ Map[indicesOf[#, modOptL, allQ]&, {arg, expr}]
            ]
        ]
    indicesOfObject[sfName_?ScalarFunctionQ[args___], optL_, allQ_] := Flatten @ Map[indicesOf[#, optL, allQ]&, {args}]
    indicesOfObject[expr_,                            _,     _]     := {}

(********** Utils for indexed objects **********)

(* Scalar === indexed scalar f[] || Fully contracted tensor product || ScalarFunction *)
NoIndexQ[f_?scalarNameQ[]]   := True
NoIndexQ[expr_, opts___Rule] :=
    If [ScalarFunctionQ[Head[expr]],
        True,
    (* else *)
        If [!freeObjectQ[expr, Sequence @@ FilterRules[{opts}, HeadQs]], findFreeIndices[expr, opts] === {},  (* f[] or a fully contracted tensor product *)
        (* else *)                                                       False]
    ]

(* expand indexed objects satisfying 'hOpts' *)
SetAttributes[expandObject, Listable]
expandObject[expr_, opts___Rule] := Expand[ wrapObject[expr, $FOREXPAND, Sequence @@ FilterRules[{opts}, HeadQs]], $FOREXPAND ] /. $FOREXPAND -> Identity
expandObject[args___]            := args

(* is free of indexed objects? *) (* NB: Default option for HeadQs is IndexedObjectQ *)
SetAttributes[freeObjectQ, Listable]
freeObjectQ[expr_, opts___Rule] := FreeQ[ wrapObject[expr, $FORFREE, Sequence @@ FilterRules[{opts}, HeadQs]], $FORFREE ]
freeObjectQ[args___]            := True

(* visit each objects in 'expr' and then act 'f' with arguments 'args' and 'hOptL' *)
(* NB: Default option for HeadQs is IndexedObjectQ *)
forEachObject[expr_Plus,       hOptL_, f_, args___] := forEachObject[#, hOptL, f, args]& /@ expr  (* each term *)
forEachObject[expr_Equal,      hOptL_, f_, args___] := forEachObject[#, hOptL, f, args]& /@ expr
forEachObject[expr_Times,      hOptL_, f_, args___] := forEachObject[#, hOptL, f, args]& /@ expr  (* each factor *)
forEachObject[expr:name_[___], hOptL_, f_, args___] := f[expr, args] /; allQoptions[HeadQs][name, hOptL]
forEachObject[expr_,           _,      _,      ___] := expr

(* return {non-indexed objects, indexed objects} of a term: Apply[Times, {non-indexed objects, indexed objects}] === aTerm *)
splitTerm[aTerm_Times,         hOptL_List] := Times @@ Map[splitTerm[#, hOptL]&, List @@ aTerm]
splitTerm[aTerm:(oName_[___]), hOptL_List] := {1, aTerm} /; allQoptions[HeadQs][oName, hOptL]
splitTerm[expr_, ___]                      := {expr, 1}

(* wrap indexed objects in expr with wrapSymb *)
SetAttributes[wrapObject, Listable]
wrapObject[expr_, wrapSymb_Symbol, opts___Rule] := forEachObject[expr, FilterRules[{opts}, HeadQs], wrapWith, wrapSymb]

    wrapWith[expr_, wrapSymb_] := wrapSymb[expr]

(* is an indexed scalar? *)
scalarNameQ[oName_?IndexedTensorQ] := GetRank[oName] === 0
scalarNameQ[___]                   := False

(* is an indexed vector? *)
vectorNameQ[oName_?IndexedTensorQ] := GetRank[oName] === 1
vectorNameQ[fName_?IndexedFormQ]   := MetricSpaceQ[KindOf @ fName] && getDegree[fName] === 1
vectorNameQ[___]                   := False

(* reordering indices of IndexedObject *)
AntisymmetrizeIndices[indexL_?VectorQ, expr_, opts___Rule] := symmetrizeAux[indexL, expr, True, opts]
AntisymmetrizeIndices[___]                                 := Message[AntisymmetrizeIndices::usage]

SymmetrizeIndices[indexL_?VectorQ, expr_, opts___Rule] := symmetrizeAux[indexL, expr, False, opts]
SymmetrizeIndices[___]                                 := Message[SymmetrizeIndices::usage]

    symmetrizeAux[indexL_, expr_, antiQ_, opts___Rule] := (
            If [!ValidIndicesQ[indexL, All, True], Return[expr]];
            forEachTerm[expandObject[expr, opts], symmetrizeTerm, indexL, FilterRules[{opts}, HeadQs], antiQ]
        )

        symmetrizeTerm[aTerm_, symIndexL_, hOptL_List, antiQ_] :=
            Module[ {ordTerm, oTerm},
                {ordTerm, oTerm} = splitTerm[aTerm, hOptL];
                ordTerm * symmetrizeTermAux[oTerm, symIndexL, antiQ, findIndicesAll[oTerm, Sequence @@ hOptL]]
            ]

            symmetrizeTermAux[oTerm_, symIndexL_, antiQ_, indexL_] :=
                If [!AllTrue[symIndexL, (MemberQ[indexL, #])&],  (* if no symIndex in oTerm *)
                    Message[Msg::warn, symIndexL, "is not subset of", indexL, ""]; oTerm,
                (* else *)
                    Module[ {sIndexL = Sort[symIndexL], allSymL, rc},
                        (* all possible permutations of symIndexL: may be long *)
                        allSymL = Permutations @ sIndexL;

                        (* List of re-ordered oTerms *)
                        rc = oTerm /. (Inner[Rule, sIndexL, #, List]& /@ allSymL);

                        If [antiQ === True, rc = Dot[(Signature[#]& /@ allSymL), rc],  (* Antisymmetrize *)
                        (* else *)          rc = Plus @@ rc];
                        rc / (Length[symIndexL]!)
                    ]
                ]

(********** Dummy Indices **********)

SetAttributes[Dum, Listable]
Dum[expr_, opts___Rule] := forEachTerm[expandObject[expr, opts], dumTerm, RegularIndexQ, FilterRules[{opts}, IndexQs], FilterRules[{opts}, HeadQs]]
Dum[___]                := Message[Dum::usage]

SetAttributes[DumFresh, Listable]
DumFresh[expr_, opts___Rule] := forEachTerm[expandObject[expr, opts], dumTerm, TensorialIndexQ, FilterRules[{opts}, IndexQs], FilterRules[{opts}, HeadQs]]
DumFresh[___]                := Message[DumFresh::usage]

dumTerm[aTerm_, selectQ_, iOptL_List, hOptL_List]  :=
    Module[ {ordTerm, oTerm, indexL},
        {ordTerm, oTerm} = splitTerm[aTerm, hOptL];

        (* get indices which obeying selectQ and IndexQs from indexed objects satisfying hOptL *)
        indexL = Select[indicesOf[oTerm, Join[iOptL, hOptL]], selectQ];
        If [indexL === {}, Return[aTerm]];

        ordTerm * dumTermAux[oTerm, indexL]
    ]

    dumTermAux[oTerm_, {}]      := oTerm
    dumTermAux[oTerm_, {_}]     := oTerm
    dumTermAux[oTerm_, indexL_] :=
        Module[ {pairL, dummyL},
            pairL = TakePairs @ indexL;
            If [pairL === {}, Return[oTerm]];

            dummyL = DummyPair[indexKind @ First @ #]& /@ pairL;
            oTerm /. MapThread[Rule, {Flatten[pairL, 1], Flatten[dummyL, 1]}]
        ]

(* reset dummy indices *)
SetAttributes[ResetDummies, Listable]
Options[ResetDummies] = {All -> False, Dummy -> ""}
ResetDummies[expr_, opts___Rule] := forEachTerm[expandObject[expr, opts], resetDummiesTerm, FilterRules[{opts}, IndexQs], FilterRules[{opts}, HeadQs], opts]
ResetDummies[expr___]            := expr

resetDummiesTerm[aTerm_, iOptL_List, hOptL_List, opts___Rule] :=
    Module[ {ordTerm, oTerm, indexL, dummyL},
        {ordTerm, oTerm} = splitTerm[aTerm, hOptL];

        If [All /. {opts} /. Options[ResetDummies],
            (* get ALL kinds of contracted indices WITHOUT considering the kindness of indexed objects,
               and then locally Dum to keep the order of dummyL *)
            oTerm = dumTermSpecial[oTerm, indicesOf[oTerm, hOptL, True]]
        ];

        (* get all kinds of "dummy" indices *)
        indexL = indicesOf[oTerm, hOptL, True];
        dummyL = Select[indexL, DummyIndexQ];

        If [iOptL =!= {}, dummyL = Flatten @ (Select[dummyL, #]& /@ iOptL[[1,2]])];
        If [dummyL === {}, Return[aTerm]];

		(* reset ALL kinds of contracted indices WITH considering the kindness of indexed objects *)
        ordTerm * resetDummiesTermAux[oTerm, dummyL, Complement[Select[indexL, TensorialIndexQ], dummyL], opts]
    ]

    (* for resetDummiesTerm *)
    dumTermSpecial[oTerm_, {}]      := oTerm
    dumTermSpecial[oTerm_, {_}]     := oTerm
    dumTermSpecial[oTerm_, indexL_] :=
        With[ {pairL = TakePairs @ indexL},
            If[pairL === {},
                oTerm,
            (* else *)
                Module[ {cntDummy, pair, dummyL},
                    (* re-set counters for each kind *)
                    (cntDummy[#] = 1)& /@ definedKindList;

                    (* locally gives unique dummy pair *)
                    pair[kind_] := {"l" <> dummyPreCharacter[kind] <> ToString[cntDummy[kind]],
                                    "u" <> dummyPreCharacter[kind] <> ToString[cntDummy[kind]++]};

                    dummyL = pair[indexKind @ #[[1]]]& /@ pairL;
                    oTerm /. MapThread[Rule, {Flatten[pairL, 1], Flatten[dummyL, 1]}]
                ]
            ]
        ]

    resetDummiesTermAux[oTerm_, {},      _,      opts___] := oTerm
    resetDummiesTermAux[oTerm_, dummyL_, freeL_, opts___] := oTerm /. Flatten[reOrderRuleEachKind[Select[dummyL, KindIndexQ[#]],
                                                                                                  remainingIndicesKind[freeL, #, opts]]& /@ definedKindList]

        reOrderRuleEachKind[{},      _]           := {}
        reOrderRuleEachKind[dummyL_, remainingL_] :=
            Module[{splitL, chrL, newL},
                (* split "l$num" and "uc into {"l", "num"} and {"u", "c"}, respecively *)                    (* {l$3,u$3,lc,uc} --> {{l,3},{u,3},{l,c},{u,c}} *)
                splitL =
                    If [DummyIndexQ[#], {StringTake[#, 1], StringDrop[#, 2]},
                    (* else *)          {StringTake[#, 1], StringDrop[#, 1]}
                    ]& /@ (ToString /@ dummyL);

                chrL = DeleteDuplicates @ Map[#[[2]]&, splitL];                                              (* --> {3,c} *)

				(* Check Length[remainingL] >= Length[dummyL]? If not, return {}. *)
				If [Length[remainingL] < Length[chrL],
				    With[ {kind = indexKind @ First @ dummyL, len = Length[chrL]},
				    	Message[Msg::note, "In", kind, "it needs to add, at least,", len, "more indices. Use AddIndices[num, kind]."];
				    	Return[{}]
				    ]
				];

                newL = Map[SymbolJoin, splitL /. MapThread[Rule, {chrL, Take[remainingL, Length @ chrL]}]];  (* --> {la,ua,lb,ub} *)
                MapThread[Rule, {dummyL, newL}]                                                              (* --> {l$3->la,u$3->ua,lc->lb,uc->ub} *)
            ]

(* return indices from kind's allIndexCharacters, which do not contain the freeL's indices *)
remainingIndicesKind[freeL_, kind_, opts___] :=
    With[{allIdx = DeleteDuplicates @ Join[Characters[Dummy /. {opts} /. Options[ResetDummies]], allIndexCharacters[kind]]},
        With[ {freeChrs = StringDrop[#, 1]& /@ (ToString /@ Select[freeL, KindIndexQ[kind]])},
            Select[allIdx, (Not @ MemberQ[freeChrs, #])&]  (* to keep the order of the added indices *)
        ]
    ]

(********** Sum Dummy **********)

(* numeric SumDum *)
SumDum[{lower_Integer?Positive, upper_Integer?Positive}, expr_,              opts___Rule] := SumDum[{lower, upper}, expr, DefaultKind, opts]
SumDum[{lower_Integer?Positive, upper_Integer?Positive}, expr_, kind_Symbol, opts___Rule] :=
    Module[{iOptL},
        If [!checkIndexKind[kind, True], Return[expr]];

        (* set IndexQs to ValidIndexQ if no index options *)
        iOptL = {IndexQs -> {ValidIndexQ[#, kind]&}};

        sumDumWithoutKind[{lower, upper}, expr, iOptL, opts]
    ]

    sumDumWithoutKind[{lower_, upper_}, expr_, iOptL_, opts___] :=
        Module[{hOptL},
            (* Fix BUG: e.g., Log[V[la]V[ua]] =!=> Log[V[-1]V[1]] + Log[V[-2]V[2]] + ... *)
            hOptL = FilterRules[{opts}, HeadQs];
            If [hOptL =!= {},
                With[ {modL = DeleteCases[hOptL[[1,2]], ObjectQ]},
                    hOptL = If [modL =!= {}, {HeadQs -> modL}, {}]  (* drop ObjectQ in opts, if exists *)
                ]
            ];

            If [lower < upper, forEachTerm[expandObject[expr, opts], sumDumNumericTerm, {lower, upper}, iOptL, hOptL],
            (* else *)         expr]
        ]

(* numeric SumDum in component mode *)
SumDum[expr_,              opts___Rule] := SumDum[expr, DefaultKind, opts]
SumDum[expr_, kind_Symbol, opts___Rule] :=
    Module[ {nDim},
        If [!checkIndexKind[kind, True], Return[expr]];

        nDim = GetDimension[kind];
        If [!PositiveIntegerQ[nDim],
            Message[Msg::warn, "Component mode of SumDum requires Dimension for", kind, "Use SetDimension.", ""]; Return[expr]
        ];

        SumDum[{1, nDim}, expr, kind, opts]
    ]
SumDum[___] := Message[SumDum::usage]

	sumDumNumericTerm[aTerm_, {lower_, upper_}, iOptL_List, hOptL_List] :=
	(* numeric dummy sum of a term. return sum of them *)
	    Module[{ordTerm, oTerm},
    	    {ordTerm, oTerm} = splitTerm[aTerm, hOptL];
        	If [oTerm === 1, aTerm, ordTerm * sumDumNumericAux[oTerm, {lower, upper}, iOptL, hOptL]]
    	]

	    sumDumNumericAux[oTerm_, {lower_, upper_}, iOptL_, hOptL_] :=
    	    With[ {pairL = TakePairs @ findIndices[oTerm, Sequence @@ Join[iOptL, hOptL]]},
        	    If [pairL === {},
            	    oTerm,
	            (* else *)
    	            Module[{rcL, i, j},
        	            rcL = oTerm;
            	        Do [
                	        rcL = rcL /. {pairL[[i,1]] -> -j, pairL[[i,2]] -> j};  (* prepare for Table generation *)
                    	    rcL = Table[rcL, {j, lower, upper}],                   (* dummy indices -> component indices *)
                            {i, Length[pairL]}
	                    ];
    	                If [rcL === oTerm, oTerm, Plus @@ Flatten[rcL, Length[pairL] - 1]]
        	        ]
            	]
	        ]

(* symbolic SumDum *)
SumDum[argLs:(({_, _, __}?VectorQ)..), expr_, opts___Rule] :=
    Module[{rangeL = ToDnIndex /@ {argLs}, hOptL = FilterRules[{opts}, HeadQs]},
        (* Fix BUG: e.g., Log[V[la]V[ua]] =!=> Log[V[-1]V[1]] + Log[V[-2]V[2]] + ... *)
        If [hOptL =!= {},
            With[ {modL = DeleteCases[hOptL[[1,2]], ObjectQ]},
                hOptL = If [modL =!= {}, {HeadQs -> modL}, {}]  (* drop ObjectQ in opts, if exists *)
            ]
        ];

        forEachTerm[expandObject[expr, opts], sumDumSymbolicTerm, rangeL, hOptL]
    ]

	sumDumSymbolicTerm[aTerm_, rangeL_, hOptL_List] :=
	(* symbolic dummy sum of a term. return sum of them *)
	    Module[{ordTerm, oTerm},
	        {ordTerm, oTerm} = splitTerm[aTerm, hOptL];
	        ordTerm * sumDumSymbolicIndexedTerm[oTerm, rangeL, hOptL]
	    ]

		sumDumSymbolicIndexedTerm[oTerm_, rangeL_, hOptL_] :=
		    Module[{indexL, newRangeL = {}, aIndex, aRangeL, ruleL, rcL, i, j},
		        indexL = Select[findIndicesAll[oTerm, Sequence @@ hOptL], TensorialIndexQ];  (* neglect kinds of objects in oTerm *)

		        (* get rangeL of dummy indices *)
		        Do [
		            aIndex = rangeL[[i,1]];
		            If [Position[indexL, aIndex] === {},
		                Message[Msg::warn, "no compatible index:", aIndex, "in", oTerm]; Continue[],
		            (* else *)
		                If [Position[indexL, FlipIndex[aIndex]] === {}, Message[Msg::warn, "not dummy index:", aIndex, "in", indexL]; Continue[]]
		            ];
	    	        newRangeL = Join[newRangeL, {rangeL[[i]]}],
                    {i, Length[rangeL]}
	        	];
		        If [newRangeL === {}, Return[oTerm]];

		        (* substitution *)
	    	    rcL = oTerm;
	        	Do [
    	        	(* {{la, ua}, {-1,1}, {li, ui},...} for {la, -1, li,...} *)
	        	    aRangeL = Map[{#, FlipIndex[#]}&, newRangeL[[i]]];

		            ruleL = {};
    		        Do [
        		        ruleL = Join[ruleL, { {aRangeL[[1,1]] -> aRangeL[[j,1]], aRangeL[[1,2]] -> aRangeL[[j,2]]} }],
                        {j, 2, Length[aRangeL]}
            		];
		            rcL = Map[(rcL /. #)&, ruleL],
                    {i, Length[newRangeL]}
    		    ];

	    	    If [rcL === oTerm, oTerm,  (* not summed *)
    	    	(* else *)         Plus @@ Flatten[rcL, Length[newRangeL] - 1]]
		    ]

(********** RuleUnique **********)

SetAttributes[RuleUnique, HoldAll]
RuleUnique[lhs_, rhs_, cond_:True] := ruleUnique[lhs, Evaluate[Dum[rhs]], cond]
RuleUnique[___]                    := (Message[RuleUnique::usage]; {})

    SetAttributes[ruleUnique, HoldAll]
    ruleUnique[lhs_, rhs_, True]  := RuleDelayed[lhs, DumFresh[rhs]]
    ruleUnique[lhs_, rhs_, cond_] := RuleDelayed[lhs, DumFresh[rhs] /; cond]

(* set lhs to rhs if cond holds, where dummy indices in rhs are preperly treated. *)
SetAttributes[DefUnique, HoldAll]
DefUnique[lhs_, rhs_, cond_:True] := defUnique[lhs, Evaluate[Dum[rhs]], cond]
DefUnique[___]                    := Message[DefUnique::usage]

    SetAttributes[defUnique, HoldAll]
    defUnique[lhs_, rhs_, True]  := SetDelayed[lhs, DumFresh[rhs]]
    defUnique[lhs_, rhs_, cond_] := SetDelayed[lhs, DumFresh[rhs] /; cond]

(********** for SyntaxCheck **********)

(* Check expr satisfying HeadQs *)
SetAttributes[SyntaxCheck, Listable]
SyntaxCheck[aPlus_Plus, opts___Rule] :=
    Module[{hOpts = Sequence @@ FilterRules[{opts}, HeadQs], rcExpr, freeIndexL1, freeIndexL2, i},
        rcExpr = expandObject[aPlus, hOpts];

        If [!FreeQ[rcExpr[[1]] = syntaxCheckTerm[rcExpr[[1]], {hOpts}], ErrorT], Return[rcExpr]];

        (* get free-indices of 1st term *)
        freeIndexL1 = findFreeIndices[rcExpr[[1]], hOpts];

        For [i = 2, i <= Length[rcExpr], ++i,
            If [!FreeQ[rcExpr[[i]] = syntaxCheckTerm[rcExpr[[i]], {hOpts}], ErrorT], Return[rcExpr]];

            (* the same free-indices? *)
            freeIndexL2 = findFreeIndices[rcExpr[[i]], hOpts];
            If [freeIndexL1 =!= freeIndexL2, Message[Msg::err, "incompatible free indices:", freeIndexL1, "and", freeIndexL2]; Return[ErrorT @ rcExpr]]
        ];

        aPlus  (* no error *)
    ] /; FreePatternQ[aPlus]
SyntaxCheck[aTerm_, opts___Rule] :=
    Module[{hOpts = Sequence @@ FilterRules[{opts}, HeadQs], expr},
        expr = expandObject[aTerm, hOpts];

        If[Head[expr] === Plus, Return[SyntaxCheck[expr, hOpts]],
        (* else *)              Return[syntaxCheckTerm[expr, {hOpts}]]]
    ] /; FreePatternQ[aTerm]
SyntaxCheck[expr_, opts___Rule] := expr
SyntaxCheck[___] := Message[SyntaxCheck::usage]

    syntaxCheckTerm[aTerm_, hOptL_List] :=
        Module[{ordTerm, oTerm, modhOptL = hOptL},
            (* for considering all exprs having the pattern f_[___] when hOptL === {} *)
            If [hOptL === {}, modhOptL = {HeadQs -> {True&}}];

            {ordTerm, oTerm} = splitTerm[aTerm, modhOptL];
            If [oTerm === 1, Return[aTerm]];

            (* check objects *)
            oTerm = forEachObject[oTerm, modhOptL, syntaxCheckObject];
            If [!FreeQ[oTerm, ErrorT], Return[oTerm]];  (* there are errors *)
            If [duplicatedIndicesQ[indicesOf[oTerm, modhOptL], True], Return[ErrorT @ oTerm]];

            aTerm  (* no-errors *)
        ]

        (* hOptL == {} in this function *)
        syntaxCheckObject[oName:ErrorT[_][___]] := syntaxCheckObject[oName //. ErrorT -> Identity]

        syntaxCheckObject[(oName_?IndexedOperandQ)[]] :=
            If [GetRank[oName] =!= 0,  (* scalar *)
                Message[Msg::err, "invalid number of indices for", oName, "", ""]; ErrorT[oName][],
            (* else *)
                oName[]  (* no errors *)
            ]
        syntaxCheckObject[(oName_?IndexedOperandQ)[aIndices__]] :=
            If [!checkObject[oName, {aIndices}, True],
                ErrorT[oName][aIndices],
            (* else *)
                With [{kind = KindOf @ oName},
                	If [MetricSpaceQ[kind],
                    	With[ {nDim = GetDimension[kind]},
                        	If [oName === GetEpsilon[kind] && PositiveIntegerQ[nDim] && Length[{aIndices}] =!= nDim,
                            	Message[Msg::err, "invalid number of indices", nDim, "for", oName]; ErrorT[oName][aIndices],
                        	(* else *)
                            	oName[aIndices]
                        	]
                    	],
                    (* else *)
                         oName[aIndices]
                    ]
                ]
            ]
        syntaxCheckObject[(opName_?IndexedOperatorQ)[arg_, expr___]] :=
            Module [{rcExpr},
                Switch [getType[opName],
                    CD, If [!FreeQ[rcExpr = SyntaxCheck[{expr}], ErrorT], Return[opName[arg, Sequence @@ rcExpr]]];
                        If [!ValidIndexQ[arg, KindOf[opName, arg], True], Return[ErrorT[opName][arg, expr]]];
                        If [!DnIndexQ[arg] && !MetricSpaceQ[indexKindProper @ arg],
                        	Message[Msg::err, "The index of", opName, "is not down:", arg]; Return[ErrorT[opName][arg, expr]]
                        ];
                        If [duplicatedIndicesQ[Join[{arg}, findIndices[expr]], True], Return[ErrorT[opName][arg, expr]]];
                        opName[arg, expr],
                    LD, If [!FreeQ[rcExpr = SyntaxCheck[{expr}], ErrorT], Return[opName[arg, Sequence @@ rcExpr]]];
                        If [!checkFirstArgLD[opName, arg], Return[ErrorT[opName][arg, expr]]];
                        opName[arg, expr],
                    XD, If [!FreeQ[rcExpr = SyntaxCheck[arg], ErrorT], Return[opName[rcExpr, expr]]];
                        opName[arg, expr],
                    XP, If [!FreeQ[rcExpr = SyntaxCheck /@ {arg, expr}, False], Return[opName[Sequence @@ rcExpr]]];
                        If [duplicatedIndicesQ[Flatten @ (findIndices /@ {arg, expr}), True], Return[ErrorT[opName][arg, expr]]];
                        opName[arg, expr]
                ]
            ]

            (* check 1st argument of LD-type operator *)
            checkFirstArgLD[LD, aV_] :=  (* check LD *)
                If [!vectorNameQ[aV], Message[Msg::err, "non-vector:", aV, "", ""]; False,
                (* else *)            True]
            checkFirstArgLD[opName_, arg_] := (* check LD-type operator *)
                If [Head[arg] =!= Symbol, Message[Msg::err, "non-symbolic argument", arg, "for an operator", opName]; False,
                (* else *)                True]

        syntaxCheckObject[(sfName_?ScalarFunctionQ)[arg_, expr___]] :=
            Module [{rcExpr},
                If [sfName === Tscalar && {expr} =!= {},
                    Message[Msg::err, "too many arguments", Length[{expr}] + 1, ". One argument is required.", ""]; Return[ErrorT[sfName][arg, expr]]
                ];

                (* check each argument *)
                If [!FreeQ[rcExpr = SyntaxCheck[#, HeadQs -> {ObjectQ}]& /@ {arg, expr}, ErrorT], Return[sfName[Sequence @@ rcExpr]]];

                If [findFreeIndices[arg, HeadQs -> {ObjectQ}] =!= {},
                    Message[Msg::err, "non-scalar expression", arg, "", ""]; Return[ErrorT[sfName][arg, expr]],
                (* else *)
                    If [{expr} =!= {} && MemberQ[findFreeIndices[#, HeadQs -> {ObjectQ}]& /@ {expr}, {__}],
                        Message[Msg::err, "non-scalar expression:", expr, "", ""]; Return[ErrorT[sfName][arg, expr]]
                    ]
                ];
                sfName[arg, expr]
            ]
        syntaxCheckObject[sName_[args___]] :=
            Module [{rcExpr},
                If [!FreeQ[rcExpr = SyntaxCheck[#, HeadQs -> {ObjectQ}]& /@ {args}, ErrorT], Return[sName[Sequence @@ args]]];
                If [Flatten[findFreeIndices[#, HeadQs -> {ObjectQ}]& /@ {args}] =!= {},
                    Message[Msg::err, "non-scalar expression:", {args}, "in", sName]; Return[ErrorT[sName][args]]
                ];
                sName[args]
            ] /; !ObjectQ[sName] && MemberQ[freeObjectQ[{args}, HeadQs -> {ObjectQ}], False]

checkObject[oName_?IndexedOperandQ, aIndexL_List, withMsg_:False] :=
    Module[ {nRank = GetRank @ oName, len, i},
        (* check # of indices *)
        len = Length[aIndexL];
        If [nRank =!= -1 && nRank =!= len,
            If [!IndexedFormQ[oName] || (IndexedFormQ[oName] && getDegree[oName] + nRank =!= len),
                If [withMsg, Message[Msg::err, "invalid number of indices for", oName, ": ", aIndexL]];
                Return[False]
            ]
        ];

        Switch [oName,
        	Kdelta,
        		(* check the kind which is all the same *)
        		If [Length[DeleteDuplicates @ (indexKind /@ aIndexL)] =!= 1 && indexKind[First @ aIndexL] =!= errorIndex,
            		If [withMsg, Message[Msg::err, "Kdelta has wrong-kind:", aIndexL, "", ""]]; Return[False]
        		];

        		If [upupdndnIndexQ[aIndexL],   (* check dn/up states which are all-dn/all-up *)
        		    If [withMsg, Message[Msg::err, "Kdelta has wrong-dn/up:", aIndexL, "", ""]]; Return[False]
        		],
			_,
       		    Module[ {kind, dnup}, (* check validity and dn/up states for each index *)
         		    For [i = 1, i <= len, ++i,
        		        If [IndexedFormQ[oName] && len > nRank,
        		            kind = If [i > len - nRank, KindOf[oName, i - (len - nRank)], DefaultKind],
        		        (* else *)
        		            kind = KindOf[oName, i]
        		        ];

		           		If [!ValidIndexQ[aIndexL[[i]], kind, withMsg], Return[False]];

                        If [IndexedFormQ[oName] && len > nRank,
                            dnup = If [i > len - nRank, dnupAt[oName, i - (len - nRank)], -1],
                        (* else *)
                            dnup = dnupAt[oName, i]
                        ];

		           		If [!MetricSpaceQ[kind] && dnupState[aIndexL[[i]]] =!= dnup,
	           	    		If [withMsg, Message[Msg::err, oName, "has wrong-dn/up:", aIndexL, ""]]; Return[False]
           				]
        		    ]
                ]
        ];

        If [duplicatedIndicesQ[aIndexL, withMsg], Return[False]];
        True  (* no errors *)
    ]

(***** postEval *****)

SetAttributes[postEval, {HoldAll}]
postEval[lst_List] := postEval /@ lst
postEval[expr_] := (
        If [flagTable[SyntaxCheckFlag],
            With[ {rcExpr = SyntaxCheck[expr]},
                If [!FreeQ[rcExpr, ErrorT], Return[rcExpr]]  (* there are errors *)
            ]
        ];

        forEachTerm[expandObject[expr], canObject] /. $PROTECTEXPANDING -> Identity (* See CollectForm for $PROTECTEXPANDING *)
    ) /; FreePatternQ[expr] && !freeObjectQ[expr]
postEval[expr_] := expr /. $PROTECTEXPANDING -> Identity
postEval[expr_, __] := expr /. $PROTECTEXPANDING -> Identity  (* for Sequence input *)

    canObject[term_] :=
        Module[ {rcTerm = term},
            If [!flagTable[MarkErrorFlag],   rcTerm = rcTerm /. {ErrorT -> Identity}];
            If [flagTable[ResetDummiesFlag], rcTerm = ResetDummies[rcTerm, HeadQs -> {IndexedObjectQ}]];
            rcTerm /. $flattenOTHER[other_] :> other
        ]

(***** On / Off *****)

Unprotect[Off]  (* turn off a flag *)
Off[AutoFlag]         := (flagTable[AutoFlag] = False; $Post = .;)
Off[MarkErrorFlag]    := (flagTable[MarkErrorFlag] = False;)
Off[ResetDummiesFlag] := (flagTable[ResetDummiesFlag] = False;)
Off[SyntaxCheckFlag]  := (flagTable[SyntaxCheckFlag] = False;)
Protect[Off]

Unprotect[On]  (* turn on a flag *)
On[AutoFlag]         := (flagTable[AutoFlag] = True; $Post = postEval;)
On[MarkErrorFlag]    := (flagTable[MarkErrorFlag] = True;)
On[ResetDummiesFlag] := (flagTable[ResetDummiesFlag] = True;)
On[SyntaxCheckFlag]  := (flagTable[SyntaxCheckFlag] = True;)
Protect[On]

(********************************************************************)
initIndexNotation[] := (
        (***** Default Options: allQoptions에서 사용 *****)
        Options[HeadQs]  = {HeadQs  -> {IndexedObjectQ}};  (* default option for selecting heads, which means excluding ScalarFunctions. *)
        Options[IndexQs] = {IndexQs -> {True&}};           (* default option for selecting indices *)
        reservedNameList = {HeadQs, IndexQs};

        (* When reloading, Unprotect and TagUnset previously introduced index symbols *)
        If [ValueQ[loadedIndexNotation], setIndices[{}, #]& /@ definedKindList];

        (***** Indices *****)
        dummyPreListPrepared = {"/", "$", "%", "!", "@", "#", "&", "|", ":", ";", "?"};
        definedKindList = {};  (* initialize *)
        dummyPreList    = {};
		DefaultKind = Latin;  (* for ValidIndexQ. Use SetDefaultKind[Latin] for the metric and the covariant structure. *)
        DefineKind[{"0"},      Zero];  (* pre-defined Kinds *)
        DefineKind[Alphabet[], Latin];
        reservedNameList = Join[reservedNameList, {All, Zero, Latin, Epsilon, Structuref, Torsion}];

        (***** Defining Indexed Objects *****)
        reservedNameList = Join[reservedNameList, {C, D, E, I, N, O}];  (* Protected names in Mathematica *)
        reservedNameList = Join[reservedNameList, {CD, LD, XD, XP}];    (* Operator Types *)
        reservedNameList = Join[reservedNameList, {Tscalar, ErrorT}];   (* Predefined ScalarFunction and ErrorT *)

        (***** On/Off *****)
        Off[General::spell1];
        Off[General::spell];

        On[AutoFlag];
        On[MarkErrorFlag];
        On[ResetDummiesFlag];
        Off[SyntaxCheckFlag];

		(***** Finish initIndexNotation *****)
		reservedNameList = DeleteDuplicates[reservedNameList];
		loadedIndexNotation = True;
    )
initIndexNotation[]

(********************************************************************)
End[]

EndPackage[]
