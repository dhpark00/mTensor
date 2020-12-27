(* :Title: CTensor.m *)
(* :Context: mTensor` *)
(* :Author: Dal-Ho Park *)
(* :Summary: Component Calculations in mTensor *)
(* :Package Version: 2020.12 *)
(* :Mathematica Version: 10.4 *)

(********************************************************************)
BeginPackage["mTensor`"]

(********** Usage messages for the exported functions **********)

InitCTensor::usage = "InitCTensor[coSys, metric, <opts>]"
Tcalc::usage       = "Tcalc[tAtom, <simpCmd>]"

Geodesic::usage = "Geodesic[n, <simpCmd>]"

(***** Exported Variables *****)
(* CTensor *)
Csimplify::usage      = ""
CsimplifyMore::usage  = ""
CsimplifyRules::usage = ""
MetricPath::usage     = ""

(* Options for IniTCTensor *)
SimplifyMore::usage = ""

(********************************************************************)
Begin["`Private`"]

(***************** Definition of Local Variables ********************)

calcTimeVerbose = 0  (* for displaying calculation time when defaultCTensor[Verbose] === TRUE *)
nDimension = GetDimension[DefaultKind]

(************ Default of Exported Functions and Variables ***********)

Csimplify[expr_] := Together[ expr /. CsimplifyRules ] /. CsimplifyRules
CsimplifyMore[expr_, assump_:(True&)] := Simplify[ expr /. CsimplifyRules, assump ] /. CsimplifyRules

CsimplifyRules = {}
MetricPath     = "mTensor`Metrics`"

(************************** InitCTensor *****************************)

Options[InitCTensor] = {SimplifyMore -> False, Verbose -> False, GammaCD -> False, RicciCD -> False, RiemannCD -> False}
InitCTensor[fileName_String] := Get[MetricPath <> fileName <> "`"];
InitCTensor[coSys_ /; VectorQ[coSys, AtomQ], metric_?SquareMatrixQ, opts___Rule]                       := initCTensor[coSys, metric, False, opts] (* coordinate basis *)
InitCTensor[coSys_ /; VectorQ[coSys, AtomQ], metric_?SquareMatrixQ, basis_?SquareMatrixQ, opts___Rule] := initCTensor[coSys, metric, basis, opts] (* non-coordinate basis *)
InitCTensor[___] := Message[InitCTensor::usage]

	initCTensor[coSys_, metric_, basis_, opts___] :=
	    Module[ {calcGammaQ, calcRicciQ, calcRiemannQ},
	        If [!TorsionFreeQ[CD], Message[Msg::warn, "CTensor requires torsion-free!", "Use TorsionFreeQ[CD] ^= True;", "", ""]; Return[]];

        	If [basis === False && !(Length[coSys] === Length[metric[[1]]]),  (* coordinate basis *)
       			Message[Msg::err, "incompatible number of elements in coSys and metric", "", "", ""]; Return[]
       		];

        	If [basis =!= False && !(Length[coSys] === Length[metric[[1]]] === Length[basis[[1]]]),  (* non-coordinate basis *)
       			Message[Msg::err, "incompatible number of elements in coSys, metric, basis", "", "", ""]; Return[]
       		];

        	(* for options *)
        	If [SimplifyMore /. {opts} /. Options[InitCTensor], defaultCTensor[simpMethod] = CsimplifyMore,
        	(* else *)                                          defaultCTensor[simpMethod] = Csimplify];

        	defaultCTensor[Verbose] = Verbose /. {opts} /. Options[InitCTensor];

        	calcGammaQ   = GammaCD   /. {opts} /. Options[InitCTensor];
        	calcRicciQ   = RicciCD   /. {opts} /. Options[InitCTensor];
        	calcRiemannQ = RiemannCD /. {opts} /. Options[InitCTensor];

        	(* set Flags *)
        	flagTable[initCTensorFlag] = True;
        	flagTable[EvaluateBDFlag]  = True;

			If [basis === False, On[CoordinateBasisFlag], Off[CoordinateBasisFlag]];

        	(* metric, coordinates, and dimension *)
        	cMetric = metric;
            tCoordinates[DefaultKind]    = coSys;
            tCoordinatesStr[DefaultKind] = ToString /@ coSys;  (* String form of the coordinate system *)
            SetDimension[Length @ coSys];

        	tableToComponents[Metricg, 2, {-1,-1}, cMetric];
			If [basis === False,
        		basisMatrix[DefaultKind] = inverseBasisMatrix = IdentityMatrix[nDimension],
        	(* else *)
        		basisMatrix[DefaultKind] = basis;           (* basis matrix: \xi_a = h_a^{\mu} \pd_{\mu} *)
        		inverseBasisMatrix       = Inverse[basis] // CsimplifyMore
			];

        	(* initialize calc table *)
        	cTensorTable[Structuref] = False;
        	cTensorTable[cInvMetric] = False;
        	cTensorTable[bdMetric]   = False;
        	cTensorTable[GammaCD]    = False;
        	cTensorTable[RiemannCD]  = False;
        	cTensorTable[RicciCD]    = False;
        	cTensorTable[ScalarCD]   = False;
        	cTensorTable[WeylCD]     = False;

        	calcTimeVerbose = 0;  (* initialize *)
        	Tcalc[Structuref];
        	If [calcRicciQ || calcRiemannQ,
            	Tcalc[RiemannCD];
            	If [calcRicciQ, Tcalc[RicciCD]; Tcalc[ScalarCD]],
        	(* else *)
            	If [calcGammaQ, Tcalc[GammaCD]]
        	];

        	If [defaultCTensor[Verbose], Print["Total time: ", calcTimeVerbose, "Sec."]];
    	]

(***************************** Tcalc ********************************)

SetAttributes[Tcalc, HoldFirst]
Tcalc[GammaCD, simpCmd_:defaultCTensor[simpMethod]] :=
(* GammaCD[la,lb,lc] and GammaCD[la,lb,uc] *)
    Module[ {inTime, outTime},
        If [!cTensorTable[cInvMetric], calcInvMetric[simpCmd]];
        If [!cTensorTable[bdMetric],   calcBdMetric[simpCmd]];

        (* for GammaCD[la,lb,lc] *)
        inTime = TimeUsed[];
        If [CoordinateBasisQ[DefaultKind],  (* symmetric: la <-> lb *)
            Table[ GammaCD[-a,-b,-c] = ( bdMetric[[a,b,c]] + bdMetric[[b,a,c]] - bdMetric[[c,a,b]] ) / 2 // simpCmd,
                   {a, nDimension}, {b, a, nDimension}, {c, nDimension} ];
            Table[ GammaCD[-a,-b,-c] = GammaCD[-b,-a,-c], {a, 2, nDimension}, {b, 1, a - 1}, {c, nDimension} ],
        (* else *)  (* non-coordinate basis *)
            If [!cTensorTable[Structuref], Tcalc[Structuref, simpCmd]];

            tableToComponents[GammaCD, 3, {-1,-1,-1},
                              Table[ bdMetric[[a,b,c]] + bdMetric[[b,a,c]] - bdMetric[[c,a,b]]
                                     + Structuref[-a,-b,-c] + Structuref[-c,-a,-b] + Structuref[-c,-b,-a],
                                     {a, nDimension}, {b, nDimension}, {c, nDimension} ] / 2 // simpCmd]
        ];
        outTime = TimeUsed[];
        calcTimeVerbose += outTime - inTime;

        If [defaultCTensor[Verbose],
            Print["Calculated ", Subscript["\[CapitalGamma]", "abc"], " using ", simpCmd, " (", outTime - inTime, " Second)"];
        ];

        (* for GammaCD[la,lb,uc] *)
        inTime = TimeUsed[];
        If [CoordinateBasisQ[DefaultKind],  (* symmetric: la <-> lb *)
            Table[ GammaCD[-a,-b,c] = Sum[GammaCD[-a,-b,-m] Metricg[c,m], {m, nDimension} ] // simpCmd,
                   {a, nDimension}, {b, a, nDimension}, {c, nDimension} ];
            Table[ GammaCD[-a,-b,c] = GammaCD[-b,-a,c], {a, 2, nDimension}, {b, 1, a - 1}, {c, nDimension} ],
        (* else *)
            tableToComponents[GammaCD, 3, {-1,-1,1},
                              Table[ Sum[GammaCD[-a,-b,-m] Metricg[c,m], {m, nDimension} ],
                                     {a, nDimension}, {b, nDimension}, {c, nDimension} ] // simpCmd]
        ];
        cTensorTable[GammaCD] = True;
        outTime = TimeUsed[];
        calcTimeVerbose += outTime - inTime;

        If [defaultCTensor[Verbose],
            Print["Calculated ", Subsuperscript["\[CapitalGamma]", "ab", "  c"], " using ", simpCmd, " (", outTime - inTime, " Second)"];
        ];
    ] /; flagTable[initCTensorFlag]

Tcalc[RicciCD, simpCmd_:defaultCTensor[simpMethod]] :=
(* R[la,lb] *)
    Module[ {inTime, outTime},
        If [!cTensorTable[cInvMetric], calcInvMetric[simpCmd]];
        If [!cTensorTable[RiemannCD],  Tcalc[RiemannCD, simpCmd]];

        inTime = TimeUsed[];
        Table[ RicciCD[-a,-b] = Sum[ Metricg[c,d] RiemannCD[-a,-c,-b,-d], {c, nDimension}, {d, nDimension} ] // simpCmd,
               {a, nDimension}, {b, a, nDimension}];
        Table[ RicciCD[-a,-b] = RicciCD[-b,-a],  {a, 2, nDimension}, {b, 1, a - 1}];  (* symmetric: la <-> lb *)
        cTensorTable[RicciCD] = True;
        outTime = TimeUsed[];
        calcTimeVerbose += outTime - inTime;

        If [defaultCTensor[Verbose],
            Print["Calculated ", Subscript["R", "ab"], " using ", simpCmd, " (", outTime - inTime, " Second)"];
        ];
    ] /; flagTable[initCTensorFlag]

Tcalc[RiemannCD, simpCmd_:defaultCTensor[simpMethod]] :=
(* R[la,lb,lc,ld] *)
    Module[ {inTime, outTime},
        If [!cTensorTable[bdMetric], calcBdMetric[simpCmd]];
        If [!cTensorTable[GammaCD], Tcalc[GammaCD, simpCmd]];

        inTime = TimeUsed[];

        Table[ RiemannCD[-a,-a,-b,-c] = 0, {a, nDimension}, {b, nDimension}, {c, nDimension} ];  (* anti-symmetric *)
        Table[ RiemannCD[-b,-c,-a,-a] = 0, {a, nDimension}, {b, nDimension}, {c, nDimension} ];  (* anti-symmetric *)

        If [CoordinateBasisQ[DefaultKind],
            Table[
                RiemannCD[-a,-b,-c,-d] =
                    (riemannSign) * (bdD[a, bdMetric[[c,b,d]] - bdMetric[[d,b,c]]] / 2 - bdD[b, bdMetric[[c,a,d]] - bdMetric[[d,a,c]]] / 2
                                     + Sum[ GammaCD[-a,-c,-m] GammaCD[-b,-d,m] - GammaCD[-b,-c,-m] GammaCD[-a,-d,m], {m, nDimension} ]) // simpCmd,
                {a, nDimension}, {b, a + 1, nDimension}, {c, a, nDimension}, {d, c + 1, nDimension}
            ],
        (* else *)
            Table[
                RiemannCD[-a,-b,-c,-d] =
                    (riemannSign) * (Sum[ Metricg[-d,-m] (bdD[a, GammaCD[-b,-c,m]] - bdD[b, GammaCD[-a,-c,m]])
                                          + GammaCD[-a,-m,-d] GammaCD[-b,-c,m] - GammaCD[-b,-m,-d] GammaCD[-a,-c,m]
                                          - Structuref[-a,-b,m] GammaCD[-m,-c,-d], {m, nDimension} ]) // simpCmd,
                {a, nDimension}, {b, a + 1, nDimension}, {c, a, nDimension}, {d, c + 1, nDimension}
            ]
        ];

        (* symmetric: (la,lb)(lc,ld) <-> (lc,ld)(la,lb) *)
        Table[ RiemannCD[-a,-b,-c,-d] =  RiemannCD[-c,-d,-a,-b],
               {a, 2, nDimension}, {b, a + 1, nDimension}, {c, 1, a - 1}, {d, c + 1, nDimension} ];

        (* anti-symmetric: la <-> lb *)
        Table[ RiemannCD[-a,-b,-c,-d] = -RiemannCD[-b,-a,-c,-d],
               {a, 2, nDimension}, {b, 1, a - 1}, {c, nDimension}, {d, c + 1, nDimension} ];

        (* anti-symmetric: lc <-> ld *)
        Table[ RiemannCD[-a,-b,-c,-d] = -RiemannCD[-a,-b,-d,-c],
               {a, nDimension}, {b, a + 1, nDimension}, {c, 2, nDimension}, {d, 1, c - 1} ];

        (* symmetric: la <-> lb and lc <-> ld *)
        Table[ RiemannCD[-a,-b,-c,-d] =  RiemannCD[-b,-a,-d,-c],
               {a, 2, nDimension}, {b, 1, a - 1}, {c, 2, nDimension}, {d, 1, c - 1} ];

        cTensorTable[RiemannCD] = True;
        outTime = TimeUsed[];
        calcTimeVerbose += outTime - inTime;

        If [defaultCTensor[Verbose],
            Print["Calculated ", Subscript["R", "abcd"], " using ", simpCmd, " (", outTime - inTime, " Second)"];
        ];
    ] /; flagTable[initCTensorFlag]
Tcalc[RiemannCD[i_Integer, j_Integer, k_Integer, l_Integer], simpCmd_:defaultCTensor[simpMethod]] :=
(* calculate R[-a,-b,-c,-d] *)
    Module[ {a = -i, b = -j, c = -k, d = -l, rc},
        If [a > nDimension, Message[Msg::err, a, " in ", nDimension, "dimension."]; Return[]];
        If [b > nDimension, Message[Msg::err, b, " in ", nDimension, "dimension."]; Return[]];
        If [c > nDimension, Message[Msg::err, c, " in ", nDimension, "dimension."]; Return[]];
        If [d > nDimension, Message[Msg::err, d, " in ", nDimension, "dimension."]; Return[]];

        If [!cTensorTable[bdMetric], calcBdMetric[simpCmd]];
        If [!cTensorTable[GammaCD], Tcalc[GammaCD, simpCmd]];

        inTime = TimeUsed[];
        If [CoordinateBasisQ[DefaultKind],
            rc = bdD[a, bdMetric[[c,b,d]] - bdMetric[[d,b,c]]] / 2 - bdD[b, bdMetric[[c,a,d]] - bdMetric[[d,a,c]]] / 2
                 + Sum[ GammaCD[-a,-c,-m] GammaCD[-b,-d,m] - GammaCD[-b,-c,-m] GammaCD[-a,-d,m], {m, nDimension} ] // simpCmd,
        (* else *)
            rc = Sum[ Metricg[-d,-m] (bdD[a, GammaCD[-b,-c,m]] - bdD[b, GammaCD[-a,-c,m]])
                      + GammaCD[-a,-m,-d] GammaCD[-b,-c,m] - GammaCD[-b,-m,-d] GammaCD[-a,-c,m]
                      - Structuref[-a,-b,m] GammaCD[-m,-c,-d], {m, nDimension} ] // simpCmd
        ];
        rc = (riemannSign) * rc;

        RiemannCD[-a,-b,-c,-d] =  rc;
        RiemannCD[-b,-a,-c,-d] = -rc;
        RiemannCD[-a,-b,-d,-c] = -rc;
        RiemannCD[-b,-a,-d,-c] =  rc;
        RiemannCD[-c,-d,-a,-b] =  rc;
        RiemannCD[-d,-c,-a,-b] = -rc;
        RiemannCD[-c,-d,-b,-a] = -rc;
        RiemannCD[-d,-c,-b,-a] =  rc;

        outTime = TimeUsed[];
        calcTimeVerbose += outTime - inTime;

        If [defaultCTensor[Verbose],
            Print["Calculated ", printCTensor[RiemannCD, {-1,-1,-1,-1}, {a,b,c,d}], " using ", simpCmd, " (", outTime - inTime, " Second)"];
        ];
    ] /; flagTable[initCTensorFlag] && AllTrue[{i, j, k, l}, DnIndexQ] && i != j && k != l

Tcalc[ScalarCD, simpCmd_:defaultCTensor[simpMethod]] :=
(* R[] *)
    Module[ {inTime, outTime},
        If [!cTensorTable[cInvMetric], calcInvMetric[simpCmd]];
        If [!cTensorTable[RicciCD],    Tcalc[RicciCD, simpCmd]];

        inTime = TimeUsed[];
        ScalarCD[] = Sum[ Metricg[a,b] RicciCD[-a,-b], {a, nDimension}, {b, nDimension}] // simpCmd;
        cTensorTable[ScalarCD] = True;
        outTime = TimeUsed[];
        calcTimeVerbose += outTime - inTime;

        If [defaultCTensor[Verbose], Print["Calculated R using ", simpCmd, " (", outTime - inTime, " Second)"]];
    ] /; flagTable[initCTensorFlag]

Tcalc[Structuref, simpCmd_:defaultCTensor[simpMethod]] :=
(* structure constants f[la,lb,uc] and f[la,lb,lc] *)
    Module[ {stConst, inTime, bdh, outTime},
        inTime = TimeUsed[];

        If [CoordinateBasisQ[DefaultKind],
            stConst = Table[ 0, {a, nDimension}, {b, nDimension}, {c, nDimension} ];
            tableToComponents[Structuref, 3, {-1,-1,-1}, stConst];
            tableToComponents[Structuref, 3, {-1,-1,1}, stConst],
        (* else *)
            bdh = Table[ bdD[a, basisMatrix[DefaultKind][[b,c]]], {a, nDimension}, {b, nDimension}, {c, nDimension} ] // simpCmd;

            (* anti-symmetric *)
            Table[ Structuref[-a,-a,c] = Structuref[-a,-a,-c] = 0, {a, nDimension}, {c, nDimension} ];

            Table[ Structuref[-a,-b,c] = Sum[ inverseBasisMatrix[[mu,c]] (bdh[[a,b,mu]] - bdh[[b,a,mu]]), {mu, nDimension} ] // simpCmd,
                   {a, nDimension}, {b, a + 1, nDimension}, {c, nDimension} ];

            Table[ Structuref[-a,-b,-c] = Sum[Metricg[-c,-m] Structuref[-a,-b,m], {m, nDimension}] // simpCmd,
                   {a, nDimension}, {b, a + 1, nDimension}, {c, nDimension} ];

            Table[ Structuref[-a,-b,c] = -Structuref[-b,-a,c]; Structuref[-a,-b,-c] = -Structuref[-b,-a,-c],
                   {a, 2, nDimension}, {b, 1, a - 1}, {c, nDimension} ]
        ];
        cTensorTable[Structuref] = True;
        outTime = TimeUsed[];
        calcTimeVerbose += outTime - inTime;

        If [!CoordinateBasisQ[DefaultKind] && defaultCTensor[Verbose],
            Print["Calculated ", Subsuperscript["f", "ab", "  c"], " and ", Subscript["f", "abc"], " using ", simpCmd, " (", outTime - inTime, " Second)"]
        ];
    ] /; flagTable[initCTensorFlag]

Tcalc[WeylCD, simpCmd_:defaultCTensor[simpMethod]] :=
    Module[ {inTime, outTime},
        If [nDimension > 2,
            If [!cTensorTable[RiemannCD], Tcalc[RiemannCD, simpCmd]];
            If [!cTensorTable[RicciCD],   Tcalc[RicciCD, simpCmd]];
            If [!cTensorTable[ScalarCD],  Tcalc[ScalarCD, simpCmd]];

            inTime = TimeUsed[];
            Table[ WeylCD[-a,-a,-b,-c] = 0, {a, nDimension}, {b, nDimension}, {c, nDimension} ];  (* anti-symmetric *)
            Table[ WeylCD[-b,-c,-a,-a] = 0, {a, nDimension}, {b, nDimension}, {c, nDimension} ];  (* anti-symmetric *)

            Table[
                WeylCD[-a,-b,-c,-d] =
                    RiemannCD[-a,-b,-c,-d]
                    - (riemannSign) * (
                        - (Metricg[-a,-c] RicciCD[-b,-d] - Metricg[-a,-d] RicciCD[-b,-c]
                           + Metricg[-b,-d] RicciCD[-a,-c] - Metricg[-b,-c] RicciCD[-a,-d]) / (nDimension - 2)
                        + ScalarCD[] (Metricg[-a,-c] Metricg[-b,-d] - Metricg[-a,-d] Metricg[-b,-c]) / (nDimension-1) / (nDimension-2)
                      ) // simpCmd,
               {a, nDimension}, {b, a + 1, nDimension}, {c, a, nDimension}, {d, c + 1, nDimension} ];

            (* symmetric: (la,lb)(lc,ld) <-> (lc,ld)(la,lb) *)
            Table[ WeylCD[-a,-b,-c,-d] =  WeylCD[-c,-d,-a,-b],
                   {a, 2, nDimension}, {b, a + 1, nDimension}, {c, 1, a - 1}, {d, c + 1, nDimension} ];

            (* anti-symmetric: la <-> lb *)
            Table[ WeylCD[-a,-b,-c,-d] = -WeylCD[-b,-a,-c,-d],
                   {a, 2, nDimension}, {b, 1, a - 1}, {c, nDimension}, {d, c + 1, nDimension} ];

            (* anti-symmetric: lc <-> ld *)
            Table[ WeylCD[-a,-b,-c,-d] = -WeylCD[-a,-b,-d,-c],
                   {a, nDimension}, {b, a + 1, nDimension}, {c, 2, nDimension}, {d, 1, c - 1} ];

            (* symmetric: la <-> lb and lc <-> ld *)
            Table[ WeylCD[-a,-b,-c,-d] =  WeylCD[-b,-a,-d,-c], {a, 2, nDimension}, {b, 1, a - 1}, {c, 2, nDimension}, {d, 1, c - 1} ];

            cTensorTable[WeylCD] = True;
            outTime = TimeUsed[];
            calcTimeVerbose += outTime - inTime;

            If [defaultCTensor[Verbose], Print["Calculated ", Subscript["C", "abcd"], " using ", simpCmd, " (", outTime - inTime, " Second)"]]
        ];
    ] /; flagTable[initCTensorFlag]

(***** Local Functions *****)
calcBdMetric[simpCmd_:defaultCTensor[simpMethod]] :=
(* calculate bdD[la, Metricg[lb,lc]] *)
    Module[ {inTime, outTime},
        inTime = TimeUsed[];
        bdMetric = Table[0, {a, nDimension}, {b, nDimension}, {c, nDimension} ];
        Table[ bdMetric[[a,b,c]] = bdD[a, cMetric[[b,c]]] // simpCmd, {a, nDimension}, {b, nDimension}, {c, b, nDimension} ];
        Table[ bdMetric[[a,b,c]] = bdMetric[[a,c,b]], {a, nDimension}, {b, 2, nDimension}, {c, 1, b - 1} ];  (* symmetric: lb <-> lc *)
        cTensorTable[bdMetric] = True;
        outTime = TimeUsed[];
        calcTimeVerbose += outTime - inTime;

        If [defaultCTensor[Verbose],
            Print["Calculated ", Subscript["\[PartialD]", "a"], Subscript["g", "bc"], " using ", simpCmd, " (", outTime - inTime, " Second)"]
        ];
    ]

calcInvMetric[simpCmd_:defaultCTensor[simpMethod]] :=
(* inverse metric *)
    Module[ {inTime, outTime},
        inTime = TimeUsed[];
        tableToComponents[Metricg, 2, {1,1}, Inverse[cMetric] // simpCmd];
        cTensorTable[cInvMetric] = True;
        outTime = TimeUsed[];
        calcTimeVerbose += outTime - inTime;

        If [defaultCTensor[Verbose], Print["Calculated ", Superscript["g", "ab"], " using ", simpCmd, " (", outTime - inTime, " Second)"]];
    ]

(****************************** Show ********************************)

Unprotect[Show]
Show[GammaCD] :=
    Module[ {isAllZero = True, jStart, i, j, k},
        If [!cTensorTable[GammaCD], Message[Msg::warn, "not calculated", "", "", ""]; Return[]];

        If [CoordinateBasisQ[DefaultKind],
            Print[Row[{"Symmetry: ", Subsuperscript["\[CapitalGamma\]", "(ab)", "    c"]}]];
            jStart = i,
        (* else *)
            jStart = 1
        ];

        Do [
            Do [
                Do [
                    If [GammaCD[-i,-j,k] =!= 0,
                        isAllZero = False;
                        Print[Row[{printCTensor[GammaCD, {-1,-1,1}, {i,j,k}], " = ", GammaCD[-i,-j,k]}]]
                    ],
                    {k, nDimension}
                ],
                {j, jStart, nDimension}
            ],
            {i, nDimension}
        ];

        If [isAllZero === True,
            Print[Row[{Subsuperscript["\[CapitalGamma\]", "ab", "  c"], " = ", "0"}]]
        ]
   ] /; flagTable[initCTensorFlag]

Show[Metricg] :=
    Module[ {i, j},
        Print[Row[{"Symmetry: ", Subscript["g", "(ab)"]}]];

        Do [
            Do [
                If [Metricg[-i,-j] =!= 0,
                    Print[Row[{printCTensor[Metricg, {-1,-1}, {i,j}], " = ", Metricg[-i,-j]}]]
                ],
                {j, i, nDimension}
            ],
            {i, nDimension}
        ]
    ] /; flagTable[initCTensorFlag]

Show[RicciCD] :=
    Module[ {isAllZero = True, i, j},
        If [!cTensorTable[RicciCD], Message[Msg::warn, "not calculated", "", "", ""]; Return[]];

        Print[Row[{"Symmetry: ", Subscript["R", "(ab)"]}]];

        Do [
            Do [
                If [RicciCD[-i,-j] =!= 0,
                    isAllZero = False;
                    Print[Row[{printCTensor[RicciCD, {-1,-1}, {i,j}], " = ", RicciCD[-i,-j]}]]
                ],
                {j, i, nDimension}
            ],
            {i, nDimension}
        ];

        If [isAllZero === True, Print[SequenceForm[Subscript["R", "ab"], " = ", "0"]]]
    ] /; flagTable[initCTensorFlag]

Show[RiemannCD] :=
    Module[ {isAllZero = True, i, j, k, l},
        If [!cTensorTable[RiemannCD], Message[Msg::warn, "not calculated", "", "", ""]; Return[]];

        Print[Row[{"Symmetry: ", Subscript["R", "[ab][cd]"], " = ", Subscript["R", "[cd][ab]"]}]];

        Do [
            Do [
                Do [
                    Do [
                        If [RiemannCD[-i,-j,-k,-l] =!= 0,
                            isAllZero = False;
                            Print[Row[{printCTensor[RiemannCD, {-1,-1,-1,-1}, {i,j,k,l}], " = ", RiemannCD[-i,-j,-k,-l]}]]
                        ],
                        {l, k + 1, nDimension}
                    ],
                    {k, i, nDimension}
                ],
                {j, i + 1, nDimension}
            ],
            {i, nDimension}
        ];

        If [isAllZero === True, Print[Row[{Subscript["R", "abcd"], " = ", "0"}]]]
    ] /; flagTable[initCTensorFlag]

Show[ScalarCD] :=
    Module[ {},
        If [!cTensorTable[ScalarCD], Message[Msg::warn, "not calculated", "", "", ""]; Return[]];

        Print[Row[{printCTensor[ScalarCD, {}, {}], " = ", ScalarCD[]}]]
    ] /; flagTable[initCTensorFlag]

Show[Structuref] :=
    If [CoordinateBasisQ[DefaultKind],
        Print[Row[{Subsuperscript["f", "ab", "  c"], " = ", "0"}]],
    (* else *)
        Module[ {isAllZero = True, i, j, k},
            If [!cTensorTable[Structuref], Message[Msg::warn, "not calculated", "", "", ""]; Return[]];

            Print[Row[{"Symmetry: ", Subsuperscript["f", "[ab]", "    c"]}]];

            Do [
                Do [
                    Do [
                        If [Structuref[-i,-j,k] =!= 0,
                            isAllZero = False;
                            Print[Row[{printCTensor[Structuref, {-1,-1,1}, {i,j,k}], " = ", Structuref[-i,-j,k]}]]
                        ],
                        {k, nDimension}
                    ],
                    {j, i + 1, nDimension}
                ],
                {i, nDimension}
            ];

            If [isAllZero === True, Print[Row[{Subsuperscript["f", "ab", "  c"], " = ", "0"}]]]
        ]
    ] /; flagTable[initCTensorFlag]

Show[WeylCD] :=
    Module[ {isAllZero = True, i, j, k, l},
        If [nDimension <= 2, Message[Msg::warn, "WeylCD is not defined in ", nDimension, "dimension.",  ""]; Return[]];

        If [!cTensorTable[WeylCD], Message[Msg::warn, "not calculated", "", "", ""]; Return[]];

        Print[Row[{"Symmetry: ", Subscript["C", "[ab][cd]"]}]];

        Do [
            Do [
                Do [
                    Do [
                        If [WeylCD[-i,-j,-k,-l] =!= 0,
                            isAllZero = False;
                            Print[Row[{printCTensor[WeylCD, {-1,-1,-1,-1}, {i,j,k,l}], " = ", WeylCD[-i,-j,-k,-l]}]]
                        ],
                        {l, k + 1, nDimension}
                    ],
                    {k, nDimension}
                ],
                {j, i + 1, nDimension}
            ],
            {i, nDimension}
        ];

        If [isAllZero === True, Print[Row[{Subscript["C", "abcd"], " = ", "0"}]]]
    ] /; flagTable[initCTensorFlag]

Show[tName_[indices___]] :=
(* display one tensor *)
(* TODO: consider symmetries and contraction, in general, in Show[tName] *)
    Module[ {dnupL = dnupListFrom[indices], indexL = {}, value, i},
        For [i = 1, i <= Length[{indices}], i++,
            indexL = Join[indexL, {Table[j, {j, nDimension}]}]
        ];

        (* get all possible combinations of component indices *)
        indexL = Flatten[Outer[List, Sequence @@ Table[indexL[[i]], {i, Length[indexL]}]], 1];
        indexL = Flatten[indexL, TensorRank[indexL] - 2];

        Do [
            value = tName[Sequence @@ (dnupL * indexL[[i]])];
            If [value =!= 0, Print[Row[{printCTensor[tName, dnupL, indexL[[i]]], " = ", value}]]],

            {i, Length[indexL]}
        ]
    ] /; IndexedTensorQ[tName] && AllTrue[{indices}, TensorialIndexQ]

Protect[Show]

(***** Local Functions *****)

printCTensor[tName_, dnupL_, posL_] :=
    Module[ {upL = {}, dnL = {}, i},
        Do [
            If [dnupL[[i]] === -1,
                If [CoordinateBasisQ[DefaultKind], AppendTo[dnL, tCoordinatesStr[DefaultKind][[posL[[i]]]]],
                (* else *)                         AppendTo[dnL, posL[[i]]]];
                AppendTo[upL, " "],
            (* else *)
                AppendTo[dnL, " "];
                If [CoordinateBasisQ[DefaultKind], AppendTo[upL, tCoordinatesStr[DefaultKind][[posL[[i]]]]],
                (* else *)                         AppendTo[upL, posL[[i]]]]
            ],

            {i, Length[dnupL]}
        ];

        Subsuperscript[ToExpression @ getPrtStr[tName], Row[dnL], Row[upL]]
    ]

(************************ Misc. for CTensor **************************)

Geodesic[comp_Integer?Positive, simpCmd_:defaultCTensor[simpCmd]] :=
(* print geodesic equation *)
    Module[ {rc, i, j},
        If [comp > nDimension, Message[Msg::err, comp, "is incompatible with dimension", nDimension, ""]; Return[]];

        If [!CoordinateBasisQ[DefaultKind], Message[Msg::err, "coordinate basis only", "", "", ""]; Return[]];

        rc = Overscript[tCoordinatesStr[DefaultKind][[comp]], ".."];
        Do [
            Do [
                If [i === j, rc +=   GammaCD[-i,-j,comp] OverDot[tCoordinatesStr[DefaultKind][[i]]] OverDot[tCoordinatesStr[DefaultKind][[j]]],
                (* else *)   rc += 2 GammaCD[-i,-j,comp] OverDot[tCoordinatesStr[DefaultKind][[i]]] OverDot[tCoordinatesStr[DefaultKind][[j]]]],

                {j, i, nDimension}
            ],
            {i, nDimension}
        ];
        rc // simpCmd
    ] /; flagTable[initCTensorFlag]
Geodesic[___] := Message[Geodesic::usage]

(********************************************************************)

End[ ] (* end the private context *)

EndPackage[ ]  (* end the package context *)

(********************************************************************)
