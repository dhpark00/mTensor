(* :Title: CTensorNT.m *)
(* :Context: mTensor` *)
(* :Author: Dal-Ho Park *)
(* :Summary: Newman-Penrose Calculations in mTensor *)
(* :Package Version: 2019.08 *)
(* :Mathematica Version: 10.4 *)

(********************************************************************)
BeginPackage["mTensor`"]

(********** Usage messages for the exported functions **********)

BasisNP::usage       = "BasisNP[metric]"
InitCTensorNP::usage = "InitCTensorNP[coSys, nullVectors, opts]"
RotateNP::usage      = "RotateNP[nullVectors, classN, param1, param2]"

(***** Exported Variables *****)

PetrovType::usage       = ""
LambdaNP::usage         = ""
PhiNP::usage            = ""
PsiNP::usage            = ""
SpinCoefficients::usage = ""

(********************************************************************)
Begin["`Private`"]

(************************* InitCTensorNP ****************************)

Options[InitCTensorNP] = {SimplifyMore -> False}
InitCTensorNP[coSys_ /; VectorQ[coSys, AtomQ], nullVectors_?SquareMatrixQ, opts___Rule] := (
        If [!TorsionFreeQ[CD], Message[Msg::warn, "CTensor requires torsion-free!", "Use TorsionFreeQ[CD] ^= True;", "", ""]; Return[]];

        If [Length[coSys] =!= 4, Message[Msg::err, "Not four-dimension", "", "", ""]; Return[]];

        If [Dimensions[nullVectors] =!= {4,4}, Message[Msg::err, nullVectors, "is not 4 by 4 matrix!", "", ""]; Return[]];

        (* for options *)
        If [SimplifyMore /. {opts} /. Options[InitCTensorNP], defaultCTensor[simpMethod] = CsimplifyMore,
        (* else *)                                            defaultCTensor[simpMethod] = Csimplify];

        flagTable[initCTensorFlag] = True;
        flagTable[EvaluateBDFlag]  = True;
        Off[CoordinateBasisFlag];

        tCoordinates[DefaultKind]    = coSys;
        tCoordinatesStr[DefaultKind] = ToString /@ coSys;  (* String form of the coordinate system *)
        SetDimension[4];

        tableToComponents[Metricg, 2, {-1,-1}, {{0,-1,0,0}, {-1,0,0,0}, {0,0,0,1}, {0,0,1,0}}];
        tableToComponents[Metricg, 2, { 1, 1}, {{0,-1,0,0}, {-1,0,0,0}, {0,0,0,1}, {0,0,1,0}}];
        basisMatrix[DefaultKind] = nullVectors;            (* basis matrix: \xi_a = h_a^{\mu} \pd_{\mu} *)
        inverseBasisMatrix       = Inverse[nullVectors] // defaultCTensor[simpMethod];

        Tcalc[Structuref];
        calcGammaNP[];
        assignSpinCoefficients[];
        calcRiemannNP[];
        calcRicciNP[];
        assignPhiNP[];
        assignPsiNP[];
        assignWeylNP[];
    )
InitCTensorNP[___] := Message[InitCTensorNP::usage]

(* generate Newman-Penrose frame from a metric *)
BasisNP[metric_?SquareMatrixQ, simpCmd_:Csimplify] :=
    Module[ {invg, l, n, m, mBar, a, b, s},
        If [Dimensions[metric] =!= {4,4}, Message[Msg::err, metric, "is not 4 by 4 matrix!", "", ""]; Return[]];

        invg = Inverse[metric] // simpCmd;

        Switch[ {invg[[1,1]] === 0, invg[[2,2]] === 0},
            {True,  True},
                If [invg[[1,2]] === 0, Message[Msg::warn, "Incompatible metric", "", "", ""]; Return[]];
                l = invg[[1]] / Sqrt[-invg[[1,2]]];
                n = invg[[2]] / Sqrt[-invg[[1,2]]],
            {False, True},
                If [invg[[1,2]] === 0, Message[Msg::warn, "Incompatible metric", "", "", ""]; Return[]];
                l = (invg[[1]] - invg[[1,1]] invg[[2]] / 2 / invg[[1,2]]) / Sqrt[-invg[[1,2]]];
                n = invg[[2]] / Sqrt[-invg[[1,2]]],
            {True,  False},
                If [invg[[1,2]] === 0, Message[Msg::warn, "Incompatible metric", "", "", ""]; Return[]];
                l = invg[[1]] / Sqrt[-invg[[1,2]]];
                n = (invg[[2]] - invg[[2,2]] invg[[1]] / 2 / invg[[1,2]]) / Sqrt[-invg[[1,2]]],
            {False, False},
                a = (-invg[[1,2]] + Sqrt[invg[[1,2]]^2 - invg[[1,1]] invg[[2,2]]]) / invg[[2,2]];
                b = (-invg[[1,2]] - Sqrt[invg[[1,2]]^2 - invg[[1,1]] invg[[2,2]]]) / invg[[2,2]];
                s = 2 (-invg[[1,1]] + invg[[1,2]]^2 / invg[[2,2]]);
                l = (invg[[1]] + a invg[[2]]);
                n = (invg[[1]] + b invg[[2]]) / s;
                {l, n} = {l / l[[2]], n l[[2]]}
        ];

        Switch[ {invg[[3,3]] === 0, invg[[4,4]] === 0},
            {True,  True},
                If [invg[[3,4]] === 0, Message[Msg::warn, "Incompatible metric", "", "", ""]; Return[]];
                m    = invg[[3]] / Sqrt[invg[[3,4]]];
                mBar = invg[[4]] / Sqrt[invg[[3,4]]],
            {True,  False},
                If [invg[[3,4]] === 0, Message[Msg::warn, "Incompatible metric", "", "", ""]; Return[]];
                m    = invg[[3]] / Sqrt[invg[[3,4]]];
                mBar = (invg[[4]] - invg[[4,4]] invg[[3]] / 2 / invg[[3,4]]) / Sqrt[invg[[3,4]]],
            {False, True},
                If [invg[[3,4]] === 0, Message[Msg::warn, "Incompatible metric", "", "", ""]; Return[]];
                m    = (invg[[3]] - invg[[3,3]] invg[[4]] / 2 / invg[[3,4]]) / Sqrt[invg[[3,4]]];
                mBar = invg[[4]] / Sqrt[invg[[3,4]]],
            {False, False},
                a = (-invg[[3,4]] + Sqrt[invg[[3,4]]^2 - invg[[3,3]] invg[[4,4]]]) / invg[[4,4]];
                b = (-invg[[3,4]] - Sqrt[invg[[3,4]]^2 - invg[[3,3]] invg[[4,4]]]) / invg[[4,4]];
                s = Sqrt[2(invg[[3,3]] - invg[[3,4]]^2 / invg[[4,4]])];
                m    = (invg[[3]] + a invg[[4]]) / s;
                mBar = (invg[[3]] + b invg[[4]]) / s
        ];

        {l, n, m, mBar} // simpCmd
    ]
BasisNP[___] := Message[BasisNP::usage]

RotateNP[nullVectors_?SquareMatrixQ, classN_?IntegerQ, param1_, param2_, simpCmd_:Csimplify] :=
    Module[ {l, n, m, mBar, param},
        If [Dimensions[nullVectors] =!= {4,4}, Message[Msg::err, nullVectors, "is not 4 by 4 matrix!", "", ""]; Return[]];

        {l, n, m, mBar} = nullVectors;

        Switch[ classN,
            1, param = param1 + I param2;
                n    = n + cc[param] m + param mBar + param cc[param] l;
                m    = m + param l;
                mBar = cc[m],
            2, param = param1 + I param2;
                l    = l + cc[param] m + param mBar + param cc[param] n;
                m    = m + param n;
                mBar = cc[m],
            3, l     = l / param1;
                n    = n param1;
                m    = m Exp[I param2];
                mBar = cc[m]
        ];
        {l, n, m, mBar} // simpCmd
    ] /; MemberQ[{1,2,3}, classN]
RotateNP[___] := Message[RotateNP::usage]

Unprotect[Show]
Show[PetrovType] := (* TODO: correct the algorithm for PetrovType. See Chandrasekhar, pp 59 *)
    Switch[ {PsiNP[0] === 0, PsiNP[1] === 0, PsiNP[2] === 0, PsiNP[3] === 0, PsiNP[4] === 0},
        {True, False, False, False, False}, Print["Petrov type: I"],
        {True, True,  False, False, False}, Print["Petrov type: II"],
        {True, True,  True,  False, False}, Print["Petrov type: III"],
        {True, True,  True,  True,  False}, Print["Petrov type: N"],
        {True, True,  False, True,  True},  Print["Petrov type: D"],
        _,                                  Message[Msg::warn, "Need to another algorithm", "", "", ""]
    ]
Show[PhiNP] :=
    Module[ {vL, sL, pos, zeroes, i},
        vL = {PhiNP[0,0], PhiNP[0,1], PhiNP[0,2], PhiNP[1,1], PhiNP[1,2], PhiNP[2,2], LambdaNP};
        sL = {Subscript["\[CapitalPhi]", "00"], Subscript["\[CapitalPhi]", "01"],
              Subscript["\[CapitalPhi]", "02"], Subscript["\[CapitalPhi]", "11"],
              Subscript["\[CapitalPhi]", "12"], Subscript["\[CapitalPhi]", "22"], "\[CapitalLambda]"};

        pos = Position[vL, 0];  (* positions of zeroes *)
        zeroes = Map[Row[{#, " = "}]&, sL[[Flatten @ pos]]];
        If [zeroes =!= {}, Print[Row @ zeroes, "0"]];

        (* remove zeroes *)
        vL = Delete[vL, pos];
        sL = Delete[sL, pos];

        (* print non-zero values *)
        For [i = 1, i <= Length[vL], i++,
            Print[sL[[i]], " = ", vL[[i]]];
        ];
    ]
Show[PsiNP] :=
    Module[ {vL, sL, pos, zeroes, i},
        vL = {PsiNP[0], PsiNP[1], PsiNP[2], PsiNP[3], PsiNP[4]};
        sL = {Subscript["\[CapitalPsi]", "0"], Subscript["\[CapitalPsi]", "1"],
              Subscript["\[CapitalPsi]", "2"], Subscript["\[CapitalPsi]", "3"],
              Subscript["\[CapitalPsi]", "4"]};

        pos = Position[vL, 0];  (* positions of zeroes *)
        zeroes = Map[Row[{#, " = "}]&, sL[[Flatten @ pos]]];
        If [zeroes =!= {}, Print[Row @ zeroes, "0"]];

        (* remove zeroes *)
        vL = Delete[vL, pos];
        sL = Delete[sL, pos];

        (* print non-zero values *)
        Do [Print[sL[[i]], " = ", vL[[i]]], {i, Length[vL]}];
    ]
Show[SpinCoefficients] :=
    Module[ {vL, sL, pos, zeroes, i},
        vL = {alphaNP,    betaNP,    gammaNP,    epsilonNP,    kappaNP,    lambdaNP,    muNP,    nuNP,    piNP,    rhoNP,    sigmaNP,    tauNP};
        sL = {"\[Alpha]", "\[Beta]", "\[Gamma]", "\[Epsilon]", "\[Kappa]", "\[Lambda]", "\[Mu]", "\[Nu]", "\[Pi]", "\[Rho]", "\[Sigma]", "\[Tau]"};

        pos = Position[vL, 0];  (* positions of zeroes *)
        zeroes = Map[(# <> " = ")&, sL[[Flatten @ pos]]];
        If [zeroes =!= {}, Print[StringJoin @@ zeroes, "0"]];

        (* remove zeroes *)
        vL = Delete[vL, pos];
        sL = Delete[sL, pos];

        (* print non-zero values *)
        Do [Print[sL[[i]], " = ", vL[[i]]], {i, Length[vL]}];
    ]
Protect[Show]

(***** Local Rules *****)

rSymRule = {
        r_[i_,j_,k_,l_] :>  0 /; (i === j || k === l),
        r_[i_,j_,k_,l_] :> -r[j,i,k,l] /; i > j,
        r_[i_,j_,k_,l_] :> -r[i,j,l,k] /; k > l,
        r_[i_,j_,k_,l_] :>  r[k,l,i,j] /; i > k,
        r_[i_,j_,k_,l_] :>  r[k,l,i,j] /; (i === k && j > l)
    }

(***** Local Functions *****)

assignPhiNP[simpCmd_:defaultCTensor[simpMethod]] := (
        PhiNP[0,0] =  RicciCD[-1,-1] / 2;
        PhiNP[0,1] =  RicciCD[-1,-3] / 2;
        PhiNP[0,2] =  RicciCD[-3,-3] / 2;
        PhiNP[1,1] = (RicciCD[-1,-2] + RicciCD[-3,-4]) / 4 // simpCmd;
        PhiNP[1,2] =  RicciCD[-2,-3] / 2;
        PhiNP[2,2] =  RicciCD[-2,-2] / 2;
        LambdaNP   = -ScalarCD[] / 24;
    )

assignPsiNP[simpCmd_:defaultCTensor[simpMethod]] := (
        PsiNP[0] = RiemannCD[-1,-3,-1,-3];
        PsiNP[1] = RiemannCD[-1,-2,-1,-3] - RicciCD[-1,-3] / 2 // simpCmd;
        PsiNP[2] = -(RiemannCD[-1,-3,-2,-4] + ScalarCD[] / 12) // simpCmd;
        PsiNP[3] = -(RiemannCD[-1,-2,-2,-4] + RicciCD[-2,-4] / 2) // simpCmd;
        PsiNP[4] = RiemannCD[-2,-4,-2,-4];
    )

assignSpinCoefficients[simpCmd_:defaultCTensor[simpMethod]] := (
        epsilonNP = (GammaCD[-1,-1,-2] - GammaCD[-1,-3,-4]) / 2 // simpCmd;
        kappaNP   =  GammaCD[-1,-1,-3];
        piNP      = -GammaCD[-1,-2,-4];
        gammaNP   = (GammaCD[-2,-1,-2] - GammaCD[-2,-3,-4]) / 2 // simpCmd;
        tauNP     =  GammaCD[-2,-1,-3];
        nuNP      = -GammaCD[-2,-2,-4];
        betaNP    = (GammaCD[-3,-1,-2] - GammaCD[-3,-3,-4]) / 2 // simpCmd;
        sigmaNP   =  GammaCD[-3,-1,-3];
        lambdaNP  = -GammaCD[-4,-2,-4];
        rhoNP     =  GammaCD[-4,-1,-3];
        muNP      = -GammaCD[-3,-2,-4];
        alphaNP   = (GammaCD[-4,-1,-2] - GammaCD[-4,-3,-4]) / 2 // simpCmd;
    )

assignWeylNP[simpCmd_:defaultCTensor[simpMethod]] :=
    Module[ {weyl, weylTable},
        weyl[1,2,1,2] = PsiNP[2] + cc[PsiNP[2]] // simpCmd;
        weyl[1,2,1,3] = PsiNP[1];
        weyl[1,2,1,4] = cc[PsiNP[1]];
        weyl[1,2,2,3] = -cc[PsiNP[3]];
        weyl[1,2,2,4] = -PsiNP[3];
        weyl[1,2,3,4] = -PsiNP[2] + cc[PsiNP[2]] // simpCmd;
        weyl[1,3,1,3] = PsiNP[0];
        weyl[1,3,1,4] = 0;
        weyl[1,3,2,3] = 0;
        weyl[1,3,2,4] = -PsiNP[2];
        weyl[1,3,3,4] = -PsiNP[1];
        weyl[1,4,1,4] = cc[PsiNP[0]];
        weyl[1,4,2,3] = -cc[PsiNP[2]];
        weyl[1,4,2,4] = 0;
        weyl[1,4,3,4] = -cc[PsiNP[1]];
        weyl[2,3,2,3] = cc[PsiNP[4]];
        weyl[2,3,2,4] = 0;
        weyl[2,3,3,4] = -cc[PsiNP[3]];
        weyl[2,4,2,4] = PsiNP[4];
        weyl[2,4,3,4] = PsiNP[3];
        weyl[3,4,3,4] = PsiNP[2] + cc[PsiNP[2]] // simpCmd;

        weylTable = Table[weyl[i,j,k,l] //. rSymRule, {i,4}, {j,4}, {k,4}, {l,4}];
        tableToComponents[WeylCD, 4, {-1,-1,-1,-1}, weylTable];
    ]

calcGammaNP[simpCmd_:defaultCTensor[simpMethod]] :=
(* Riemannian connection in general basis *)
    Module[ {lowG, affineG},
        lowG = Table[ Structuref[-a,-b,-c] + Structuref[-c,-a,-b] + Structuref[-c,-b,-a],
                      {a, nDimension}, {b, nDimension}, {c, nDimension} ] / 2 // simpCmd;
        tableToComponents[GammaCD, 3, {-1,-1,-1}, lowG];

        affineG = Table[ Sum[ Metricg[c,d] lowG[[a,b,d]], {d, nDimension} ], {a, nDimension}, {b, nDimension}, {c, nDimension} ] // simpCmd;
        tableToComponents[GammaCD, 3, {-1,-1,1}, affineG];
    ]

calcRicciNP[simpCmd_:defaultCTensor[simpMethod]] :=
    Module[ {ricci, ricciTable},
        ricci[1,1] = 2 RiemannCD[-1,-3,-1,-4];
        ricci[1,2] = RiemannCD[-1,-2,-1,-2] + RiemannCD[-1,-3,-2,-4] + cc[RiemannCD[-1,-3,-2,-4]] // simpCmd;
        ricci[1,3] = RiemannCD[-1,-2,-1,-3] + RiemannCD[-1,-3,-3,-4] // simpCmd;
        ricci[1,4] = cc[ricci[1,3]];
        ricci[2,2] = 2 RiemannCD[-2,-3,-2,-4];
        ricci[2,3] = -RiemannCD[-1,-2,-2,-3] + RiemannCD[-2,-3,-3,-4] // simpCmd;
        ricci[2,4] = cc[ricci[2,3]];
        ricci[3,3] = -2 RiemannCD[-1,-3,-2,-3];
        ricci[3,4] = -RiemannCD[-1,-3,-2,-4] - cc[RiemannCD[-1,-3,-2,-4]] - RiemannCD[-3,-4,-3,-4] // simpCmd;
        ricci[4,4] = -2 cc[RiemannCD[-1,-3,-2,-3]];

        ricciTable = Table[If [i > j, ricci[j,i], ricci[i,j]], {i,4}, {j,4}];
        tableToComponents[RicciCD, 2, {-1,-1}, ricciTable];

        tableToComponents[ScalarCD, 0, {}, -2(ricci[1,2] - ricci[3,4]) // simpCmd];
    ]

calcRiemannNP[simpCmd_:defaultCTensor[simpMethod]] :=
    Module[ {curvR, curvTable, tmp},
        tmp = bdD[1, gammaNP] - bdD[2, epsilonNP] + piNP tauNP - nuNP kappaNP
              - (epsilonNP + cc[epsilonNP]) (gammaNP + cc[gammaNP]) + (alphaNP + cc[betaNP]) (tauNP + cc[piNP]);
        curvR[1,2,1,2] = tmp + cc[tmp] // simpCmd;
        curvR[1,2,1,3] = bdD[1, tauNP] - bdD[2, kappaNP] + (epsilonNP - cc[epsilonNP]) tauNP
                         - kappaNP (3 gammaNP + cc[gammaNP]) + (piNP + cc[tauNP]) sigmaNP + (cc[piNP] + tauNP) rhoNP // simpCmd;
        curvR[1,2,1,4] = cc[curvR[1,2,1,3]];
        curvR[1,2,2,4] = -bdD[1, nuNP] + bdD[2, piNP] + (cc[epsilonNP] + 3 epsilonNP) nuNP
                         - (gammaNP - cc[gammaNP]) piNP - (cc[piNP] + tauNP) lambdaNP - (piNP + cc[tauNP]) muNP // simpCmd;
        curvR[1,2,2,3] = cc[curvR[1,2,2,4]];
        curvR[1,3,1,3] = bdD[1, sigmaNP] - bdD[3, kappaNP] - kappaNP (cc[alphaNP] + 3 betaNP - cc[piNP] + tauNP)
                         + sigmaNP (3 epsilonNP - cc[epsilonNP] + rhoNP + cc[rhoNP]) // simpCmd;
        curvR[1,3,1,4] = bdD[1, cc[rhoNP]] - bdD[3, cc[kappaNP]] - cc[kappaNP] (3 cc[alphaNP] + betaNP - cc[piNP])
                         - kappaNP cc[tauNP] + cc[rhoNP] (epsilonNP + cc[epsilonNP] + cc[rhoNP]) + sigmaNP cc[sigmaNP] // simpCmd;
        curvR[1,3,2,3] = -bdD[1, cc[lambdaNP]] + bdD[3, cc[piNP]] - cc[lambdaNP] (epsilonNP - 3 cc[epsilonNP] + cc[rhoNP])
                         - cc[piNP] (cc[alphaNP] - betaNP + cc[piNP]) + kappaNP cc[nuNP] - sigmaNP cc[muNP] // simpCmd;
        curvR[1,3,2,4] = -bdD[1, muNP] + bdD[3, piNP] + muNP (epsilonNP + cc[epsilonNP] - cc[rhoNP])
                         + piNP (cc[alphaNP] - betaNP - cc[piNP]) + kappaNP nuNP - sigmaNP lambdaNP // simpCmd;
        curvR[1,2,3,4] = curvR[1,3,2,4] - cc[curvR[1,3,2,4]] // simpCmd;
        curvR[1,3,3,4] = bdD[1, cc[alphaNP] - betaNP] + bdD[3, epsilonNP - cc[epsilonNP]]
                         + kappaNP (muNP + gammaNP - cc[gammaNP]) - cc[kappaNP] cc[lambdaNP]
                         - piNP sigmaNP + cc[piNP] (cc[rhoNP] - epsilonNP + cc[epsilonNP])
                         - sigmaNP (alphaNP - cc[betaNP]) - betaNP cc[rhoNP]
                         + cc[alphaNP] (2 epsilonNP - 2 cc[epsilonNP] + cc[rhoNP]) // simpCmd;
        curvR[1,4,1,4] = cc[curvR[1,3,1,3]];
        curvR[1,4,2,3] = cc[curvR[1,3,2,4]];
        curvR[1,4,2,4] = cc[curvR[1,3,2,3]];
        curvR[1,4,3,4] = -cc[curvR[1,3,3,4]];
        curvR[2,3,2,3] = -bdD[2, cc[lambdaNP]] + bdD[3, cc[nuNP]] - cc[nuNP] (3 cc[alphaNP] + betaNP + cc[piNP] - tauNP)
                         + cc[lambdaNP] (muNP + cc[muNP] - gammaNP + 3 cc[gammaNP]) // simpCmd;
        curvR[2,3,2,4] = -bdD[2, muNP] + bdD[3, nuNP] - nuNP (cc[alphaNP] + 3 betaNP - tauNP)
                         - cc[nuNP] piNP + muNP (muNP + gammaNP + cc[gammaNP]) + lambdaNP cc[lambdaNP] // simpCmd;
        curvR[2,3,3,4] = bdD[2, cc[alphaNP] - betaNP] + bdD[3, gammaNP - cc[gammaNP]]
                         - cc[tauNP] cc[lambdaNP] - nuNP sigmaNP + cc[rhoNP] cc[nuNP] + muNP tauNP
                         - cc[nuNP] (epsilonNP - cc[epsilonNP]) + tauNP (gammaNP - cc[gammaNP])
                         + cc[lambdaNP] (alphaNP - cc[betaNP]) - cc[alphaNP] muNP - betaNP (2 gammaNP - 2 cc[gammaNP] - muNP) // simpCmd;
        curvR[2,4,2,4] = cc[curvR[2,3,2,3]];
        curvR[2,4,3,4] = -cc[curvR[2,3,3,4]];
        tmp = -bdD[3, alphaNP - cc[betaNP]] - muNP rhoNP + lambdaNP sigmaNP - (muNP - cc[muNP]) (epsilonNP - cc[epsilonNP]) / 2
              - (rhoNP - cc[rhoNP]) (gammaNP - cc[gammaNP]) / 2 - (alphaNP - cc[betaNP]) (cc[alphaNP] - betaNP);
        curvR[3,4,3,4] = tmp + cc[tmp] // simpCmd;

        curvTable = Table[(riemannSign) * curvR[i,j,k,l] //. rSymRule, {i,4}, {j,4}, {k,4}, {l,4}];
        tableToComponents[RiemannCD, 4, {-1,-1,-1,-1}, curvTable];
    ]

(* complex conjugate *)
cc[expr__] := expr /. {Complex[re_, im_] :> Complex[re, -im]}

(********************************************************************)

End[ ] (* end the private context *)

EndPackage[ ]  (* end the package context *)

(********************************************************************)
